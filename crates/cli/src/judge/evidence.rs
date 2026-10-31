//! A bounded index map, shared by every judge adapter and review retry feedback.
//! This exposes provenance; it neither selects evidence nor supplies assessments.
use mimir_core::learning::{Experience, ObservationSource};
use serde_json::{json, Value};

pub(super) fn index_map(experience: &Experience) -> Value {
    let structured = !experience.source_records.is_empty();
    let entries: Vec<_> = experience.evidence.iter().enumerate().map(|(index, text)| {
        let provenance = if structured {
            experience.source_records.get(index).map(|s| &s.provenance)
        } else { Some(&experience.source) };
        json!({"index":index,"nonempty":!text.trim().is_empty(),"provenance":provenance,
            "non_agent_provenance":provenance.is_some_and(|p| *p != ObservationSource::AgentReport)})
    }).collect();
    json!({"format":if structured {"source_records"} else {"legacy_evidence"},"entries":entries})
}

pub(super) fn guidance(experience: &Experience) -> String {
    format!("Pinned evidence index map: {}. These indices address experience.evidence, not item IDs. Provenance is caller-reported, not independently verified. Select only citations relevant to the scoped claim and benefit rubric; an eligible index does not itself justify a score or weight.", index_map(experience))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn experience(source: &str) -> Experience {
        serde_json::from_value(json!({"id":"11111111-1111-4111-8111-111111111111","project":"judge-evidence-fixture","context":"User rejected an action, not its technical execution","action":"Created unsolicited backups","outcome":"unknown","source":source,"evidence":["Copied files successfully","Remove all backups. Nobody asked you to make them."],"belief_ids":[],"pattern_id":null})).unwrap()
    }
    #[test]
    fn legacy_user_feedback_is_addressable_without_structured_sources() {
        let e = experience("user_feedback");
        let map = index_map(&e);
        assert_eq!(map["format"], "legacy_evidence");
        assert_eq!(
            map["entries"][1],
            json!({"index":1,"nonempty":true,"provenance":"user_feedback","non_agent_provenance":true})
        );
        let agent = index_map(&experience("agent_report"));
        assert_eq!(agent["entries"][1]["non_agent_provenance"], false);
        let mut empty = e.clone();
        empty.evidence.clear();
        assert_eq!(index_map(&empty)["entries"], json!([]));
    }
    #[test]
    fn structured_provenance_does_not_leak_between_neighbors() {
        let mut e = experience("tool_result");
        e.source_records=serde_json::from_value(json!([
            {"source_ref":"agent","actor":"agent","provenance":"agent_report","text":"Copied successfully"},
            {"source_ref":"human","actor":"human","provenance":"user_feedback","text":"Not authorized"}
        ])).unwrap();
        e.evidence = vec!["agent".into(), "human".into()];
        let map = index_map(&e);
        assert_eq!(map["format"], "source_records");
        assert_eq!(map["entries"][0]["non_agent_provenance"], false);
        assert_eq!(map["entries"][1]["provenance"], "user_feedback");
    }

    struct RepairCitation {
        calls: usize,
    }
    impl crate::judge::runner::Backend for RepairCitation {
        fn next<'a>(
            &'a mut self,
            selected: &'a mimir_core::learning::ExperienceState,
            last: Option<&'a Value>,
            _tools: &'a [Value],
        ) -> std::pin::Pin<
            Box<
                dyn std::future::Future<Output = anyhow::Result<crate::judge::runner::Action>>
                    + Send
                    + 'a,
            >,
        > {
            Box::pin(async move {
                if self.calls == 1 {
                    let error = last.expect("rejection must reach reviewer");
                    assert_eq!(error["error"], "invalid_tool_arguments");
                    let message = error["message"].as_str().unwrap();
                    assert!(message.contains("weighted assessment requires evidence"));
                    assert!(message.contains("legacy_evidence"));
                    assert!(message.contains("user_feedback"));
                    assert!(message.contains("\"index\":1"));
                }
                self.calls += 1;
                Ok(crate::judge::runner::Action::Tool {
                    name: "review_experience".into(),
                    arguments: json!({
                        "expected_review_revision":selected.review_revision,
                        "review":{"experience_id":selected.experience.id,"experience_revision":selected.revision,
                        "reviewer":"fixture","rationale":"Citation repair preserves supported numeric assessment",
                        "candidates":[{"kind":"belief","key":"authorized-backups","content":"Creating these unsolicited backups was authorized and beneficial"}],
                        "assessments":[{"target":{"candidate_key":"authorized-backups"},"scope":"this decision","rubric":"scope-compliance-and-user-benefit/v1",
                            "correctness":{"value":0,"weight":1},"usefulness":{"value":-1,"weight":1},
                            "evidence_indices":if self.calls==1 {vec![]} else {vec![1]},
                            "rationale":"User explicitly rejected the decision; technical execution is separate"}]}
                    }),
                })
            })
        }
    }
    #[tokio::test]
    async fn judge_repairs_missing_legacy_citation_without_erasing_negative_assessment() {
        use std::{fs, os::unix::fs::PermissionsExt};
        let dir =
            std::env::temp_dir().join(format!("mimir-judge-evidence-{}", uuid::Uuid::new_v4()));
        fs::create_dir(&dir).unwrap();
        fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).unwrap();
        let fixture =
            std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/judge/retry_fixture.sh");
        let id = uuid::Uuid::new_v4();
        let config = dir.join("config.toml");
        let log = dir.join("review.log");
        fs::write(&config,format!("[database]\nhost='localhost'\nport=5432\ndbname='unused'\nuser='unused'\n[judge]\nproject='judge-retry-fixture'\nbatch_size=1\nmcp_command='bash'\nmcp_args=['{}','{}','{}','user-feedback']\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='/bin/true'\ntimeout_seconds=10\nmax_calls=3\n",fixture.display(),id,log.display())).unwrap();
        fs::set_permissions(&config, fs::Permissions::from_mode(0o600)).unwrap();
        let settings = crate::judge::config::load(Some(&config)).unwrap();
        let state = crate::judge::state::State::lock(dir.join("state"))
            .unwrap()
            .unwrap();
        let mut backend = RepairCitation { calls: 0 };
        let report = crate::judge::runner::run(&settings, &state, &mut backend).await;
        assert_eq!(report.status, "complete");
        assert_eq!(report.confirmed, 1);
        assert_eq!(backend.calls, 2);
        let payload = fs::read_to_string(dir.join("review.log.payload")).unwrap();
        assert_eq!(
            payload.lines().count(),
            1,
            "invalid request must not reach MCP"
        );
        let review: Value = serde_json::from_str(payload.trim()).unwrap();
        assert_eq!(review["assessments"][0]["evidence_indices"], json!([1]));
        assert_eq!(
            review["assessments"][0]["correctness"]["value"].as_f64(),
            Some(0.)
        );
        assert_eq!(
            review["assessments"][0]["usefulness"]["value"].as_f64(),
            Some(-1.)
        );
        drop(state);
        fs::remove_dir_all(dir).unwrap();
    }
}
