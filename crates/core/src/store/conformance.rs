//! Transaction boundaries and closure required by the checked application contracts.
use super::*;
use anyhow::ensure;
use std::collections::{BTreeMap, HashSet};
use tokio_postgres::Transaction;

impl AgeStore {
    // GraphPaths.Returned: arbitrary mixtures of propagation relations, with
    // no depth bound and one result per identity. A nonempty cycle may reach
    // the seed; the inference engine separately clamps it.
    pub(super) async fn downstream_on(
        &self,
        client: &Client,
        seed: Uuid,
        causal_only: bool,
    ) -> Result<Vec<Belief>> {
        let g = &self.graph_name;
        let mut reached = BTreeMap::new();
        let mut expanded = HashSet::new();
        let mut frontier = vec![seed];
        while !frontier.is_empty() {
            frontier.retain(|id| expanded.insert(*id));
            if frontier.is_empty() {
                break;
            }
            let ids = frontier
                .iter()
                .map(|id| format!("'{id}'"))
                .collect::<Vec<_>>()
                .join(",");
            let labels = if causal_only {
                &["CAUSES"][..]
            } else {
                &["SUPPORTS", "CAUSES", "DEFEATS"][..]
            };
            let arms = labels.iter().map(|label| format!(
                "MATCH (s:Belief)-[:{label}]->(n:Belief) WHERE s.id IN [{ids}] RETURN n.id,n.content,n.probability,n.confidence,n.alpha,n.beta,n.alpha0,n.beta0,n.created_at,n.last_activated_at,n.memory_type,n.project"
            )).collect::<Vec<_>>().join(" UNION ");
            let sql = format!("SELECT id::text,content::text,probability::text,confidence::text,alpha::text,beta::text,alpha0::text,beta0::text,created_at::text,last_activated_at::text,memory_type::text,project::text FROM ag_catalog.cypher('{g}', $$ {arms} $$) {BELIEF_RETURN_COLUMNS}");
            frontier.clear();
            for row in client.query(&sql, &[]).await? {
                let belief = belief_from_row(&row)?;
                if !expanded.contains(&belief.id) {
                    frontier.push(belief.id);
                }
                reached.insert(belief.id, belief);
            }
        }
        Ok(reached.into_values().collect())
    }

    pub(super) async fn propagate_in(
        &self,
        tx: &Transaction<'_>,
        seed_id: Uuid,
    ) -> Result<Vec<(Uuid, Probability)>> {
        let seed = self
            .get_belief_on(tx.client(), seed_id)
            .await?
            .ok_or_else(|| anyhow::anyhow!("belief {seed_id} not found"))?;
        let mut downstream = self.downstream_on(tx.client(), seed_id, false).await?;
        let (learning_mass, _) = learning::overlay(&Self::active_reviews(tx).await?);
        let grounding = self.get_grounding_mass_all_on(tx.client()).await?;
        for belief in &mut downstream {
            belief.alpha0 += grounding.get(&belief.id).copied().unwrap_or(0.0);
            if let Some((a, b)) = learning_mass.get(&belief.id) {
                belief.alpha0 += a;
                belief.beta0 += b;
            }
        }
        let mut ids: Vec<_> = downstream.iter().map(|b| b.id).collect();
        ids.push(seed_id);
        let incoming = self.get_incoming_edges_on(tx.client(), &ids).await?;
        let edges = crate::strip_source_means(&incoming);
        let external = crate::external_means_from(&incoming, &ids);
        let updates = crate::inference::InferenceEngine::new().propagate_defeat(
            &seed,
            &downstream,
            &edges,
            &external,
        )?;
        let writes: Vec<_> = updates.iter().map(|&(id, (a, b))| (id, a, b)).collect();
        self.update_beliefs_beta_on(tx.client(), &writes).await?;
        updates
            .into_iter()
            .map(|(id, (a, b))| Ok((id, Probability::new(crate::graph::beta_mean(a, b))?)))
            .collect()
    }

    pub(crate) async fn propagate_locked(&self, seed_id: Uuid) -> Result<Vec<(Uuid, Probability)>> {
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let result = self.propagate_in(&tx, seed_id).await?;
        tx.commit().await?;
        Ok(result)
    }

    pub(crate) async fn decay_locked(&self, factor: f64, project: Option<&str>) -> Result<usize> {
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let beliefs = match project {
            Some(project) => {
                self.list_beliefs_by_project_on(tx.client(), project)
                    .await?
            }
            None => self.list_beliefs_on(tx.client()).await?,
        };
        let grounding = self.get_grounding_mass_all_on(tx.client()).await?;
        let updates = crate::inference::InferenceEngine::new().decay_all(
            &beliefs,
            chrono::Utc::now(),
            factor,
            &grounding,
        )?;
        let writes: Vec<_> = updates.into_iter().map(|(id, (a, b))| (id, a, b)).collect();
        self.update_beliefs_beta_on(tx.client(), &writes).await?;
        tx.commit().await?;
        Ok(writes.len())
    }

    pub(super) async fn ensure_candidate_identity_free(
        &self,
        tx: &Transaction<'_>,
        id: Uuid,
    ) -> Result<()> {
        let g = &self.graph_name;
        let nodes = tx.query(&format!("SELECT id::text FROM ag_catalog.cypher('{g}', $$ MATCH (n) WHERE n.id = '{id}' RETURN n.id $$) AS (id ag_catalog.agtype)"), &[]).await?;
        let reservation = tx
            .query_opt(
                "SELECT node_id FROM mimir_review_candidates WHERE node_id=$1",
                &[&id],
            )
            .await?;
        ensure!(
            nodes.is_empty() && reservation.is_none(),
            "generated candidate identity is already occupied"
        );
        Ok(())
    }

    pub async fn replace_document(
        &self,
        path: &str,
        chunks: &[DocumentChunk],
        vectors: &[Vec<f32>],
    ) -> Result<()> {
        validate_document_batch(path, chunks, vectors)?;
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let old = self
            .get_chunk_ids_for_document_on(tx.client(), path)
            .await?;
        let proposed: HashSet<_> = chunks.iter().map(|c| c.id).collect();
        let g = &self.graph_name;
        // Validate against retained chunk identities before deleting anything.
        for row in tx.query(&format!("SELECT id::text FROM ag_catalog.cypher('{g}', $$ MATCH (c:DocumentChunk) RETURN c.id $$) AS (id ag_catalog.agtype)"), &[]).await? {
            let id = Uuid::parse_str(row.get(0))?;
            ensure!(!proposed.contains(&id) || old.contains(&id), "generated chunk identity is already occupied");
        }
        self.delete_document_chunks_in(&tx, &old).await?;
        self.delete_chunk_embeddings_on(tx.client(), &old).await?;
        for (chunk, vector) in chunks.iter().zip(vectors) {
            self.insert_document_chunk_on(tx.client(), chunk).await?;
            self.insert_chunk_embedding_on(tx.client(), chunk.id, vector)
                .await?;
        }
        tx.commit().await?;
        Ok(())
    }

    pub async fn clear_document(&self, path: &str) -> Result<usize> {
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let old = self
            .get_chunk_ids_for_document_on(tx.client(), path)
            .await?;
        self.delete_document_chunks_in(&tx, &old).await?;
        self.delete_chunk_embeddings_on(tx.client(), &old).await?;
        tx.commit().await?;
        Ok(old.len())
    }
}

fn validate_document_batch(
    path: &str,
    chunks: &[DocumentChunk],
    vectors: &[Vec<f32>],
) -> Result<()> {
    ensure!(
        chunks.len() == vectors.len(),
        "document embedding count does not match chunks"
    );
    let mut ids = HashSet::new();
    for chunk in chunks {
        ensure!(
            chunk.document_path == path,
            "replacement contains a different document"
        );
        ensure!(ids.insert(chunk.id), "duplicate generated chunk identity");
    }
    if let Some(first) = vectors.first() {
        ensure!(
            vectors.iter().all(|v| v.len() == first.len()),
            "inconsistent document embedding dimensions"
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(dead_code)] // Test-only adapter for the shared integration guard.
    mod isolation {
        use crate as mimir_core;
        include!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/support/isolation.rs"
        ));
    }

    #[test]
    fn document_admission_checks_count_shape_path_and_duplicate_id() {
        let chunk = DocumentChunk::new("document".into(), vec![], "text".into(), None, None);
        assert!(validate_document_batch(
            "document",
            std::slice::from_ref(&chunk),
            &[vec![1.0, 0.0]]
        )
        .is_ok());
        assert!(validate_document_batch("document", std::slice::from_ref(&chunk), &[]).is_err());
        assert!(
            validate_document_batch("other", std::slice::from_ref(&chunk), &[vec![1.0]]).is_err()
        );
        assert!(validate_document_batch(
            "document",
            &[chunk.clone(), chunk.clone()],
            &[vec![1.0], vec![1.0]]
        )
        .is_err());
        let mut second = chunk.clone();
        second.id = Uuid::new_v4();
        assert!(validate_document_batch(
            "document",
            &[chunk, second],
            &[vec![1.0], vec![1.0, 2.0]]
        )
        .is_err());
    }

    #[tokio::test]
    async fn belief_preparation_and_publication_failures_leave_no_partial_belief() {
        struct Provider {
            fail: bool,
        }
        impl crate::embed::EmbeddingProvider for Provider {
            fn embed<'a>(&'a self, texts: &'a [String]) -> crate::embed::EmbedFuture<'a> {
                Box::pin(async move {
                    if self.fail {
                        anyhow::bail!("fixture embedding failed");
                    }
                    Ok(vec![vec![1.0, 0.0]; texts.len()])
                })
            }
        }
        let cfg = isolation::fixture().database_config();
        let mut service = crate::MimirService::connect(&crate::config::Config {
            database: cfg,
            embeddings: None,
            llm: None,
            judge: None,
            email: None,
        })
        .await
        .unwrap();
        let project = format!("prepared-belief-{}", Uuid::new_v4());
        let path = format!("/fixture/{project}.md");
        let source = DocumentChunk::new(
            path.clone(),
            vec![],
            "Backups are kept for 30 days.".into(),
            None,
            Some(project.clone()),
        );
        service
            .store
            .replace_document(&path, std::slice::from_ref(&source), &[vec![1.0, 0.0]])
            .await
            .unwrap();
        let draft = || {
            Belief::new_in_project(
                "Backups are kept for 30 days.".into(),
                0.6,
                0.3,
                project.clone(),
            )
            .unwrap()
        };

        service.embeddings = Some(Box::new(Provider { fail: true }));
        assert!(service
            .publish_supported_belief(draft(), None, source.id)
            .await
            .is_err());
        assert!(!service
            .store
            .list_beliefs()
            .await
            .unwrap()
            .iter()
            .any(|belief| belief.project.as_deref() == Some(project.as_str())));

        service.embeddings = Some(Box::new(Provider { fail: false }));
        {
            let client = service.store.client.lock().await;
            client.batch_execute("CREATE FUNCTION mimir_test_reject_belief_vector() RETURNS trigger LANGUAGE plpgsql AS $$ BEGIN RAISE EXCEPTION 'fixture vector publication rejected'; END $$; CREATE TRIGGER mimir_test_reject_belief_vector BEFORE INSERT ON belief_embeddings FOR EACH STATEMENT EXECUTE FUNCTION mimir_test_reject_belief_vector()").await.unwrap();
        }
        let failed = service
            .publish_supported_belief(draft(), None, source.id)
            .await;
        {
            let client = service.store.client.lock().await;
            client.batch_execute("DROP TRIGGER mimir_test_reject_belief_vector ON belief_embeddings; DROP FUNCTION mimir_test_reject_belief_vector()").await.unwrap();
        }
        assert!(failed.is_err());
        assert!(!service
            .store
            .list_beliefs()
            .await
            .unwrap()
            .iter()
            .any(|belief| belief.project.as_deref() == Some(project.as_str())));

        let published = service
            .publish_supported_belief(draft(), None, source.id)
            .await
            .unwrap();
        let stored = service
            .store
            .get_belief(published.id)
            .await
            .unwrap()
            .unwrap();
        assert_eq!(stored.probability.value(), 0.6);
        assert_eq!(stored.confidence.value(), 0.3);
        assert_eq!(
            service
                .store
                .get_evidence_for_beliefs(&[published.id])
                .await
                .unwrap(),
            vec![(published.id, source.id, 0.0)]
        );
        let client = service.store.client.lock().await;
        let vectors: i64 = client
            .query_one(
                "SELECT count(*) FROM belief_embeddings WHERE belief_id=$1",
                &[&published.id],
            )
            .await
            .unwrap()
            .get(0);
        assert_eq!(vectors, 1);
        drop(client);
        // Review-created beliefs obey the same prepare-then-publish rule.
        let experience: crate::learning::Experience = serde_json::from_value(serde_json::json!({
            "id":Uuid::new_v4(), "project":project, "context":"backup retention",
            "action":"check retention documentation", "outcome":"success", "source":"tool_result",
            "evidence":["document read"], "pattern_id":null
        }))
        .unwrap();
        service.record_experience(&experience, 0).await.unwrap();
        let mut review: crate::learning::Review = serde_json::from_value(serde_json::json!({
            "experience_id":experience.id, "experience_revision":1, "reviewer":"fixture",
            "rationale":"document confirms retention", "candidates":[{
                "kind":"belief", "key":"retention", "content":"Backups are kept for 30 days.",
                "supporting_passage_id":source.id
            }]
        }))
        .unwrap();
        service.embeddings = Some(Box::new(Provider { fail: true }));
        assert!(service
            .review_supported_experience(&review, 0)
            .await
            .is_err());
        assert!(service
            .store
            .existing_belief_candidates(experience.id)
            .await
            .unwrap()
            .is_empty());
        assert_eq!(
            service
                .get_experience(experience.id)
                .await
                .unwrap()
                .unwrap()
                .review_revision,
            0
        );
        service.embeddings = Some(Box::new(Provider { fail: false }));
        if let crate::learning::Candidate::Belief {
            supporting_passage_id,
            ..
        } = &mut review.candidates[0]
        {
            *supporting_passage_id = None;
        }
        assert!(service
            .review_supported_experience(&review, 0)
            .await
            .is_err());
        if let crate::learning::Candidate::Belief {
            supporting_passage_id,
            ..
        } = &mut review.candidates[0]
        {
            *supporting_passage_id = Some(source.id);
        }
        let applied = service
            .review_supported_experience(&review, 0)
            .await
            .unwrap();
        let candidate_id = applied.candidate_ids["retention"];
        assert_eq!(
            service
                .store
                .get_evidence_for_beliefs(&[candidate_id])
                .await
                .unwrap(),
            vec![(candidate_id, source.id, 0.0)]
        );
        // A completed retry uses the existing belief without invoking a provider.
        service.embeddings = Some(Box::new(Provider { fail: true }));
        let retried = service
            .review_supported_experience(&review, 0)
            .await
            .unwrap();
        assert_eq!(retried.candidate_ids, applied.candidate_ids);
        service.delete_project(&project).await.unwrap();
    }

    #[tokio::test]
    async fn project_deletion_rolls_back_before_a_fresh_retry() {
        let cfg = isolation::fixture().database_config();
        crate::db::migrate(&cfg).await.unwrap();
        let store =
            AgeStore::new(crate::db::connect(&cfg).await.unwrap(), cfg.dbname.clone()).unwrap();
        let project = format!("deletion-rollback-{}", Uuid::new_v4());
        let belief = Belief::new_in_project(
            "deletion rollback fixture".into(),
            0.5,
            0.0,
            project.clone(),
        )
        .unwrap();
        store.insert_belief(&belief).await.unwrap();
        // A statement trigger rejects a later deletion inside the transaction.
        // Every earlier graph mutation must roll back with it.
        {
            let client = store.client.lock().await;
            client.batch_execute("CREATE FUNCTION mimir_test_reject_delete() RETURNS trigger LANGUAGE plpgsql AS $$ BEGIN RAISE EXCEPTION 'fixture deletion rejected'; END $$; CREATE TRIGGER mimir_test_reject_delete BEFORE DELETE ON belief_embeddings FOR EACH STATEMENT EXECUTE FUNCTION mimir_test_reject_delete()").await.unwrap();
        }
        let failed = store.delete_project(&project).await;
        {
            let client = store.client.lock().await;
            client.batch_execute("DROP TRIGGER mimir_test_reject_delete ON belief_embeddings; DROP FUNCTION mimir_test_reject_delete()").await.unwrap();
        }
        assert!(failed.is_err());
        assert!(store.get_belief(belief.id).await.unwrap().is_some());
        store.delete_project(&project).await.unwrap();
        assert!(store.get_belief(belief.id).await.unwrap().is_none());
    }

    #[tokio::test]
    async fn candidate_allocation_rejects_live_and_retired_occupied_ids() {
        let cfg = isolation::fixture().database_config();
        let dbname = cfg.dbname.clone();
        crate::db::migrate(&cfg).await.unwrap();
        let store = AgeStore::new(crate::db::connect(&cfg).await.unwrap(), dbname).unwrap();
        let project = format!("identity-fixture-{}", Uuid::new_v4());
        let live = Belief::new_in_project(
            "identity collision fixture".into(),
            0.5,
            0.0,
            project.clone(),
        )
        .unwrap();
        store.insert_belief(&live).await.unwrap();
        let mut client = store.client.lock().await;
        client
            .batch_execute("SET default_transaction_isolation TO 'repeatable read'")
            .await
            .unwrap();
        let tx = learning_transaction(&mut client).await.unwrap();
        let isolation: String = tx
            .query_one("SHOW transaction_isolation", &[])
            .await
            .unwrap()
            .get(0);
        assert_eq!(isolation, "read committed");
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await
            .unwrap();
        assert!(store
            .ensure_candidate_identity_free(&tx, Uuid::new_v4())
            .await
            .is_ok());
        assert!(store
            .ensure_candidate_identity_free(&tx, live.id)
            .await
            .is_err());
        let experience = Uuid::new_v4();
        let retired = Uuid::new_v4();
        tx.execute(
            "INSERT INTO mimir_experiences(id,project,revision) VALUES($1,'fixture',1)",
            &[&experience],
        )
        .await
        .unwrap();
        tx.execute("INSERT INTO mimir_review_candidates(experience_id,candidate_key,kind,node_id,declaration,retired) VALUES($1,'retired','belief',$2,'{}'::jsonb,true)", &[&experience,&retired]).await.unwrap();
        assert!(store
            .ensure_candidate_identity_free(&tx, retired)
            .await
            .is_err());
        tx.rollback().await.unwrap();
        drop(client);
        store.delete_project(&project).await.unwrap();
    }
}
