//! Revision conflicts offer exact readback, without rewriting newer work.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use mimir_core::{
    config::Config,
    db,
    interaction::NeedsInput,
    validation::{Code, Segment},
    MimirService,
};
use serde_json::{json, Value};
use std::process::Stdio;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

struct Client {
    child: tokio::process::Child,
    input: tokio::process::ChildStdin,
    output: BufReader<tokio::process::ChildStdout>,
    next_id: u64,
}
impl Client {
    fn start(id: uuid::Uuid) -> Result<Self> {
        let fixture = isolation::fixture();
        let stderr = std::fs::File::create(
            fixture
                .root
                .join(format!("learning-references-{id}.stderr")),
        )?;
        let mut child = tokio::process::Command::new(&fixture.mcp)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(stderr)
            .kill_on_drop(true)
            .spawn()?;
        let input = child.stdin.take().unwrap();
        let output = BufReader::new(child.stdout.take().unwrap());
        Ok(Self {
            child,
            input,
            output,
            next_id: 0,
        })
    }
    async fn call(&mut self, name: &str, arguments: Value) -> Result<Value> {
        let request = json!({"jsonrpc":"2.0","id":self.next_id,"method":"tools/call","params":{"name":name,"arguments":arguments}});
        self.next_id += 1;
        self.input
            .write_all(format!("{request}\n").as_bytes())
            .await?;
        self.input.flush().await?;
        let mut line = String::new();
        ensure!(
            self.output.read_line(&mut line).await? != 0,
            "MCP stopped after {name}"
        );
        let response: Value = serde_json::from_str(&line)?;
        ensure!(
            response.get("error").is_none(),
            "{name} did not offer a normal result: {response}"
        );
        Ok(serde_json::from_str(
            response["result"]["content"][0]["text"].as_str().unwrap(),
        )?)
    }
}

async fn test_service() -> Result<MimirService> {
    MimirService::connect(&Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await
}

async fn fixture_identity() -> Result<uuid::Uuid> {
    Ok(db::connect(&isolation::fixture().database_config())
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0))
}

#[tokio::test]
async fn conflicting_review_entries_offer_repairs_without_changing_saved_work() -> Result<()> {
    use mimir_core::graph::MemoryType;
    let service = test_service().await?;
    let id = fixture_identity().await?;
    let project = format!("review-conflicts-{id}");
    let first = isolation::seed_belief_in_project(
        "first review target",
        0.5,
        0.1,
        &project,
        MemoryType::Fact,
    )
    .await?;
    let second = isolation::seed_belief_in_project(
        "second review target",
        0.5,
        0.1,
        &project,
        MemoryType::Fact,
    )
    .await?;
    let mut client = Client::start(id)?;
    let checked = async {
        let source=json!({"id":id,"project":project,"context":"inspect conflicting review entries","action":"retain each observed contribution once","outcome":"unknown","source":"tool_result","evidence":["isolated fixture observation"],"belief_ids":[first.id,second.id]});
        client.call("record_experience",json!({"experience":source,"expected_revision":0})).await?;
        let original=client.call("get_experience",json!({"id":id})).await?;
        let history=client.call("experience_history",json!({"id":id})).await?;
        let saved_review=client.call("get_learning_review",json!({"id":id})).await?;
        let base=json!({"experience_id":id,"experience_revision":1,"reviewer":"fixture","rationale":"unresolved fixture observation"});
        let assessment=json!({"target":{"belief_id":first.id},"scope":"fixture","rubric":"fixture","correctness":{"value":null,"weight":0},"usefulness":{"value":null,"weight":0},"evidence_indices":[],"rationale":"unresolved"});
        let feedback=json!({"belief_id":first.id,"verdict":"support","weight":0});
        let link=json!({"from_id":first.id,"to_id":second.id,"relation":"Contradicts","weight":0});
        let candidate_feedback=json!({"target":{"belief_id":first.id},"verdict":"support","weight":0});
        let candidate_link=json!({"from":{"belief_id":first.id},"to":{"belief_id":second.id},"relation":"Supports","weight":0});
        let mut cases=Vec::new();
        let mut duplicate=base.clone();duplicate["assessments"]=json!([assessment,assessment]);
        cases.push((duplicate,json!(["review","assessments",1]),Code::Duplicate));
        for (field,entry) in [("feedback",feedback.clone()),("links",link.clone()),("candidate_feedback",candidate_feedback),("candidate_links",candidate_link)] {
            let mut review=base.clone(); review["assessments"]=json!([assessment]);review[field]=json!([entry]);
            cases.push((review,json!(["review","assessments",0]),Code::UnsupportedCombination));
        }
        let mut self_link=base.clone();self_link["links"]=json!([{"from_id":first.id,"to_id":first.id,"relation":"Supports","weight":0}]);
        cases.push((self_link,json!(["review","links",0]),Code::UnsupportedCombination));
        for repeated in [link.clone(),json!({"from_id":second.id,"to_id":first.id,"relation":"Contradicts","weight":0})] {
            let mut review=base.clone();review["links"]=json!([link,repeated]);
            cases.push((review,json!(["review","links",1]),Code::Duplicate));
        }
        let mut duplicate_feedback=base.clone();duplicate_feedback["feedback"]=json!([feedback,feedback]);
        cases.push((duplicate_feedback,json!(["review","feedback",1]),Code::Duplicate));
        for (review,path,code) in cases {
            let result=client.call("review_experience",json!({"review":review,"expected_review_revision":0})).await?;
            let correction:NeedsInput=serde_json::from_value(result)?;
            let item=&correction.issues()[0];
            ensure!(item.fault().code==code && serde_json::to_value(&item.fault().path)?==path);
            ensure!(!item.fault().message.is_empty() && !item.expected().is_empty());
            ensure!(item.suggested_correction().contains("same experience ID"));
            ensure!(client.call("get_experience",json!({"id":id})).await?==original,"conflict changed its experience");
            ensure!(client.call("experience_history",json!({"id":id})).await?==history,"conflict changed its history");
            ensure!(client.call("get_learning_review",json!({"id":id})).await?==saved_review,"conflict published a review");
        }
        let mut corrected=base;corrected["assessments"]=json!([assessment]);
        let result=client.call("review_experience",json!({"review":corrected,"expected_review_revision":0})).await?;
        ensure!(result["review_revision"]==1,"corrected request did not complete: {result}");
        Ok::<_,anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    Ok(())
}

#[tokio::test]
async fn learning_history_and_explanations_return_all_or_the_explicit_positive_selection(
) -> Result<()> {
    use mimir_core::graph::MemoryType;
    let service = test_service().await?;
    let id = fixture_identity().await?;
    let project = format!("remaining-selection-{id}");
    let belief = isolation::seed_belief_in_project(
        "selection fixture",
        0.5,
        0.1,
        &project,
        MemoryType::Fact,
    )
    .await?;
    let mut client = Client::start(id)?;
    let checked = async {
        for assessment in [false,true] {
            for index in 0..21 {
                let experience_id = fixture_identity().await?;
                let source = json!({"id":experience_id,"project":project,"context":format!("selection {assessment} {index}"),"action":"record complete selection fixture","outcome":"unknown","source":"tool_result","evidence":["isolated fixture observation"],"belief_ids":[belief.id]});
                client.call("record_experience",json!({"experience":source,"expected_revision":0})).await?;
                let mut review = json!({"experience_id":experience_id,"experience_revision":1,"reviewer":"fixture","rationale":"unresolved fixture observation"});
                if assessment {
                    review["assessments"] = json!([{"target":{"belief_id":belief.id},"scope":"fixture","rubric":"fixture","correctness":{"value":null,"weight":0},"usefulness":{"value":null,"weight":0},"evidence_indices":[],"rationale":"unresolved"}]);
                } else {
                    review["feedback"] = json!([{"belief_id":belief.id,"verdict":"support","weight":0}]);
                }
                ensure!(client.call("review_experience",json!({"review":review,"expected_review_revision":0})).await?["review_revision"]==1);
            }
        }
        let history = json!({"project":project,"belief_id":belief.id,"scope":"fixture","rubric":"fixture"});
        let explanation = json!({"id":belief.id});
        for (name,base,field) in [("lesson_assessment_history",history,"entries"),("explain_belief",explanation,"reviews")] {
            for (limit,offset,want,next) in [(None,0,21,None),(Some(21),0,21,None),(Some(3),0,3,Some(3)),(None,3,18,None),(Some(3),3,3,Some(6)),(Some(u64::MAX),0,21,None),(None,u64::MAX,0,None)] {
                let mut request = base.clone();
                if let Some(count)=limit { request["limit"]=json!(count); }
                if offset!=0 { request["offset"]=json!(offset); }
                let result=client.call(name,request).await?;
                let page=if name=="explain_belief" { &result["learning"] } else { &result };
                ensure!(page[field].as_array().map(Vec::len)==Some(want),"wrong {name} selection: {result}");
                ensure!(page["next_offset"]==json!(next),"wrong {name} continuation: {result}");
            }
            for bad in [json!(0),json!(-1),json!("all"),json!(null)] {
                let mut request=base.clone();request["limit"]=bad;
                let correction:NeedsInput=serde_json::from_value(client.call(name,request).await?)?;
                ensure!(serde_json::to_value(&correction.issues()[0].fault().path)?==json!(["limit"]));
                ensure!(!correction.issues()[0].suggested_correction().is_empty());
            }
            ensure!(client.call(name,base).await?["status"]!="needs_input");
        }
        Ok::<_,anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    Ok(())
}

#[tokio::test]
async fn review_source_dialogues_precede_embedding_and_preserve_literal_evidence() -> Result<()> {
    use mimir_core::graph::MemoryType;
    let service = test_service().await?;
    let id = fixture_identity().await?;
    let bare_id = fixture_identity().await?;
    let project = format!("review-sources-{id}");
    let belief =
        isolation::seed_belief_in_project("source fixture", 0.5, 0.1, &project, MemoryType::Fact)
            .await?;
    let db = db::connect(&isolation::fixture().database_config()).await?;
    let mut client = Client::start(id)?;
    let checked = async {
        let source = json!({"id":id,"project":project,"context":"literal evidence","action":"read the saved source before extraction","outcome":"unknown","source":"agent_report","evidence":["event/0","wrapped/1"],"belief_ids":[belief.id],"source_records":[
            {"source_ref":"event/0","actor":"agent","provenance":"agent_report","text":"Proceed carefully."},
            {"source_ref":"wrapped/1","actor":"controller","provenance":"tool_result","text":"{\"actor\":\"agent\",\"message\":\"Check first\\nThen proceed\"}"}]});
        ensure!(client.call("record_experience",json!({"experience":source,"expected_revision":0})).await?["revision"]==1);
        let history = service.experience_history(id).await?;
        let item = json!({"kind":"suggestion","key":"check-first","source_ref":"wrapped/1","actor":"controller","statement":"Check first\\nThen proceed","conditions":"nested speaker remains interpretation"});
        let review = json!({"experience_id":id,"experience_revision":1,"reviewer":"fixture","rationale":"literal source words","extracted_items":[item],"source_coverage":[
            {"source_ref":"event/0","status":"unresolved","reason":"no outcome yet"},
            {"source_ref":"wrapped/1","status":"unresolved","reason":"no outcome yet"}]});
        let mut missing = review.clone(); missing["source_coverage"] = json!([]);
        let mut duplicate = review.clone(); duplicate["source_coverage"][1] = duplicate["source_coverage"][0].clone();
        let mut unknown_coverage = review.clone(); unknown_coverage["source_coverage"][1]["source_ref"] = json!("absent/2");
        let mut unknown_source = review.clone(); unknown_source["extracted_items"][0]["source_ref"] = json!("absent/2");
        let mut actor = review.clone(); actor["extracted_items"][0]["actor"] = json!("agent");
        let mut quote = review.clone(); quote["extracted_items"][0]["statement"] = json!("Check first\nThen proceed");
        let mut legacy = review.clone(); legacy["feedback"] = json!([{"belief_id":belief.id,"verdict":"support","weight":0.5}]);
        for (mut invalid,path,code) in [
            (missing,json!(["review","source_coverage"]),Code::MissingReference),
            (duplicate,json!(["review","source_coverage"]),Code::Duplicate),
            (unknown_coverage,json!(["review","source_coverage",1,"source_ref"]),Code::MissingReference),
            (unknown_source,json!(["review","extracted_items",0,"source_ref"]),Code::MissingReference),
            (actor,json!(["review","extracted_items",0,"actor"]),Code::WrongActor),
            (quote,json!(["review","extracted_items",0,"statement"]),Code::QuotationMismatch),
            (legacy,json!(["review"]),Code::UnsupportedCombination),
        ] {
            reference_correction(client.call("review_experience",json!({"review":invalid,"expected_review_revision":0})).await?,path.clone(),code)?;
            invalid["candidates"] = json!([{"kind":"belief","key":"must-not-embed","content":"complete candidate fixture","memory_type":"Fact"}]);
            reference_correction(client.call("review_experience",json!({"review":invalid,"expected_review_revision":0})).await?,path,code)?;
            ensure!(service.experience_history(id).await? == history);
            for table in ["mimir_learning_item_owners","mimir_review_candidates"] {
                ensure!(db.query_one(&format!("SELECT count(*) FROM {table} WHERE experience_id=$1"),&[&id]).await?.get::<_,i64>(0)==0);
            }
        }
        let bare = json!({"id":bare_id,"project":project,"context":"no source records","action":"do not invent sources","outcome":"unknown","source":"agent_report","evidence":[]});
        client.call("record_experience",json!({"experience":bare,"expected_revision":0})).await?;
        let mut invalid = review.clone(); invalid["experience_id"] = json!(bare_id);
        reference_correction(client.call("review_experience",json!({"review":invalid,"expected_review_revision":0})).await?,json!(["review","source_coverage"]),Code::UnsupportedCombination)?;
        invalid["source_coverage"] = json!([]);
        reference_correction(client.call("review_experience",json!({"review":invalid,"expected_review_revision":0})).await?,json!(["review","extracted_items"]),Code::UnsupportedCombination)?;
        let answer = client.call("review_experience",json!({"review":review,"expected_review_revision":0})).await?;
        ensure!(answer["review_revision"]==1 && answer["item_ids"]["check-first"].is_string());
        ensure!(client.call("review_experience",json!({"review":review,"expected_review_revision":0})).await? == answer);
        let saved = client.call("get_learning_review",json!({"id":id})).await?;
        ensure!(saved.to_string().contains("Check first\\\\nThen proceed"),"readback changed literal source escapes: {saved}");
        Ok::<_,anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    Ok(())
}

#[tokio::test]
async fn review_retention_is_checked_before_embedding_without_rewriting_original_items(
) -> Result<()> {
    let service = test_service().await?;
    let id = fixture_identity().await?;
    let project = format!("review-retention-{id}");
    let db = db::connect(&isolation::fixture().database_config()).await?;
    let mut client = Client::start(id)?;
    let checked = async {
        let source = json!({"id":id,"project":project,"context":"review retention","action":"preserve extracted evidence","outcome":"unknown","source":"agent_report","evidence":["original/0"],"source_records":[{"source_ref":"original/0","actor":"agent","provenance":"agent_report","text":"Check first. Then verify."}]});
        ensure!(client.call("record_experience",json!({"experience":source,"expected_revision":0})).await?["revision"]==1);
        let item = json!({"kind":"suggestion","key":"check-first","source_ref":"original/0","actor":"agent","statement":"Check first.","conditions":"not yet observed"});
        let review = json!({"experience_id":id,"experience_revision":1,"reviewer":"fixture","rationale":"keep the original quotation","extracted_items":[item],"source_coverage":[{"source_ref":"original/0","status":"unresolved","reason":"no observed outcome"}]});
        let original = client.call("review_experience",json!({"review":review,"expected_review_revision":0})).await?;
        ensure!(original["review_revision"]==1 && original["item_ids"]["check-first"].is_string());
        let history = service.experience_history(id).await?;
        let mut omitted = review.clone(); omitted["extracted_items"] = json!([]);
        let mut rewritten = review.clone(); rewritten["extracted_items"][0]["statement"] = json!("Then verify.");
        let mut kind = review.clone(); kind["extracted_items"][0]["kind"] = json!("decision");
        let mut renamed = review.clone(); renamed["extracted_items"][0]["key"] = json!("new-name");
        for mut invalid in [omitted.clone(),rewritten,kind,renamed] {
            reference_correction(client.call("review_experience",json!({"review":invalid,"expected_review_revision":1})).await?,json!(["review","extracted_items"]),Code::MissingReference)?;
            // A missing embedding backend must not mask this input mistake.
            invalid["candidates"] = json!([{"kind":"belief","key":"must-not-embed","content":"complete candidate fixture","memory_type":"Fact"}]);
            reference_correction(client.call("review_experience",json!({"review":invalid,"expected_review_revision":1})).await?,json!(["review","extracted_items"]),Code::MissingReference)?;
            ensure!(service.experience_history(id).await? == history);
            ensure!(db.query_one("SELECT count(*) FROM mimir_learning_item_owners WHERE experience_id=$1",&[&id]).await?.get::<_,i64>(0)==1);
            ensure!(db.query_one("SELECT count(*) FROM mimir_review_candidates WHERE experience_id=$1",&[&id]).await?.get::<_,i64>(0)==0);
        }
        ensure!(client.call("review_experience",json!({"review":review,"expected_review_revision":0})).await? == original);
        let mut revised = review.clone(); revised["extracted_items"][0]["conditions"] = json!("interpretation revised; quotation retained");
        let next = json!({"kind":"suggestion","key":"verify-next","source_ref":"original/0","actor":"agent","statement":"Then verify.","conditions":"not yet observed"});
        revised["extracted_items"].as_array_mut().unwrap().push(next);
        let answer = client.call("review_experience",json!({"review":revised,"expected_review_revision":1})).await?;
        ensure!(answer["review_revision"]==2 && answer["item_ids"]["check-first"]==original["item_ids"]["check-first"] && answer["item_ids"]["verify-next"].is_string());
        ensure!(client.call("review_experience",json!({"review":revised,"expected_review_revision":1})).await? == answer);
        let readback = client.call("get_learning_review",json!({"id":id})).await?;
        ensure!(readback["review_revision"]==2);
        ensure!(db.query_one("SELECT count(*) FROM mimir_learning_item_owners WHERE experience_id=$1",&[&id]).await?.get::<_,i64>(0)==2);
        Ok::<_,anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    Ok(())
}

#[tokio::test]
async fn source_retention_corrections_preserve_original_evidence_and_allow_appended_corrections(
) -> Result<()> {
    let service = test_service().await?;
    let id = fixture_identity().await?;
    let project = format!("source-retention-{id}");
    let db = db::connect(&isolation::fixture().database_config()).await?;
    let mut client = Client::start(id)?;
    let checked = async {
        let original_source = json!({"source_ref":"original/0","actor":"agent","provenance":"agent_report","text":"Check first.","recorded_at":"2026-11-08T00:00:00Z"});
        let source = json!({"id":id,"project":project,"context":"source retention","action":"retain the original observation","outcome":"unknown","source":"agent_report","evidence":["original/0"],"source_records":[original_source]});
        let original = client.call("record_experience",json!({"experience":source,"expected_revision":0})).await?;
        ensure!(original["revision"] == 1);
        ensure!(client.call("record_experience",json!({"experience":source,"expected_revision":0})).await? == original);
        let history = service.experience_history(id).await?;
        let mut changed_project = source.clone(); changed_project["project"] = json!(format!("other-{project}"));
        let mut missing = source.clone(); missing["source_records"] = json!([]); missing["evidence"] = json!([]);
        let mut cases = vec![(changed_project,json!(["experience","project"]),Code::WrongIdentity), (missing,json!(["experience","source_records"]),Code::MissingReference)];
        for (field,value) in [("text",json!("Changed words.")),("actor",json!("another actor")),("provenance",json!("user_feedback")),("recorded_at",json!("2026-11-08T01:00:00Z"))] {
            let mut invalid = source.clone(); invalid["source_records"][0][field] = value;
            cases.push((invalid,json!(["experience","source_records"]),Code::MissingReference));
        }
        for (mut invalid,path,code) in cases {
            invalid["learning_items"] = json!([{"kind":"suggestion","key":"tentative","source_ref":"original/0","actor":"agent","statement":"Check first.","conditions":"no observed outcome"}]);
            reference_correction(client.call("record_experience",json!({"experience":invalid,"expected_revision":1})).await?,path,code)?;
            ensure!(service.experience_history(id).await? == history);
            ensure!(db.query_one("SELECT count(*) FROM mimir_learning_item_owners WHERE experience_id=$1",&[&id]).await?.get::<_,i64>(0)==0,"refusal retained a tentative item allocation");
            let current = client.call("get_experience",json!({"id":id})).await?;
            ensure!(current["revision"]==1 && current["experience"]["source_records"][0]==original_source);
        }
        let correction = json!({"source_ref":"correction/1","actor":"human","provenance":"user_feedback","text":"The original instruction was incomplete."});
        let mut appended = source.clone(); appended["source_records"] = json!([original_source,correction]); appended["evidence"] = json!(["original/0","correction/1"]);
        let revised = client.call("record_experience",json!({"experience":appended,"expected_revision":1})).await?;
        ensure!(revised["revision"]==2 && revised["experience"]["source_records"][0]==original_source && revised["experience"]["source_records"][1]==correction);
        ensure!(client.call("record_experience",json!({"experience":appended,"expected_revision":1})).await? == revised);
        ensure!(service.experience_history(id).await? != history);
        Ok::<_,anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    Ok(())
}

#[tokio::test]
async fn candidate_name_corrections_preserve_declarations_history_and_completed_answers(
) -> Result<()> {
    use mimir_core::graph::MemoryType;
    let service = test_service().await?;
    let id = fixture_identity().await?;
    let project = format!("candidate-names-{id}");
    let belief = isolation::seed_belief_in_project(
        "candidate fixture",
        0.5,
        0.1,
        &project,
        MemoryType::Fact,
    )
    .await?;
    let database = isolation::fixture().database_config();
    let db = db::connect(&database).await?;
    let mut client = Client::start(id)?;
    let checked = async {
        let source = json!({"id":id,"project":project,"context":"candidate names","action":"read saved declarations","outcome":"unknown","source":"agent_report","evidence":["isolated fixture receipt"],"belief_ids":[belief.id]});
        ensure!(client.call("record_experience", json!({"experience":source,"expected_revision":0})).await?["revision"] == 1);
        let history = service.experience_history(id).await?;
        let candidate = json!({"kind":"pattern","key":"retry-step","situation":"retry an observed operation","approach":"read its saved answer first"});
        let review = json!({"experience_id":id,"experience_revision":1,"reviewer":"fixture","rationale":"one stable declaration","candidates":[candidate]});
        let mut duplicate = review.clone();
        duplicate["candidates"] = json!([candidate,candidate]);
        reference_correction(client.call("review_experience", json!({"review":duplicate,"expected_review_revision":0})).await?, json!(["review","candidates"]), Code::Duplicate)?;
        ensure!(service.experience_history(id).await? == history);
        let absent = json!({"candidate_key":"not-declared"});
        let present = json!({"belief_id":belief.id});
        let cases = [
            ("candidate_feedback",json!([{"target":absent,"verdict":"support","weight":0.5}]),json!(["review","candidate_feedback",0,"target","candidate_key"])),
            ("candidate_links",json!([{"from":absent,"to":present,"relation":"Supports","weight":0.5}]),json!(["review","candidate_links",0,"from","candidate_key"])),
            ("candidate_links",json!([{"from":present,"to":absent,"relation":"Supports","weight":0.5}]),json!(["review","candidate_links",0,"to","candidate_key"])),
            ("assessments",json!([{"target":absent,"scope":"fixture","rubric":"fixture","correctness":{"value":null,"weight":0},"usefulness":{"value":null,"weight":0},"evidence_indices":[],"rationale":"unresolved"}]),json!(["review","assessments",0,"target","candidate_key"])),
        ];
        for (field,value,path) in cases {
            let mut invalid = review.clone(); invalid[field] = value;
            reference_correction(client.call("review_experience", json!({"review":invalid,"expected_review_revision":0})).await?, path, Code::MissingReference)?;
            ensure!(service.experience_history(id).await? == history);
        }
        let mut wrong_kind = review.clone();
        wrong_kind["candidate_feedback"] = json!([{"target":{"candidate_key":"retry-step"},"verdict":"support","weight":0.5}]);
        reference_correction(client.call("review_experience", json!({"review":wrong_kind,"expected_review_revision":0})).await?,json!(["review","candidate_feedback",0,"target","candidate_key"]),Code::MissingReference)?;
        ensure!(service.experience_history(id).await? == history);
        ensure!(db.query_one("SELECT count(*) FROM mimir_review_candidates WHERE experience_id = $1", &[&id]).await?.get::<_,i64>(0) == 0);
        let original = client.call("review_experience", json!({"review":review,"expected_review_revision":0})).await?;
        let history = service.experience_history(id).await?;
        let node:uuid::Uuid = db.query_one("SELECT node_id FROM mimir_review_candidates WHERE experience_id = $1 AND candidate_key = 'retry-step'", &[&id]).await?.get(0);
        let mut changed = review.clone(); changed["candidates"][0]["approach"] = json!("changed declaration");
        reference_correction(client.call("review_experience",json!({"review":changed,"expected_review_revision":1})).await?,json!(["review","candidates",0,"key"]),Code::WrongIdentity)?;
        let mut batch = changed.clone();
        batch["candidates"] = json!([{"kind":"pattern","key":"new-first","situation":"must not publish","approach":"wait for a valid whole request"},changed["candidates"][0]]);
        reference_correction(client.call("review_experience",json!({"review":batch,"expected_review_revision":1})).await?,json!(["review","candidates",1,"key"]),Code::WrongIdentity)?;
        ensure!(service.experience_history(id).await? == history);
        ensure!(db.query_one("SELECT count(*) FROM mimir_review_candidates WHERE experience_id = $1", &[&id]).await?.get::<_,i64>(0) == 1);
        ensure!(client.call("review_experience",json!({"review":review,"expected_review_revision":0})).await? == original);
        client.call("delete_pattern",json!({"id":node})).await?;
        let mut fresh = review.clone(); fresh["rationale"] = json!("new review after deletion");
        reference_correction(client.call("review_experience",json!({"review":fresh,"expected_review_revision":1})).await?,json!(["review","candidates",0,"key"]),Code::MissingReference)?;
        ensure!(service.get_pattern(node).await?.is_none());
        ensure!(service.experience_history(id).await? == history);
        ensure!(client.call("review_experience",json!({"review":review,"expected_review_revision":0})).await? == original);
        ensure!(client.call("get_learning_review",json!({"id":id})).await?["review_revision"] == 1);
        Ok::<_,anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    Ok(())
}

async fn fixture_pattern(project: Option<&str>) -> Result<mimir_core::graph::Pattern> {
    let database = isolation::fixture().database_config();
    let db = db::connect(&database).await?;
    let row = db.query_one("SELECT gen_random_uuid(), now()", &[]).await?;
    let mut pattern = mimir_core::graph::Pattern::new(
        "reference fixture".into(),
        "explicit observed approach".into(),
        0.5,
    )?;
    pattern.id = row.get(0);
    pattern.created_at = row.get(1);
    pattern.project = project.map(str::to_owned);
    mimir_core::store::AgeStore::new(db, database.dbname)?
        .insert_pattern(&pattern)
        .await?;
    Ok(pattern)
}

fn reference_correction(value: Value, path: Value, code: Code) -> Result<()> {
    let response: NeedsInput = serde_json::from_value(value)?;
    let issue = &response.issues()[0];
    ensure!(
        issue.fault().code == code && serde_json::to_value(&issue.fault().path)? == path,
        "wrong reference diagnosis: {response:?}"
    );
    ensure!(
        issue.suggested_correction().contains("user")
            && issue
                .suggested_correction()
                .to_ascii_lowercase()
                .contains("do not")
    );
    Ok(())
}

#[tokio::test]
async fn learning_references_keep_exact_paths_and_refuse_before_preparation_or_publication(
) -> Result<()> {
    use mimir_core::graph::MemoryType;
    let service = test_service().await?;
    let id = fixture_identity().await?;
    let missing = fixture_identity().await?;
    let project = format!("learning-references-{id}");
    let other = format!("other-learning-references-{id}");
    let local =
        isolation::seed_belief_in_project("local fixture", 0.5, 0.1, &project, MemoryType::Fact)
            .await?;
    let foreign =
        isolation::seed_belief_in_project("foreign fixture", 0.5, 0.1, &other, MemoryType::Fact)
            .await?;
    let working = isolation::seed_belief_in_project(
        "working fixture",
        0.5,
        0.1,
        &project,
        MemoryType::Working,
    )
    .await?;
    let global = isolation::seed_belief("global fixture", 0.5, 0.1, MemoryType::Fact).await?;
    let pattern = fixture_pattern(Some(&other)).await?;
    let mut client = Client::start(id)?;
    let checked = async {
        let source = json!({"id":id,"project":project,"context":"reference fixture","action":"explicit isolated observation","outcome":"unknown","source":"agent_report","evidence":["isolated fixture receipt"]});
        for (belief, code) in [(missing, Code::MissingReference), (foreign.id, Code::WrongIdentity), (global.id, Code::WrongIdentity), (working.id, Code::UnsupportedCombination)] {
            let mut invalid = source.clone(); invalid["belief_ids"] = json!([belief]);
            reference_correction(client.call("record_experience", json!({"experience":invalid,"expected_revision":0})).await?, json!(["experience","belief_ids",0]), code)?;
            ensure!(service.get_experience(id).await?.is_none(), "refused reference published an experience");
            reference_correction(client.call("get_lesson_assessment", json!({"project":project,"belief_id":belief,"scope":"fixture","rubric":"fixture"})).await?, json!(["belief_id"]), code)?;
        }
        for (pattern_id, code) in [(missing, Code::MissingReference), (pattern.id, Code::WrongIdentity)] {
            let mut invalid = source.clone(); invalid["pattern_id"] = json!(pattern_id);
            reference_correction(client.call("record_experience", json!({"experience":invalid,"expected_revision":0})).await?, json!(["experience","pattern_id"]), code)?;
            ensure!(service.get_experience(id).await?.is_none());
        }
        let mut valid_source = source.clone(); valid_source["belief_ids"] = json!([local.id]);
        ensure!(client.call("record_experience", json!({"experience":valid_source,"expected_revision":0})).await?["revision"] == 1);
        let history = service.experience_history(id).await?;
        let review = json!({"experience_id":id,"experience_revision":1,"reviewer":"fixture","rationale":"no fabricated observation"});
        let absent = json!({"belief_id":missing});
        let present = json!({"belief_id":local.id});
        let cases = [
            ("feedback", json!([{"belief_id":missing,"verdict":"support","weight":0.5}]), json!(["review","feedback",0,"belief_id"])),
            ("superseded_beliefs", json!([missing]), json!(["review","superseded_beliefs",0])),
            ("links", json!([{"from_id":missing,"to_id":local.id,"relation":"Supports","weight":0.5}]), json!(["review","links",0,"from_id"])),
            ("links", json!([{"from_id":local.id,"to_id":missing,"relation":"Supports","weight":0.5}]), json!(["review","links",0,"to_id"])),
            ("assessments", json!([{"target":absent,"scope":"fixture","rubric":"fixture","correctness":{"value":null,"weight":0},"usefulness":{"value":null,"weight":0},"evidence_indices":[],"rationale":"unresolved"}]), json!(["review","assessments",0,"target","belief_id"])),
            ("candidate_feedback", json!([{"target":absent,"verdict":"support","weight":0.5}]), json!(["review","candidate_feedback",0,"target","belief_id"])),
            ("candidate_links", json!([{"from":absent,"to":present,"relation":"Supports","weight":0.5}]), json!(["review","candidate_links",0,"from","belief_id"])),
            ("candidate_links", json!([{"from":present,"to":absent,"relation":"Supports","weight":0.5}]), json!(["review","candidate_links",0,"to","belief_id"])),
        ];
        for (field, value, path) in cases {
            let mut invalid = review.clone(); invalid[field] = value;
            // If preparation ran first, the absent embedding configuration
            // would mask the actual invalid reference.
            invalid["candidates"] = json!([{"kind":"belief","key":"prepared-later","content":"complete candidate fixture","memory_type":"Fact"}]);
            reference_correction(client.call("review_experience", json!({"review":invalid,"expected_review_revision":0})).await?, path, Code::MissingReference)?;
            ensure!(service.experience_history(id).await? == history && service.get_experience(id).await?.unwrap().review_revision == 0);
        }
        ensure!(client.call("review_experience", json!({"review":review,"expected_review_revision":0})).await?["review_revision"] == 1);
        let score = client.call("get_lesson_assessment", json!({"project":project,"belief_id":local.id,"scope":"fixture","rubric":"fixture"})).await?;
        ensure!(score["status"] != "needs_input" && !score.is_null());
        Ok::<_, anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    let other_cleanup = service.delete_project(&other).await;
    let global_cleanup = service.delete_belief(global.id).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    other_cleanup?;
    global_cleanup?;
    Ok(())
}

#[tokio::test]
async fn permitted_project_and_global_patterns_remain_valid_references() -> Result<()> {
    let service = test_service().await?;
    let id = fixture_identity().await?;
    let project = format!("pattern-references-{id}");
    let local = fixture_pattern(Some(&project)).await?;
    let global = fixture_pattern(None).await?;
    let mut client = Client::start(id)?;
    let checked = async {
        for pattern in [&local, &global] {
            let source_id = fixture_identity().await?;
            let source = json!({"id":source_id,"project":project,"context":"pattern scope fixture","action":"explicit pattern use","outcome":"unknown","source":"agent_report","evidence":["isolated fixture"],"pattern_id":pattern.id});
            let recorded = client.call("record_experience", json!({"experience":source,"expected_revision":0})).await?;
            ensure!(recorded["revision"] == 1 && recorded["experience"]["pattern_id"] == json!(pattern.id), "permitted pattern was refused: {recorded}");
        }
        Ok::<_, anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    let global_cleanup = service.delete_pattern(global.id).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    global_cleanup?;
    Ok(())
}

#[tokio::test]
async fn item_identity_corrections_keep_authorship_and_roll_back_every_reservation() -> Result<()> {
    use mimir_core::graph::MemoryType;
    let service = test_service().await?;
    let id = fixture_identity().await?;
    let invented = fixture_identity().await?;
    let project = format!("item-corrections-{id}");
    let belief = isolation::seed_belief_in_project(
        "item assessment fixture",
        0.5,
        0.1,
        &project,
        MemoryType::Fact,
    )
    .await?;
    let db = db::connect(&isolation::fixture().database_config()).await?;
    let mut client = Client::start(id)?;
    let checked = async {
        let item = json!({"kind":"suggestion","actor":"agent","source_ref":"source/0","statement":"Check first.","conditions":"untried"});
        let mut source = json!({"id":id,"project":project,"context":"item identity fixture","action":"record the original suggestion","outcome":"unknown","source":"agent_report","evidence":["source/0"],"belief_ids":[belief.id],
            "source_records":[{"source_ref":"source/0","actor":"agent","provenance":"agent_report","text":"Check first. Then verify."}]});
        let mut id_only = item.clone(); id_only["id"] = json!(invented);
        let mut id_and_key = id_only.clone(); id_and_key["key"] = json!("new-item");
        let mut named = item.clone(); named["key"] = json!("check-first");
        for (items, index, field, code) in [
            (json!([id_only]), 0, "id", Code::MissingReference),
            (json!([item]), 0, "key", Code::MissingField),
            (json!([id_and_key]), 0, "id", Code::MissingReference),
            (json!([named,id_only]), 1, "id", Code::MissingReference),
        ] {
            let mut invalid = source.clone(); invalid["learning_items"] = items;
            reference_correction(client.call("record_experience", json!({"experience":invalid,"expected_revision":0})).await?,
                json!(["experience","learning_items",index,field]), code)?;
            ensure!(service.get_experience(id).await?.is_none());
            let count: i64 = db.query_one("SELECT count(*) FROM mimir_learning_item_owners WHERE experience_id=$1", &[&id]).await?.get(0);
            ensure!(count == 0, "refusal left a reserved item or partial source");
        }
        source["learning_items"] = json!([named]);
        let recorded = client.call("record_experience", json!({"experience":source,"expected_revision":0})).await?;
        let assigned = recorded["experience"]["learning_items"][0]["id"].clone();
        ensure!(assigned.is_string());
        ensure!(client.call("record_experience", json!({"experience":source,"expected_revision":0})).await? == recorded);
        let history = service.experience_history(id).await?;
        for (field, value) in [("id", json!(invented)), ("actor", json!("different speaker")), ("source_ref", json!("different/source"))] {
            let mut invalid = source.clone(); invalid["learning_items"][0][field] = value;
            reference_correction(client.call("record_experience", json!({"experience":invalid,"expected_revision":1})).await?,
                json!(["experience","learning_items",0,field]), Code::WrongIdentity)?;
            ensure!(service.experience_history(id).await? == history);
        }
        let extracted = json!({"kind":"suggestion","key":"verify-next","actor":"agent","source_ref":"source/0","statement":"Then verify.","conditions":"untried"});
        let review = json!({"experience_id":id,"experience_revision":1,"reviewer":"fixture","rationale":"original authorship retained",
            "source_coverage":[{"source_ref":"source/0","status":"unresolved","reason":"No observed outcome"}],"extracted_items":[extracted]});
        for (items, index, field, code) in [
            (json!([item]), 0, "key", Code::MissingField),
            (json!([id_and_key]), 0, "id", Code::MissingReference),
            (json!([extracted,id_only]), 1, "id", Code::MissingReference),
            (json!([{"kind":"suggestion","key":"check-first","actor":"different speaker","source_ref":"source/0","statement":"Check first.","conditions":"untried"}]), 0, "actor", Code::WrongIdentity),
        ] {
            let mut invalid = review.clone(); invalid["extracted_items"] = items;
            invalid["candidates"] = json!([{"kind":"belief","key":"must-not-prepare","content":"complete candidate fixture","memory_type":"Fact"}]);
            reference_correction(client.call("review_experience", json!({"review":invalid,"expected_review_revision":0})).await?,
                json!(["review","extracted_items",index,field]), code)?;
            ensure!(service.experience_history(id).await? == history);
        }
        let assessment = json!({"target":{"belief_id":belief.id},"scope":"fixture","rubric":"fixture","correctness":{"value":null,"weight":0},"usefulness":{"value":null,"weight":0},"evidence_indices":[],"item_keys":["verify-next"],"rationale":"unresolved"});
        let mut invalid = review.clone(); invalid["assessments"] = json!([assessment]);
        invalid["assessments"][0]["item_keys"] = json!(["unknown-item"]);
        reference_correction(client.call("review_experience", json!({"review":invalid,"expected_review_revision":0})).await?,
            json!(["review","assessments",0,"item_keys",0]), Code::MissingReference)?;
        ensure!(service.experience_history(id).await? == history);
        let count: i64 = db.query_one("SELECT count(*) FROM mimir_learning_item_owners WHERE experience_id=$1", &[&id]).await?.get(0);
        ensure!(count == 1, "refused review left a tentative allocation");
        let mut valid = review.clone(); valid["assessments"] = json!([assessment]);
        let reviewed = client.call("review_experience", json!({"review":valid,"expected_review_revision":0})).await?;
        ensure!(reviewed["review_revision"] == 1);
        let stored_id = reviewed["item_ids"]["verify-next"].clone();
        ensure!(stored_id.is_string() && stored_id != assigned);
        ensure!(client.call("review_experience", json!({"review":valid,"expected_review_revision":0})).await? == reviewed);
        let count: i64 = db.query_one("SELECT count(*) FROM mimir_learning_item_owners WHERE experience_id=$1", &[&id]).await?.get(0);
        ensure!(count == 2, "retry allocated a duplicate item");
        let readback = client.call("get_learning_review", json!({"id":id})).await?;
        ensure!(readback["review_revision"] == 1);
        Ok::<_, anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    Ok(())
}

#[tokio::test]
async fn completed_review_readback_survives_candidate_deletion_without_resurrection() -> Result<()>
{
    let service = test_service().await?;
    let id = fixture_identity().await?;
    let project = format!("completed-review-readback-{id}");
    let unrelated = fixture_pattern(Some(&project)).await?;
    let db = db::connect(&isolation::fixture().database_config()).await?;
    let mut client = Client::start(id)?;
    let checked = async {
        let source = json!({"id":id,"project":project,"context":"completed review fixture","action":"record one observation","outcome":"unknown","source":"agent_report","evidence":["isolated fixture receipt"]});
        client.call("record_experience", json!({"experience":source,"expected_revision":0})).await?;
        let review = json!({"experience_id":id,"experience_revision":1,"reviewer":"fixture","rationale":"retain the original completed answer",
            "candidates":[{"kind":"pattern","key":"retry-step","situation":"retry an observed operation","approach":"read the saved result before repeating it"}]});
        let original = client.call("review_experience", json!({"review":review,"expected_review_revision":0})).await?;
        let assigned: uuid::Uuid = original["candidate_ids"]["retry-step"].as_str().unwrap().parse()?;
        ensure!(service.get_pattern(assigned).await?.is_some());
        let history = service.experience_history(id).await?;
        let deleted = client.call("delete_pattern", json!({"id":assigned})).await?;
        ensure!(deleted == json!({"deleted":true}));
        ensure!(service.get_pattern(assigned).await?.is_none());
        for expected in [0, 1] {
            let replayed = client.call("review_experience", json!({"review":review,"expected_review_revision":expected})).await?;
            ensure!(replayed == original, "completed retry changed its original answer: {replayed}");
            ensure!(service.get_pattern(assigned).await?.is_none(), "readback resurrected the deleted candidate");
            ensure!(service.get_pattern(unrelated.id).await?.is_some(), "readback changed unrelated data");
            ensure!(service.experience_history(id).await? == history, "readback appended or rewrote review history");
        }
        let row = db.query_one("SELECT node_id,retired FROM mimir_review_candidates WHERE experience_id=$1 AND candidate_key=$2", &[&id, &"retry-step"]).await?;
        ensure!(row.get::<_, uuid::Uuid>(0) == assigned && row.get::<_, bool>(1), "readback changed the saved identity or retirement");
        let mut fresh = review.clone(); fresh["rationale"] = json!("a genuinely new review request");
        let fresh: mimir_core::learning::Review = serde_json::from_value(fresh)?;
        let refusal = service.review_experience(&fresh, 1).await.unwrap_err();
        ensure!(refusal.to_string().contains("deleted"), "new publication reused a retired key");
        ensure!(service.get_pattern(assigned).await?.is_none() && service.experience_history(id).await? == history);
        ensure!(client.call("get_learning_review", json!({"id":id})).await?["review_revision"] == 1);
        Ok::<_, anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    Ok(())
}

fn correction(value: Value, path: &[&str], reads: &[&str]) -> Result<()> {
    let response: NeedsInput = serde_json::from_value(value)?;
    let issue = &response.issues()[0];
    ensure!(issue.fault().code == Code::StaleRevision);
    ensure!(
        issue.fault().path
            == path
                .iter()
                .map(|key| Segment::Key((*key).into()))
                .collect::<Vec<_>>()
    );
    for name in reads {
        ensure!(
            issue.suggested_correction().contains(name),
            "missing readback {name}"
        );
    }
    ensure!(
        issue.suggested_correction().contains("Do not")
            || issue.suggested_correction().contains("do not")
    );
    Ok(())
}

#[tokio::test]
async fn stale_revisions_offer_readback_and_preserve_history_and_exact_retries() -> Result<()> {
    let fixture = isolation::fixture();
    let database = fixture.database_config();
    let db = db::connect(&database).await?;
    let id: uuid::Uuid = db.query_one("SELECT gen_random_uuid()", &[]).await?.get(0);
    let project = format!("revision-corrections-{id}");
    let service = MimirService::connect(&Config {
        database,
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?;
    let stderr = std::fs::File::create(
        fixture
            .root
            .join(format!("revision-corrections-{id}.stderr")),
    )?;
    let mut child = tokio::process::Command::new(&fixture.mcp)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(stderr)
        .kill_on_drop(true)
        .spawn()?;
    let input = child.stdin.take().unwrap();
    let output = BufReader::new(child.stdout.take().unwrap());
    let mut client = Client {
        child,
        input,
        output,
        next_id: 0,
    };
    let checked = async {
        let mut source = json!({"id":id,"project":project,"context":"revision fixture","action":"original observation","outcome":"unknown","source":"agent_report","evidence":["isolated fixture observation"]});
        correction(client.call("record_experience", json!({"experience":source,"expected_revision":1})).await?, &["expected_revision"], &["get_experience", "experience_history"])?;
        ensure!(service.get_experience(id).await?.is_none());
        let first = client.call("record_experience", json!({"experience":source,"expected_revision":0})).await?;
        ensure!(first["revision"] == 1);
        ensure!(client.call("record_experience", json!({"experience":source,"expected_revision":0})).await? == first, "exact create retry changed its result");
        source["action"] = json!("corrected observation");
        let second = client.call("record_experience", json!({"experience":source,"expected_revision":1})).await?;
        ensure!(second["revision"] == 2);
        let history = service.experience_history(id).await?;
        let mut stale = source.clone(); stale["action"] = json!("a competing stale correction");
        correction(client.call("record_experience", json!({"experience":stale,"expected_revision":1})).await?, &["expected_revision"], &["get_experience", "experience_history"])?;
        ensure!(service.experience_history(id).await? == history && service.get_experience(id).await?.unwrap().revision == 2);
        ensure!(client.call("get_experience", json!({"id":id})).await? == second);
        let mut review = json!({"experience_id":id,"experience_revision":1,"reviewer":"fixture","rationale":"no new beliefs or observed learning effects"});
        correction(client.call("review_experience", json!({"review":review,"expected_review_revision":0})).await?, &["review", "experience_revision"], &["get_experience", "get_learning_review", "experience_history"])?;
        ensure!(service.experience_history(id).await? == history);
        review["experience_revision"] = json!(2);
        let reviewed = client.call("review_experience", json!({"review":review,"expected_review_revision":0})).await?;
        ensure!(reviewed["review_revision"] == 1);
        let history = service.experience_history(id).await?;
        let mut changed = review.clone(); changed["rationale"] = json!("competing stale review");
        correction(client.call("review_experience", json!({"review":changed,"expected_review_revision":0})).await?, &["expected_review_revision"], &["get_experience", "get_learning_review"])?;
        ensure!(service.experience_history(id).await? == history, "refused review appended history or changed acknowledgement");
        let readback = client.call("get_learning_review", json!({"id":id})).await?;
        ensure!(readback["revision"] == 2 && readback["review_revision"] == 1 && readback["reviewed_revision"] == 2);
        ensure!(client.call("review_experience", json!({"review":review,"expected_review_revision":0})).await? == reviewed, "lost-reply retry did not return original review");
        ensure!(service.experience_history(id).await? == history);
        Ok::<_, anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    Ok(())
}
