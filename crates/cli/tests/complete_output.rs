//! Complete selected content through the real CLI, using the owned test database.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use mimir_core::{
    config::Config,
    db,
    documents::DocumentChunk,
    graph::{MemoryType, Pattern},
    store::AgeStore,
    MimirService,
};
use std::process::Command;

#[tokio::test]
async fn query_evidence_keeps_every_supporting_passage_beyond_three() -> Result<()> {
    let fixture = isolation::fixture();
    let cfg = Config {
        database: fixture.database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let service = MimirService::connect(&cfg).await?;
    let db = db::connect(&cfg.database).await?;
    let id: uuid::Uuid = db.query_one("SELECT gen_random_uuid()", &[]).await?.get(0);
    let project = format!("cli-evidence-selection-{id}");
    let store = AgeStore::new(
        db::connect(&cfg.database).await?,
        cfg.database.dbname.clone(),
    )?;
    let checked = async {
        let belief = isolation::seed_belief_in_project(
            "completequeryevidence fixture",
            0.5,
            0.1,
            &project,
            MemoryType::Fact,
        )
        .await?;
        let mut passages = Vec::new();
        for index in 0..5 {
            let chunk_id: uuid::Uuid = db.query_one("SELECT gen_random_uuid()", &[]).await?.get(0);
            let text = format!("supporting passage {index}: retain this condition in full");
            let chunk = DocumentChunk::with_id(
                chunk_id,
                format!("/mimir-test/{project}/{index}.md"),
                vec![],
                text.clone(),
                None,
                Some(project.clone()),
            );
            store.insert_document_chunk(&chunk).await?;
            service
                .add_evidence(belief.id, chunk_id, 0.1 + index as f64 / 10.)
                .await?;
            passages.push(text);
        }
        for (name, selection) in [("all", vec![]), ("one-belief", vec!["--limit", "1"])] {
            let output = Command::new(env!("CARGO_BIN_EXE_mimir"))
                .args([
                    "query",
                    "completequeryevidence",
                    "--project",
                    &project,
                    "--evidence",
                ])
                .args(selection)
                .output()?;
            let log = fixture
                .root
                .join(format!("query-five-passages-{id}-{name}"));
            std::fs::write(log.with_extension("stdout"), &output.stdout)?;
            std::fs::write(log.with_extension("stderr"), &output.stderr)?;
            std::fs::write(
                log.with_extension("exit"),
                format!("{:?}\n", output.status.code()),
            )?;
            ensure!(
                output.status.success(),
                "CLI failed; retained output at {}",
                log.display()
            );
            let text = String::from_utf8(output.stdout)?;
            for passage in &passages {
                ensure!(
                    text.contains(passage),
                    "missing passage {passage:?}; retained output at {}",
                    log.display()
                );
            }
            ensure!(
                text.lines()
                    .filter(|line| line.trim_start().starts_with('↳'))
                    .count()
                    == 5
            );
        }
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = service.delete_project(&project).await;
    checked?;
    cleanup?;
    Ok(())
}

#[tokio::test]
async fn cli_keeps_complete_beliefs_patterns_and_supporting_passages() -> Result<()> {
    let fixture = isolation::fixture();
    let cfg = Config {
        database: fixture.database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let svc = MimirService::connect(&cfg).await?;
    let client = db::connect(&cfg.database).await?;
    let ids = client
        .query_one("SELECT gen_random_uuid(), gen_random_uuid()", &[])
        .await?;
    let pattern_id: uuid::Uuid = ids.get(0);
    let chunk_id: uuid::Uuid = ids.get(1);
    let project = format!("complete-cli-output-{pattern_id}");
    let store = AgeStore::new(client, cfg.database.dbname.clone())?;
    let checked = async {
        let content = format!(
            "  {}\nfinal belief condition\t ",
            "λ complete belief ".repeat(250)
        );
        let situation = format!("{}final situation", "long situation ".repeat(200));
        let approach = format!("{}final approach", "long approach 全文 ".repeat(200));
        let passage = format!(
            "{}\nfinal supporting condition",
            "complete supporting text λ ".repeat(300)
        );
        let belief =
            isolation::seed_belief_in_project(&content, 0.8, 0.4, &project, MemoryType::Fact)
                .await?;
        let mut pattern = Pattern::new(situation.clone(), approach.clone(), 0.7)?;
        pattern.id = pattern_id;
        pattern.project = Some(project.clone());
        store.insert_pattern(&pattern).await?;
        let chunk = DocumentChunk::with_id(
            chunk_id,
            format!("/mimir-test/{project}.md"),
            vec!["support".into()],
            passage.clone(),
            None,
            Some(project.clone()),
        );
        store.insert_document_chunk(&chunk).await?;
        store
            .insert_chunk_embedding(chunk_id, &[1.0, 0.0, 0.0])
            .await?;
        svc.add_evidence(belief.id, chunk_id, 0.9).await?;
        let execute = |args: &[&str]| -> Result<String> {
            let output = Command::new(env!("CARGO_BIN_EXE_mimir"))
                .args(args)
                .output()?;
            ensure!(
                output.status.success(),
                "CLI failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            Ok(String::from_utf8(output.stdout)?)
        };
        let beliefs = execute(&["list", "--project", &project])?;
        ensure!(
            beliefs.contains(&content),
            "the actual list command must retain the whole belief including whitespace"
        );
        let patterns = execute(&["patterns", "--project", &project])?;
        ensure!(
            patterns.contains(&situation) && patterns.contains(&approach),
            "both pattern texts must survive the actual patterns command"
        );
        let evidence = execute(&["evidence", "list", &belief.id.to_string()])?;
        ensure!(
            evidence.contains(&passage),
            "the actual evidence command must retain the complete passage"
        );
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = svc.delete_project(&project).await;
    checked?;
    cleanup?;
    Ok(())
}
