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
