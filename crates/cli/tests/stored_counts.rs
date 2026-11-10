//! Actual CLI read/sweep commands explain bad stored evidence without success.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{ensure, Result};
use mimir_core::{
    db,
    graph::{Edge, EdgeType, MemoryType},
    interaction::NeedsInput,
    store::AgeStore,
};

#[tokio::test]
async fn stored_count_dialog_prevents_a_fake_list_or_sweep_success() -> Result<()> {
    let fixture = isolation::fixture();
    let cfg = fixture.database_config();
    let audit = db::connect(&cfg).await?;
    let key: uuid::Uuid = audit
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let project = format!("stored-count-cli-{key}");
    let source =
        isolation::seed_belief_in_project("source", 0.8, 0.2, &project, MemoryType::Fact).await?;
    let target =
        isolation::seed_belief_in_project("target", 0.1, 0.2, &project, MemoryType::Fact).await?;
    let store = AgeStore::new(db::connect(&cfg).await?, cfg.dbname.clone())?;
    store
        .insert_edge(&Edge::new(source.id, target.id, EdgeType::Defeats, 1.0)?)
        .await?;
    audit.query(&format!("SELECT * FROM ag_catalog.cypher('{}', $$ MATCH (n:Belief {{id:'{}'}}) SET n.alpha0=-1.0 RETURN n.id $$) AS(id ag_catalog.agtype)",cfg.dbname,target.id),&[]).await?;
    let token = store
        .reserve_operation(&format!("stored-count-sweep-{key}"))
        .await?
        .operation_token
        .to_string();
    let config_path = fixture.root.join(format!("stored-count-policy-{key}.toml"));
    let mut config = std::fs::read_to_string(fixture.root.join("config.toml"))?;
    if !config.contains("[retirement]") {
        config.push_str("\n[retirement]\ngrace_hours=0\n");
    }
    std::fs::write(&config_path, config)?;
    for command in ["list", "sweep-defeated"] {
        let mut child = std::process::Command::new(env!("CARGO_BIN_EXE_mimir"));
        child
            .args([command, "--project", &project])
            .env("MIMIR_CONFIG", &config_path);
        if command == "sweep-defeated" {
            child.args(["--operation-token", &token]);
        }
        let output = child.output()?;
        std::fs::write(
            fixture
                .root
                .join(format!("stored-count-{command}-{key}.stdout")),
            &output.stdout,
        )?;
        std::fs::write(
            fixture
                .root
                .join(format!("stored-count-{command}-{key}.stderr")),
            &output.stderr,
        )?;
        std::fs::write(
            fixture
                .root
                .join(format!("stored-count-{command}-{key}.exit")),
            format!("{}\n", output.status),
        )?;
        ensure!(output.status.success(), "inspect retained {command} stderr");
        let correction: NeedsInput = mimir_json::from_slice(&output.stdout)?;
        ensure!(correction.issues()[0]
            .fault()
            .message
            .contains(&target.id.to_string()));
        ensure!(correction.issues()[0].fault().message.contains("alpha0"));
    }
    audit.query(&format!("SELECT * FROM ag_catalog.cypher('{}', $$ MATCH (n:Belief {{id:'{}'}}) SET n.alpha0={} RETURN n.id $$) AS(id ag_catalog.agtype)",cfg.dbname,target.id,target.alpha0),&[]).await?;
    ensure!(store.get_belief(target.id).await?.is_some());
    store.delete_project(&project).await?;
    Ok(())
}
