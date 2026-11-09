//! Production pattern creation uses PostgreSQL metadata in its publication.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use mimir_core::{config::Config, db, graph::Pattern, store::AgeStore, MimirService};

fn config() -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    }
}

async fn setup() -> Result<(AgeStore, MimirService)> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let store = AgeStore::new(db::connect(&cfg.database).await?, cfg.database.dbname)?;
    Ok((store, service))
}

#[tokio::test]
async fn both_service_paths_publish_the_exact_server_metadata_and_preserve_other_patterns(
) -> Result<()> {
    let cfg = config();
    let (store, service) = setup().await?;
    let audit = db::connect(&cfg.database).await?;
    let suffix: String = audit
        .query_one("SELECT replace(gen_random_uuid()::text,'-','')", &[])
        .await?
        .get(0);
    let marker = format!("server-metadata-{suffix}");
    let function = format!("check_pattern_metadata_{suffix}");
    let trigger = format!("check_pattern_metadata_{suffix}");
    let graph = cfg.database.dbname.replace('"', "\"\"");
    // A client-generated time precedes this publication's transaction. This
    // database assertion catches that regression without comparing wall clocks
    // or trying to prove the external UUID generator's uniqueness.
    audit.batch_execute(&format!(r#"
CREATE FUNCTION public.{function}() RETURNS trigger LANGUAGE plpgsql AS $body$
BEGIN
  IF NEW.properties::text::jsonb->>'situation' = '{marker}' AND
     (NEW.properties::text::jsonb->>'created_at')::timestamptz IS DISTINCT FROM transaction_timestamp()
  THEN RAISE EXCEPTION 'pattern did not consume the PostgreSQL creation timestamp'; END IF;
  RETURN NEW;
END
$body$;
CREATE TRIGGER {trigger} BEFORE INSERT ON "{graph}"."Pattern"
FOR EACH ROW EXECUTE FUNCTION public.{function}();
"#)).await?;
    let created: Result<Vec<Pattern>> = async {
        let retained = service
            .add_pattern("unrelated metadata fixture", &suffix, 0.4)
            .await?;
        let retained_before = serde_json::to_value(store.get_pattern(retained.id).await?)?;
        let unscoped = service
            .add_pattern(&marker, "unscoped creation", 0.6)
            .await?;
        let scoped = service
            .add_pattern_in_project(&marker, "scoped creation", 0.8, Some(&marker))
            .await?;
        ensure!(unscoped.project.is_none());
        ensure!(scoped.project.as_deref() == Some(marker.as_str()));
        for pattern in [&unscoped, &scoped] {
            ensure!(
                serde_json::to_value(store.get_pattern(pattern.id).await?)?
                    == serde_json::to_value(Some(pattern))?
            );
            ensure!(pattern.activation_count == 0);
        }
        ensure!(serde_json::to_value(store.get_pattern(retained.id).await?)? == retained_before);
        Ok(vec![unscoped, scoped, retained])
    }
    .await;
    audit
        .batch_execute(&format!(
            r#"DROP TRIGGER {trigger} ON "{graph}"."Pattern"; DROP FUNCTION public.{function}();"#
        ))
        .await?;
    for pattern in created? {
        store.delete_pattern(pattern.id).await?;
    }
    Ok(())
}

#[tokio::test]
async fn invalid_success_values_do_not_publish_patterns() -> Result<()> {
    let (store, service) = setup().await?;
    let audit = db::connect(&config().database).await?;
    let marker: String = audit
        .query_one("SELECT gen_random_uuid()::text", &[])
        .await?
        .get(0);
    for invalid in [-0.1, 1.1, f64::NAN, f64::INFINITY] {
        ensure!(service
            .add_pattern(&marker, "invalid unscoped", invalid)
            .await
            .is_err());
        ensure!(service
            .add_pattern_in_project(&marker, "invalid scoped", invalid, Some(&marker))
            .await
            .is_err());
    }
    ensure!(!store
        .list_patterns()
        .await?
        .iter()
        .any(|p| p.situation == marker));
    Ok(())
}
