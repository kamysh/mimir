//! Delete the full ownership closure before publishing one transaction.
use super::{age_execute, age_query_rows, json_esc, AgeStore, RegisteredStep, StepDecision};
use crate::operation_catalogue::CommitSite;
use anyhow::{ensure, Context, Result};
use serde_json::json;
use tokio_postgres::{Client, Transaction};
use uuid::Uuid;

impl AgeStore {
    async fn project_node_ids(
        &self,
        client: &Client,
        project: &str,
        label: &str,
    ) -> Result<Vec<Uuid>> {
        let graph = &self.graph_name;
        let name = format!("age_project_ids_{}", Uuid::new_v4().simple());
        let prepare=format!("PREPARE {name}(agtype) AS SELECT id::text FROM ag_catalog.cypher('{graph}', $$ MATCH (n:{label}) WHERE n.project = $project RETURN n.id $$, $1) AS (id agtype)");
        let parameters = mimir_json::to_string(&json!({"project":project}))?;
        age_query_rows(client, &name, &prepare, &parameters)
            .await?
            .iter()
            .map(|row| {
                let raw = row
                    .get(0)
                    .context("A project-owned node has no id; deletion was not committed")?;
                let text = if raw.starts_with('"') {
                    mimir_json::from_str::<String>(raw)?
                } else {
                    raw.to_owned()
                };
                Uuid::parse_str(&text)
                    .context("A project-owned node has an invalid UUID; deletion was not committed")
            })
            .collect()
    }

    async fn delete_project_in(&self, tx: &Transaction<'_>, project: &str) -> Result<usize> {
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        tx.execute(
            "DELETE FROM mimir_embedding_owners WHERE project=$1",
            &[&project],
        )
        .await?;
        let client = tx.client();
        // Keep every discovery key until the dependent rows are known.
        let beliefs = self.project_node_ids(client, project, "Belief").await?;
        let chunks = self
            .project_node_ids(client, project, "DocumentChunk")
            .await?;
        let graph = &self.graph_name;
        let parameters = format!(r#"{{"project":"{}"}}"#, json_esc(project));
        for label in ["Belief", "Pattern"] {
            let name = format!("age_project_delete_{}", Uuid::new_v4().simple());
            let prepare=format!("PREPARE {name}(agtype) AS SELECT * FROM ag_catalog.cypher('{graph}', $$ MATCH (n:{label}) WHERE n.project = $project DETACH DELETE n RETURN 1 $$, $1) AS (ok agtype)");
            age_execute(client, &name, &prepare, &parameters).await?;
        }
        tx.execute(
            "DELETE FROM public.belief_embeddings WHERE belief_id = ANY($1)",
            &[&beliefs],
        )
        .await?;
        self.delete_document_chunks_in(tx, &chunks).await?;
        tx.execute(
            "DELETE FROM public.chunk_embeddings WHERE chunk_id = ANY($1)",
            &[&chunks],
        )
        .await?;
        tx.execute(
            "DELETE FROM mimir_experiences WHERE project=$1",
            &[&project],
        )
        .await?;
        Ok(beliefs.len() + chunks.len())
    }

    /// Original service/CLI callers also use the same atomic closure. Their
    /// token admission is connected by the later public-interface changes.
    pub async fn delete_project(&self, project: &str) -> Result<usize> {
        let mut client = self.client.lock().await;
        let tx = super::learning_transaction(&mut client).await?;
        let count = self.delete_project_in(&tx, project).await?;
        tx.commit().await?;
        Ok(count)
    }

    /// The entire deletion and its original result share the final-step commit.
    pub async fn delete_project_operation(&self, step: &RegisteredStep) -> Result<StepDecision> {
        ensure!(
            step.description().site == CommitSite::ProjectDeletion.name(),
            "Use the registered delete_project step; no project data was changed"
        );
        let owner = AgeStore {
            client: self.client.clone(),
            graph_name: self.graph_name.clone(),
        };
        self.commit_final_operation_step(step,move|tx,request|Box::pin(async move {
            let project=request.arguments().get("project").and_then(serde_json::Value::as_str).context("delete_project requires the admitted project string; correct the request before writing")?;
            let count=owner.delete_project_in(tx,project).await?;
            let reply=json!({"deleted":count});
            Ok((reply.clone(),reply))
        })).await
    }
}
