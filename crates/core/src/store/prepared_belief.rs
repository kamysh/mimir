//! Publish one prepared belief, its vector and indexed grounding together.
use super::{learning_transaction, snapshot_transaction, vector_query, AgeStore, VectorTable};
use crate::{
    graph::Belief,
    interaction::Location,
    preparation::{compatible_projects, PreparationRequired, PreparedBelief, SupportingPassage},
    validation::{Code, Segment},
    GROUND_THRESHOLD,
};
use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use pgvector::Vector;
use uuid::Uuid;

impl AgeStore {
    pub(crate) async fn owns_belief_preparation(&self, belief: &Belief) -> Result<bool> {
        Ok(self.client.lock().await.query_one(
            "SELECT EXISTS(SELECT 1 FROM mimir_embedding_owners WHERE owner_token=$1 AND project IS NOT DISTINCT FROM $2)",
            &[&belief.id, &belief.project],
        ).await?.get(0))
    }

    pub(crate) async fn reserve_belief_preparation(
        &self,
        project: Option<&str>,
    ) -> Result<(Uuid, DateTime<Utc>)> {
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let row = tx.query_one("INSERT INTO mimir_embedding_owners(project) VALUES($1) RETURNING owner_token,reserved_at", &[&project]).await?;
        let identity = (row.get(0), row.get(1));
        tx.commit().await?;
        Ok(identity)
    }

    pub(crate) async fn prepare_belief_support(
        &self,
        belief: &Belief,
        vector: &[f32],
    ) -> Result<Vec<SupportingPassage>> {
        let mut client = self.client.lock().await;
        let tx = snapshot_transaction(&mut client).await?;
        let vector = Vector::from(vector.to_vec());
        let sql = vector_query(VectorTable::Chunks, None, false, true);
        let rows = tx.query(&sql, &[&vector]).await?;
        let mut support = Vec::new();
        for row in rows {
            let similarity: f64 = row.try_get("similarity")?;
            anyhow::ensure!(similarity.is_finite(), "An indexed document produced a nonfinite grounding score; check its stored embedding before retrying.");
            if similarity < GROUND_THRESHOLD {
                continue;
            }
            let id = Uuid::parse_str(row.try_get::<_, &str>(0)?)?;
            let Some(chunk) = self.get_chunk_by_id_on(tx.client(), id).await? else {
                continue;
            };
            if !chunk.content.is_empty()
                && compatible_projects(belief.project.as_deref(), chunk.project.as_deref())
            {
                support.push(SupportingPassage {
                    chunk,
                    weight: crate::graph::Probability::new(similarity)?,
                });
            }
        }
        tx.commit().await?;
        Ok(support)
    }

    pub(crate) async fn publish_prepared_belief(
        &self,
        prepared: &PreparedBelief,
    ) -> Result<Belief> {
        let belief = &prepared.belief;
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        self.insert_prepared_belief_on(&tx, prepared).await?;
        self.recompute_learning(&tx, None, [belief.id].into())
            .await?;
        let published = self.get_belief_on(tx.client(), belief.id).await?.context(
            "Prepared publication did not retain its belief; the transaction was not committed",
        )?;
        tx.commit().await.with_context(|| format!("The publication outcome for belief {} must be read back before retrying. Read that belief and its indexed grounding; do not allocate a replacement identity.", belief.id))?;
        Ok(published)
    }

    pub(super) async fn insert_prepared_belief_on(
        &self,
        tx: &tokio_postgres::Transaction<'_>,
        prepared: &PreparedBelief,
    ) -> Result<()> {
        let belief = &prepared.belief;
        // Every refusal below precedes this candidate's writes. The caller
        // owns the transaction; returning an error rolls back any earlier
        // uncommitted candidates too. Never relabel transport/write errors.
        let owner_exists: bool = tx.query_one(
            "SELECT EXISTS(SELECT 1 FROM mimir_embedding_owners WHERE owner_token=$1 AND project IS NOT DISTINCT FROM $2)",
            &[&belief.id, &belief.project],
        ).await?.get(0);
        if !owner_exists {
            return Err(PreparationRequired::new(Location::Request, vec![], Code::MissingReference,
                format!("Preparation {} no longer owns publication: its work was cancelled, its project was deleted, or publication already completed. Read the original operation outcome and get_belief for this ID, then ask the user before starting new work. No new belief was stored.", belief.id)).into());
        }
        if self.get_belief_on(tx.client(), belief.id).await?.is_some() {
            return Err(PreparationRequired::new(
                Location::Arguments,
                vec![Segment::Key("id".into())],
                Code::WrongIdentity,
                format!("Prepared belief {} already exists. Read its current state and the original operation outcome before retrying; do not allocate a replacement identity. No new belief was stored.", belief.id),
            ).into());
        }
        anyhow::ensure!(
            crate::preparation::usable_vector(&prepared.vector) && !prepared.support.is_empty(),
            "Only a complete validated preparation may enter publication"
        );
        for passage in &prepared.support {
            let current = self
                .get_chunk_by_id_on(tx.client(), passage.chunk.id)
                .await?;
            let indexed: bool = tx
                .query_one(
                    "SELECT EXISTS(SELECT 1 FROM public.chunk_embeddings WHERE chunk_id=$1)",
                    &[&passage.chunk.id],
                )
                .await?
                .get(0);
            if current.as_ref() != Some(&passage.chunk) || !indexed {
                return Err(PreparationRequired::new(
                    Location::Arguments,
                    vec![Segment::Key("content".into())],
                    Code::MissingReference,
                    format!("Supporting indexed passage {} changed or disappeared during preparation. Read the current document and ask the user how to proceed. No belief was stored.", passage.chunk.id),
                ).into());
            }
        }

        self.insert_belief_on(tx.client(), belief, prepared.provenance.as_ref())
            .await?;
        self.insert_belief_embedding_on(tx.client(), belief.id, &prepared.vector)
            .await?;
        for passage in &prepared.support {
            self.insert_grounding_on(tx.client(), passage.chunk.id, belief.id, passage.weight)
                .await?;
        }
        tx.execute(
            "DELETE FROM mimir_embedding_owners WHERE owner_token=$1",
            &[&belief.id],
        )
        .await?;
        Ok(())
    }
}
