//! The original file preparation is metadata. The complete document and its
//! final answer publish together only after owned embedding succeeds.
use super::{AgeStore, OperationBindingRequest, RegisteredStep, StepDecision};
use crate::{
    documents::{parse_markdown, DocumentChunk},
    interaction::Location,
    operation_catalogue::CommitSite,
    preparation::PreparationRequired,
    validation::{Code, Segment},
};
use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio_postgres::Client;
use uuid::Uuid;

pub(crate) fn issue(code: Code, message: impl Into<String>) -> anyhow::Error {
    PreparationRequired::document(
        Location::Request,
        vec![Segment::Key("operation_token".into())],
        code,
        message.into(),
    )
    .into()
}

#[derive(Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Arguments {
    pub(crate) path: String,
    pub(crate) project: Option<String>,
}

pub(crate) fn document_arguments(request: &OperationBindingRequest) -> Result<Arguments> {
    let decode = || -> Result<Arguments> {
        anyhow::ensure!(
            request.operation() == "load_document",
            "The token belongs to a different operation"
        );
        crate::preparation::validate_operation_settings(request.settings())?;
        let arguments: Arguments = mimir_json::decode_ref(request.arguments())?;
        anyhow::ensure!(
            !arguments.path.trim().is_empty(),
            "The original path must contain nonblank text"
        );
        anyhow::ensure!(
            arguments
                .project
                .as_ref()
                .is_none_or(|project| !project.trim().is_empty()),
            "Supply a nonblank project or omit that optional field"
        );
        Ok(arguments)
    };
    decode().map_err(|error| issue(Code::MalformedInput, format!("The original document request is not usable: {error:#}. Read its saved binding and outcome before deciding whether to cancel and reserve corrected work. No document was replaced.")))
}

pub(crate) struct DocumentDraft {
    pub(crate) path: String,
    pub(crate) source: String,
    pub(crate) chunks: Vec<DocumentChunk>,
}

impl DocumentDraft {
    pub(crate) fn read(arguments: &Arguments) -> Result<Self> {
        let read = || -> Result<Self> {
            let path = std::fs::canonicalize(&arguments.path)
                .context("cannot resolve the original document path")?;
            let path = path
                .to_str()
                .context("the resolved document path is not UTF-8")?
                .to_owned();
            let source = std::fs::read_to_string(&path)
                .context("cannot read the original document as UTF-8")?;
            let chunks = parse_markdown(&source, &path, arguments.project.as_deref());
            Ok(Self {
                path,
                source,
                chunks,
            })
        };
        read().map_err(|error| PreparationRequired::document(Location::Arguments,
            vec![Segment::Key("path".into())], Code::MissingReference,
            format!("The requested document could not be prepared: {error:#}. Supply a readable file. The existing index was not changed.")).into())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct DocumentPreparation {
    pub(crate) owner_token: Uuid,
    pub(crate) reserved_at: DateTime<Utc>,
    pub(crate) declared_dimensions: Option<usize>,
    pub(crate) project: Option<String>,
    pub(crate) path: String,
    pub(crate) source: String,
    pub(crate) chunks: Vec<DocumentChunk>,
    pub(crate) previous: Vec<DocumentChunk>,
}

impl AgeStore {
    async fn document_snapshot_on(
        &self,
        client: &Client,
        path: &str,
    ) -> Result<Vec<DocumentChunk>> {
        let mut chunks = Vec::new();
        for id in self.get_chunk_ids_for_document_on(client, path).await? {
            chunks.push(
                self.get_chunk_by_id_on(client, id)
                    .await?
                    .context("The document changed while its original index was being read")?,
            );
        }
        chunks.sort_by_key(|chunk| chunk.id);
        Ok(chunks)
    }

    pub(crate) async fn reserve_document_operation(
        &self,
        step: &RegisteredStep,
        mut draft: DocumentDraft,
    ) -> Result<StepDecision> {
        document_arguments(step.expected())?;
        anyhow::ensure!(
            step.description().site == CommitSite::DocumentPreparation.name(),
            "Use the registered original document-preparation step"
        );
        let token = step.token();
        let store = AgeStore {
            client: self.client.clone(),
            graph_name: self.graph_name.clone(),
        };
        self.commit_operation_step(step, move |tx, original| Box::pin(async move {
            let arguments = document_arguments(original)?;
            tx.query("SELECT pg_advisory_xact_lock(671942183)", &[]).await?;
            let previous = store.document_snapshot_on(tx.client(), &draft.path).await?;
            let owner = tx.query_one("INSERT INTO mimir_embedding_owners(project,operation_token) VALUES($1,$2) RETURNING owner_token,reserved_at", &[&arguments.project, &token]).await?;
            // pgvector stores its declared dimension in this column's typmod.
            // This is the existing database value domain, not a work quota.
            let dimensions: i32 = tx.query_one("SELECT atttypmod FROM pg_attribute WHERE attrelid='public.chunk_embeddings'::regclass AND attname='embedding' AND NOT attisdropped", &[]).await?.try_get(0)?;
            let declared_dimensions = match dimensions {
                -1 => None, // The actual column permits different dimensions.
                dimensions if dimensions > 0 => Some(usize::try_from(dimensions)?),
                _ => return Err(issue(Code::UnsupportedCombination, "The document vector column has an invalid dimension declaration. Inspect its schema before retrying; no document was replaced.")),
            };
            // Parser identities are temporary links only. Every identity saved
            // in the preparation and later document rows comes from PostgreSQL.
            let count = i64::try_from(draft.chunks.len()).context("document chunk count does not fit PostgreSQL's allocation parameter")?;
            let allocated = tx.query("SELECT gen_random_uuid() FROM generate_series(1,$1::bigint)", &[&count]).await?;
            let mapping: HashMap<Uuid, Uuid> = draft.chunks.iter().zip(allocated.iter())
                .map(|(chunk, row)| Ok((chunk.id, row.try_get(0)?))).collect::<Result<_>>()?;
            anyhow::ensure!(mapping.len() == draft.chunks.len(), "temporary document identities are inconsistent; no document was published");
            for chunk in &mut draft.chunks {
                chunk.id = mapping[&chunk.id];
                chunk.parent_id = chunk.parent_id.map(|id| mapping.get(&id).copied()
                    .context("document parent is absent from its complete preparation")).transpose()?;
            }
            let prepared = DocumentPreparation { owner_token: owner.try_get(0)?, reserved_at: owner.try_get(1)?, declared_dimensions,
                project: arguments.project, path: draft.path, source: draft.source, chunks: draft.chunks, previous };
            Ok(mimir_json::to_value(prepared)?)
        })).await
    }

    pub(crate) async fn document_preparation_is_current(
        &self,
        token: Uuid,
        prepared: &DocumentPreparation,
    ) -> Result<bool> {
        let mut client = self.client.lock().await;
        let read = super::snapshot_transaction(&mut client).await?;
        let owner: bool = read.query_one("SELECT EXISTS(SELECT 1 FROM mimir_embedding_owners WHERE owner_token=$1 AND operation_token=$2 AND project IS NOT DISTINCT FROM $3)",
            &[&prepared.owner_token, &token, &prepared.project]).await?.get(0);
        let unchanged = owner
            && self
                .document_snapshot_on(read.client(), &prepared.path)
                .await?
                == prepared.previous;
        read.rollback().await?;
        Ok(unchanged)
    }

    pub(crate) async fn publish_document_operation(
        &self,
        first: &RegisteredStep,
        final_step: &RegisteredStep,
        prepared: &DocumentPreparation,
        vectors: &[Vec<f32>],
    ) -> Result<StepDecision> {
        document_arguments(final_step.expected())?;
        anyhow::ensure!(
            first.token() == final_step.token()
                && first.expected() == final_step.expected()
                && first.description().site == CommitSite::DocumentPreparation.name()
                && final_step.description().site == CommitSite::DocumentReplacement.name(),
            "Use the original complete document plan"
        );
        super::conformance::validate_document_batch(&prepared.path, &prepared.chunks, vectors)?;
        let token = final_step.token();
        let first_key = first.id().to_owned();
        let prepared = prepared.clone();
        let vectors = vectors.to_vec();
        let store = AgeStore {
            client: self.client.clone(),
            graph_name: self.graph_name.clone(),
        };
        self.commit_final_operation_step(final_step, move |tx, original| Box::pin(async move {
            let arguments = document_arguments(original)?;
            tx.query("SELECT pg_advisory_xact_lock(671942183)", &[]).await?;
            let saved: String = tx.query_one("SELECT reply::text FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2", &[&token, &first_key]).await?.try_get(0)?;
            let original: DocumentPreparation = mimir_json::from_str(&saved)?;
            if original != prepared || prepared.project != arguments.project {
                return Err(issue(Code::WrongIdentity, "The final preparation differs from this token's saved original. Read its saved preparation; no replacement was published."));
            }
            let owner = tx.query_opt("SELECT owner_token FROM mimir_embedding_owners WHERE owner_token=$1 AND operation_token=$2 AND project IS NOT DISTINCT FROM $3 FOR KEY SHARE",
                &[&prepared.owner_token, &token, &prepared.project]).await?;
            if owner.is_none() || store.document_snapshot_on(tx.client(), &prepared.path).await? != prepared.previous {
                return Err(issue(Code::MissingReference, "Document preparation was revoked or its original index changed. Open a user dialog before retrying; the old index and this operation's saved preparation remain unchanged."));
            }
            store.replace_document_in(tx, &prepared.path, &prepared.chunks, &vectors).await?;
            tx.execute("DELETE FROM mimir_embedding_owners WHERE owner_token=$1", &[&prepared.owner_token]).await?;
            let answer = serde_json::json!({"loaded": prepared.chunks.len()});
            Ok((answer.clone(), answer))
        })).await
    }
}
