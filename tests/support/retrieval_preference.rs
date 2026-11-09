//! Shared, owned database state for testing preference/evidence composition.
use anyhow::Result;
use mimir_core::{
    config::Config,
    db,
    documents::DocumentChunk,
    graph::{Belief, MemoryType, Probability},
    store::AgeStore,
};
use uuid::Uuid;

pub struct PreferenceFixture {
    pub project: String,
    pub query: String,
    pub ordinary_first: Uuid,
    pub preferred_first: Uuid,
    store: AgeStore,
}

impl PreferenceFixture {
    pub async fn create(config: &Config) -> Result<Self> {
        let client = db::connect(&config.database).await?;
        let mut ids: Vec<Uuid> = client
            .query("SELECT gen_random_uuid() FROM generate_series(1, 6)", &[])
            .await?
            .into_iter()
            .map(|row| row.get(0))
            .collect();
        ids.sort();
        let project = format!("preference-evidence-{}", ids[5]);
        let query = format!("preferenceevidence{}", ids[5].simple());
        let store = AgeStore::new(client, config.database.dbname.clone())?;
        let chunk = DocumentChunk::with_id(
            ids[5],
            format!("/mimir-test/{project}.md"),
            vec!["support".into()],
            format!("Complete supporting passage for {query}"),
            None,
            Some(project.clone()),
        );
        let setup = async {
            store.insert_document_chunk(&chunk).await?;
            for (index, &id) in ids[..5].iter().enumerate() {
                let mut belief = Belief::new_in_project(
                    query.clone(),
                    if index == 0 { 0.95 } else { 0.5 },
                    0.2,
                    project.clone(),
                )?
                .with_memory_type(if index == 0 {
                    MemoryType::Fact
                } else {
                    MemoryType::Experiential
                });
                belief.id = id;
                store.insert_belief(&belief).await?;
                // This is controlled low-level fixture state, not public publication.
                store
                    .insert_evidence(chunk.id, belief.id, Probability::new(0.5)?)
                    .await?;
            }
            Ok::<_, anyhow::Error>(())
        }
        .await;
        if let Err(error) = setup {
            store.delete_project(&project).await?;
            return Err(error);
        }
        Ok(Self {
            project,
            query,
            ordinary_first: ids[0],
            preferred_first: ids[1],
            store,
        })
    }

    pub async fn cleanup(&self) -> Result<()> {
        self.store.delete_project(&self.project).await?;
        Ok(())
    }
}
