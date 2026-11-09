#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
#[path = "../../../tests/support/retrieval_preference.rs"]
mod preference;

use anyhow::{ensure, Result};
use mimir_core::{config::Config, graph::MemoryType, MimirService};

#[tokio::test]
async fn supporting_passages_preserve_search_preference_and_selection() -> Result<()> {
    let config = Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let service = MimirService::connect(&config).await?;
    let fixture = preference::PreferenceFixture::create(&config).await?;
    let checked = async {
        let ordinary = service
            .query_relevant(&fixture.query, None, Some(&fixture.project), None)
            .await?;
        ensure!(
            ordinary.beliefs[0].id == fixture.ordinary_first,
            "fixture must expose preference"
        );
        for limit in [None, std::num::NonZeroUsize::new(1)] {
            let preferred = service
                .query_relevant(
                    &fixture.query,
                    limit,
                    Some(&fixture.project),
                    Some(MemoryType::Experiential),
                )
                .await?;
            ensure!(
                preferred.beliefs[0].id == fixture.preferred_first,
                "preference must change selection"
            );
            let enriched = service
                .query_relevant_grounded_preferred(
                    &fixture.query,
                    limit,
                    None,
                    Some(&fixture.project),
                    Some(MemoryType::Experiential),
                )
                .await?;
            ensure!(
                enriched
                    .beliefs
                    .iter()
                    .map(|b| b.belief.id)
                    .collect::<Vec<_>>()
                    == preferred.beliefs.iter().map(|b| b.id).collect::<Vec<_>>(),
                "support changed selection or order"
            );
            ensure!(
                serde_json::to_value(&enriched.retrieval)?
                    == serde_json::to_value(&preferred.retrieval)?,
                "support changed coverage report"
            );
            ensure!(
                enriched.beliefs.iter().all(
                    |b| b.evidence.len() == 1 && b.evidence[0].snippet.contains(&fixture.query)
                ),
                "supporting passages missing"
            );
        }
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = fixture.cleanup().await;
    checked?;
    cleanup
}
