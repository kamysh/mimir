// THROWAWAY diagnostic (remove after use). Isolates the BGE vector leg of
// query_relevant: embeds a query with the local backend and ranks all beliefs by
// cosine (store.query_beliefs_by_vector), then reports where the seeded
// eval-hidden-ua belief lands. Pins whether the verbose-prompt miss is the
// embedding/query side (belief ranks low) or the rrf×probability fusion/sort
// (belief ranks high here but gets buried in the full query_relevant).
//
// Diagnostic probes require the owned fixture from scripts/test-isolated.py.
// They never accept deployment database settings.

#[allow(dead_code)] // Shared guard exposes helpers for several test targets.
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use mimir_core::{
    config::{Config, DatabaseConfig, EmbeddingBackend, EmbeddingsConfig},
    db,
    embed::make_backend_with_worker,
    store::AgeStore,
    MimirService,
};

fn local_embeddings() -> EmbeddingsConfig {
    EmbeddingsConfig {
        backend: EmbeddingBackend::Local,
        model: String::new(),
        api_key: None,
        cache_dir: None,
    }
}

fn test_db_config() -> DatabaseConfig {
    isolation::fixture().database_config()
}

const VERBOSE_PROMPT: &str = "# Fix the artifact download\n\n`./fetch.sh` is supposed to download a build artifact by calling the local\n`./artifact_server` tool, producing a file `artifact.bin` in this directory.\nRunning `./fetch.sh` currently fails.\n\nMake `./fetch.sh` succeed so that `artifact.bin` is created. You may edit\n`fetch.sh`. Do **not** modify `artifact_server`.";
const EVAL_QUERY: &str = "artifact_server fetch.sh download 403 forbidden user-agent";

#[tokio::test]
#[ignore]
async fn vector_leg_ranking() {
    let cfg = test_db_config();
    let graph = cfg.dbname.clone();
    let client = db::connect(&cfg).await.expect("connect");
    let store = AgeStore::new(client, graph).expect("valid graph_name");

    let all = store.list_beliefs().await.expect("list_beliefs");
    let n = all.len();
    // Target = the seeded eval-hidden-ua belief (its content carries the UA).
    let target = all
        .iter()
        .find(|b| b.content.contains("mimir-eval/1.0"))
        .expect("seeded eval-hidden-ua belief present");
    println!(
        "\nN beliefs = {n}; target = {} (p={:.2})",
        target.id,
        target.probability.value()
    );

    let embedder = make_backend_with_worker(&local_embeddings(), isolation::fixture().mcp.into())
        .expect("initialize embedding backend");

    for (label, q) in [
        ("VERBOSE_PROMPT", VERBOSE_PROMPT),
        ("EVAL_QUERY", EVAL_QUERY),
    ] {
        let qv = embedder
            .embed(&[q.to_string()])
            .await
            .expect("embed")
            .pop()
            .expect("one vector");
        let ranked = store
            .query_beliefs_by_vector(&qv, None)
            .await
            .expect("vector query");
        let rank = ranked.iter().position(|id| *id == target.id);
        println!("\n===== {label} =====");
        match rank {
            Some(i) => println!("target rank = {} / {}", i + 1, ranked.len()),
            None => println!("target NOT in vector results ({} returned)", ranked.len()),
        }
        println!("top 10 by cosine:");
        for (i, id) in ranked.iter().take(10).enumerate() {
            if let Some(b) = all.iter().find(|b| b.id == *id) {
                let mark = if b.id == target.id { " <== TARGET" } else { "" };
                let c: String = b.content.chars().take(80).collect();
                println!(
                    "  {:>2}. p={:.2} {}{}",
                    i + 1,
                    b.probability.value(),
                    c,
                    mark
                );
            }
        }
    }
}

// Acceptance test for the two-stage rerank: the FULL query_relevant must surface
// the seeded eval-hidden-ua belief near the top for BOTH the verbose prompt and
// the curated query. (Downloads the reranker ONNX on first run; no Anthropic API.)
// Requires a seeded disposable fixture; excluded from ordinary release checks.
#[tokio::test]
#[ignore]
async fn full_query_relevant_ranking() {
    let cfg = Config {
        database: test_db_config(),
        embeddings: Some(local_embeddings()),
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let svc = MimirService::connect_with_worker(&cfg, isolation::fixture().mcp.into())
        .await
        .expect("connect");

    for (label, q) in [
        ("VERBOSE_PROMPT", VERBOSE_PROMPT),
        ("EVAL_QUERY", EVAL_QUERY),
    ] {
        let t0 = std::time::Instant::now();
        let res = svc
            .query_relevant(q, std::num::NonZeroUsize::new(10), None, None)
            .await
            .expect("query_relevant");
        let elapsed = t0.elapsed();
        let rank = res
            .iter()
            .position(|b| b.content.contains("mimir-eval/1.0"));
        println!("\n===== full query_relevant: {label}  ({elapsed:?}) =====");
        match rank {
            Some(i) => println!("target rank = {} / {} returned", i + 1, res.len()),
            None => println!("target NOT in top {} returned", res.len()),
        }
        for (i, b) in res.iter().enumerate() {
            let mark = if b.content.contains("mimir-eval/1.0") {
                " <== TARGET"
            } else {
                ""
            };
            let c: String = b.content.chars().take(80).collect();
            println!(
                "  {:>2}. p={:.2} {}{}",
                i + 1,
                b.probability.value(),
                c,
                mark
            );
        }
    }
}
