// THROWAWAY diagnostic (remove after use). Isolates the BGE vector leg of
// query_relevant: embeds a query with the local backend and ranks all beliefs by
// cosine (store.query_beliefs_by_vector), then reports where the seeded
// eval-hidden-ua belief lands. Pins whether the verbose-prompt miss is the
// embedding/query side (belief ranks low) or the rrf×probability fusion/sort
// (belief ranks high here but gets buried in the full query_relevant).
//
// Run (no Anthropic API; uses the live graph + local BGE model):
//   MIMIR_HOST=localhost MIMIR_PORT=5450 MIMIR_DBNAME=mimir MIMIR_USER=mimir \
//     cargo test -p mimir-core --test vector_probe -- --nocapture --ignored

use mimir_core::{
    config::{Config, DatabaseConfig, EmbeddingBackend, EmbeddingsConfig, SslMode},
    db,
    embed::make_backend,
    store::AgeStore,
    MimirService,
};

fn local_embeddings() -> EmbeddingsConfig {
    EmbeddingsConfig {
        backend: EmbeddingBackend::Local,
        model: String::new(),
        api_key: None,
        batch_size: 0,
        cache_dir: None,
    }
}

fn test_db_config() -> DatabaseConfig {
    DatabaseConfig {
        host: std::env::var("MIMIR_HOST").expect("MIMIR_HOST"),
        port: std::env::var("MIMIR_PORT")
            .expect("MIMIR_PORT")
            .parse()
            .unwrap(),
        dbname: std::env::var("MIMIR_DBNAME").expect("MIMIR_DBNAME"),
        user: std::env::var("MIMIR_USER").expect("MIMIR_USER"),
        ssl_mode: SslMode::default(),
        ssl_root_cert: None,
        ssl_client_cert: None,
        ssl_client_key: None,
        pgbouncer: false,
        max_connections: 10,
    }
}

const VERBOSE_PROMPT: &str = "# Fix the artifact download\n\n`./fetch.sh` is supposed to download a build artifact by calling the local\n`./artifact_server` tool, producing a file `artifact.bin` in this directory.\nRunning `./fetch.sh` currently fails.\n\nMake `./fetch.sh` succeed so that `artifact.bin` is created. You may edit\n`fetch.sh`. Do **not** modify `artifact_server`.";
const EVAL_QUERY: &str = "artifact_server fetch.sh download 403 forbidden user-agent";

#[tokio::test]
#[ignore]
async fn vector_leg_ranking() {
    let cfg = test_db_config();
    let graph = cfg.dbname.clone();
    let pool = db::connect(&cfg).await.expect("connect");
    let store = AgeStore::new(pool, graph);

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

    let embedder = make_backend(&local_embeddings());

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
            .query_beliefs_by_vector(&qv, 0)
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
//   MIMIR_HOST=localhost MIMIR_PORT=5450 MIMIR_DBNAME=mimir MIMIR_USER=mimir \
//     cargo test -p mimir-core --test vector_probe -- --nocapture --ignored full_query
#[tokio::test]
#[ignore]
async fn full_query_relevant_ranking() {
    let cfg = Config {
        database: test_db_config(),
        embeddings: Some(local_embeddings()),
    };
    let svc = MimirService::connect(&cfg).await.expect("connect");

    for (label, q) in [
        ("VERBOSE_PROMPT", VERBOSE_PROMPT),
        ("EVAL_QUERY", EVAL_QUERY),
    ] {
        let t0 = std::time::Instant::now();
        let res = svc.query_relevant(q, 10).await.expect("query_relevant");
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
