use anyhow::{Context, Result};
use std::future::Future;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use tokenizers::Tokenizer;
use tract_onnx::prelude::*;

use crate::config::{EmbeddingBackend, EmbeddingsConfig};

// ---------------------------------------------------------------------------
// Trait
// ---------------------------------------------------------------------------

/// Boxed, sendable future returned by [`EmbeddingProvider::embed`].
pub type EmbedFuture<'a> = Pin<Box<dyn Future<Output = Result<Vec<Vec<f32>>>> + Send + 'a>>;

pub trait EmbeddingProvider: Send + Sync {
    fn embed<'a>(&'a self, texts: &'a [String]) -> EmbedFuture<'a>;
}

// ---------------------------------------------------------------------------
// Voyage AI
// ---------------------------------------------------------------------------

pub struct VoyageBackend {
    api_key: String,
    model: String,
    http: reqwest::Client,
}

impl VoyageBackend {
    fn new(api_key: String, model: String) -> Self {
        Self {
            api_key,
            model,
            http: reqwest::Client::new(),
        }
    }
}

impl EmbeddingProvider for VoyageBackend {
    fn embed<'a>(&'a self, texts: &'a [String]) -> EmbedFuture<'a> {
        Box::pin(async move {
            let body = serde_json::json!({
                "input": texts,
                "model": self.model,
                "input_type": "document"
            });
            let resp: serde_json::Value = self
                .http
                .post("https://api.voyageai.com/v1/embeddings")
                .bearer_auth(&self.api_key)
                .json(&body)
                .send()
                .await?
                .error_for_status()?
                .json()
                .await?;
            parse_embeddings(&resp)
        })
    }
}

// ---------------------------------------------------------------------------
// OpenAI
// ---------------------------------------------------------------------------

pub struct OpenAiBackend {
    api_key: String,
    model: String,
    http: reqwest::Client,
}

impl OpenAiBackend {
    fn new(api_key: String, model: String) -> Self {
        Self {
            api_key,
            model,
            http: reqwest::Client::new(),
        }
    }
}

impl EmbeddingProvider for OpenAiBackend {
    fn embed<'a>(&'a self, texts: &'a [String]) -> EmbedFuture<'a> {
        Box::pin(async move {
            let body = serde_json::json!({
                "input": texts,
                "model": self.model
            });
            let resp: serde_json::Value = self
                .http
                .post("https://api.openai.com/v1/embeddings")
                .bearer_auth(&self.api_key)
                .json(&body)
                .send()
                .await?
                .error_for_status()?
                .json()
                .await?;
            parse_embeddings(&resp)
        })
    }
}

// ---------------------------------------------------------------------------
// Local (tract ONNX + HuggingFace tokenizers)
// ---------------------------------------------------------------------------

const HF_MODEL_ID: &str = "BAAI/bge-base-en-v1.5";
const MAX_SEQ_LEN: usize = 512;
pub const LOCAL_DIM: usize = 768;

type TractPlan = SimplePlan<TypedFact, Box<dyn TypedOp>, Graph<TypedFact, Box<dyn TypedOp>>>;

struct EmbedState {
    tokenizer: Tokenizer,
    model: Mutex<TractPlan>,
}

pub struct LocalBackend {
    state: Mutex<Option<Arc<EmbedState>>>,
    batch_size: Option<usize>,
    cache_dir: Option<PathBuf>,
}

impl LocalBackend {
    fn new(batch_size: usize, cache_dir: Option<String>) -> Self {
        let batch_size = if batch_size == 0 {
            None
        } else {
            Some(batch_size)
        };
        let cache_dir = cache_dir.and_then(|p| {
            let t = p.trim().to_string();
            if t.is_empty() {
                None
            } else {
                Some(PathBuf::from(t))
            }
        });
        Self {
            state: Mutex::new(None),
            batch_size,
            cache_dir,
        }
    }

    fn ensure_loaded(&self) -> Result<Arc<EmbedState>> {
        let mut guard = self
            .state
            .lock()
            .map_err(|_| anyhow::anyhow!("embed state mutex poisoned"))?;
        if let Some(ref s) = *guard {
            return Ok(Arc::clone(s));
        }
        let state = Arc::new(load_embed_state(self.cache_dir.as_deref())?);
        *guard = Some(Arc::clone(&state));
        Ok(state)
    }
}

/// Resolve the on-disk cache root for the model files. Uses the supplied
/// `cache_dir` if any, otherwise `$HOME/.cache/mimir/models`.
fn local_model_root(cache_dir: Option<&std::path::Path>) -> Result<std::path::PathBuf> {
    if let Some(p) = cache_dir {
        return Ok(p.to_path_buf());
    }
    let home = std::env::var_os("HOME")
        .ok_or_else(|| anyhow::anyhow!("HOME is not set; cannot locate cache directory"))?;
    Ok(std::path::PathBuf::from(home).join(".cache/mimir/models"))
}

/// Download `url` to `dest` if `dest` does not already exist. Writes to a
/// `.part` sibling first and renames on success so an interrupted download
/// never leaves a half-written file in place.
///
/// We use `reqwest::blocking` directly instead of `hf-hub` because hf-hub 0.3.2
/// has a redirect bug: when the CDN sends a relative `Location` header it
/// passes that string straight into `ureq::Agent::get()`, which fails with
/// `Bad URL: relative URL without a base`. `reqwest`'s redirect policy resolves
/// relative `Location` against the prior request's URL the way the HTTP spec
/// expects.
fn ensure_cached(url: &str, dest: &std::path::Path) -> Result<()> {
    if dest.exists() {
        return Ok(());
    }
    // `reqwest::blocking` builds (and on drop tears down) its own tokio runtime.
    // Model files are first fetched lazily from inside `tokio::spawn_blocking`
    // (embedder / reranker load on first query_relevant), and tearing a runtime
    // down inside any tokio context panics with "Cannot drop a runtime in a
    // context where blocking is not allowed". Run the whole blocking download on
    // a detached OS thread that carries no runtime context, so the teardown is
    // legal regardless of how we were called.
    let url = url.to_string();
    let dest = dest.to_path_buf();
    std::thread::spawn(move || download_blocking(&url, &dest))
        .join()
        .map_err(|_| anyhow::anyhow!("download thread panicked"))?
}

/// Blocking download of `url` to `dest`. Writes to a `.part` sibling first and
/// renames on success so an interrupted download never leaves a half-written
/// file in place. MUST run on a thread with no tokio runtime context (see
/// `ensure_cached`).
///
/// We use `reqwest::blocking` directly instead of `hf-hub` because hf-hub 0.3.2
/// has a redirect bug: when the CDN sends a relative `Location` header it passes
/// that string straight into `ureq::Agent::get()`, which fails with `Bad URL:
/// relative URL without a base`. `reqwest`'s redirect policy resolves relative
/// `Location` against the prior request's URL the way the HTTP spec expects.
fn download_blocking(url: &str, dest: &std::path::Path) -> Result<()> {
    if let Some(parent) = dest.parent() {
        std::fs::create_dir_all(parent)
            .with_context(|| format!("creating {}", parent.display()))?;
    }
    tracing::info!(url, dest = %dest.display(), "downloading model file");
    let client = reqwest::blocking::Client::builder()
        .timeout(std::time::Duration::from_secs(600))
        .redirect(reqwest::redirect::Policy::limited(10))
        .build()
        .context("building HTTP client")?;
    let bytes = client
        .get(url)
        .send()
        .with_context(|| format!("GET {url}"))?
        .error_for_status()
        .with_context(|| format!("HTTP error for {url}"))?
        .bytes()
        .with_context(|| format!("reading body of {url}"))?;
    let tmp = dest.with_extension("part");
    std::fs::write(&tmp, &bytes).with_context(|| format!("writing {}", tmp.display()))?;
    std::fs::rename(&tmp, dest).with_context(|| format!("renaming to {}", dest.display()))?;
    Ok(())
}

fn load_embed_state(cache_dir: Option<&std::path::Path>) -> Result<EmbedState> {
    tracing::info!("initialising local embedding model ({HF_MODEL_ID}, {LOCAL_DIM} dims) — downloading on first use if not cached");

    // Cache layout: <root>/<model-id-with-/-replaced-by-->/{tokenizer.json, onnx/model.onnx}.
    let root = local_model_root(cache_dir)?;
    let model_dir = root.join(HF_MODEL_ID.replace('/', "--"));
    let tokenizer_path = model_dir.join("tokenizer.json");
    let model_path = model_dir.join("onnx/model.onnx");

    ensure_cached(
        &format!("https://huggingface.co/{HF_MODEL_ID}/resolve/main/tokenizer.json"),
        &tokenizer_path,
    )
    .context("downloading tokenizer.json")?;
    ensure_cached(
        &format!("https://huggingface.co/{HF_MODEL_ID}/resolve/main/onnx/model.onnx"),
        &model_path,
    )
    .context("downloading onnx/model.onnx")?;

    let tokenizer = Tokenizer::from_file(&tokenizer_path)
        .map_err(|e| anyhow::anyhow!("loading tokenizer: {e}"))?;

    let model = tract_onnx::onnx()
        .model_for_path(&model_path)
        .context("loading ONNX model")?
        .into_optimized()
        .context("optimizing ONNX model")?
        .into_runnable()
        .context("making model runnable")?;

    Ok(EmbedState {
        tokenizer,
        model: Mutex::new(model),
    })
}

impl EmbeddingProvider for LocalBackend {
    fn embed<'a>(&'a self, texts: &'a [String]) -> EmbedFuture<'a> {
        let texts = texts.to_vec();
        let batch_size = self.batch_size;
        Box::pin(async move {
            if texts.is_empty() {
                return Ok(vec![]);
            }
            let state = self.ensure_loaded()?;
            tokio::task::spawn_blocking(move || embed_with_state(&state, &texts, batch_size))
                .await
                .map_err(|e| anyhow::anyhow!("local embeddings task failed: {e}"))?
        })
    }
}

fn embed_with_state(
    state: &EmbedState,
    texts: &[String],
    batch_size: Option<usize>,
) -> Result<Vec<Vec<f32>>> {
    let chunk_size = batch_size.unwrap_or(texts.len()).max(1);
    let mut all_embeddings = Vec::with_capacity(texts.len());

    for chunk in texts.chunks(chunk_size) {
        let mut encodings = state
            .tokenizer
            .encode_batch(chunk.to_vec(), true)
            .map_err(|e| anyhow::anyhow!("tokenizer encode_batch: {e}"))?;

        // Pad all sequences in the chunk to the same length, capped at MAX_SEQ_LEN.
        let seq_len = encodings
            .iter()
            .map(|e| e.get_ids().len())
            .max()
            .unwrap_or(0)
            .min(MAX_SEQ_LEN);
        let batch = chunk.len();

        let mut input_ids = vec![0i64; batch * seq_len];
        let mut attention_mask = vec![0i64; batch * seq_len];
        let mut token_type_ids = vec![0i64; batch * seq_len];

        for (b, enc) in encodings.iter_mut().enumerate() {
            let ids = enc.get_ids();
            let masks = enc.get_attention_mask();
            let types = enc.get_type_ids();
            let len = ids.len().min(seq_len);
            for s in 0..len {
                input_ids[b * seq_len + s] = ids[s] as i64;
                attention_mask[b * seq_len + s] = masks[s] as i64;
                token_type_ids[b * seq_len + s] = types[s] as i64;
            }
        }

        let ids_t: Tensor =
            tract_ndarray::Array2::from_shape_vec((batch, seq_len), input_ids)?.into();
        let mask_t: Tensor =
            tract_ndarray::Array2::from_shape_vec((batch, seq_len), attention_mask.clone())?.into();
        let types_t: Tensor =
            tract_ndarray::Array2::from_shape_vec((batch, seq_len), token_type_ids)?.into();

        let outputs = state
            .model
            .lock()
            .map_err(|_| anyhow::anyhow!("model mutex poisoned"))?
            .run(tvec![ids_t.into(), mask_t.into(), types_t.into()])
            .context("running ONNX model")?;

        // last_hidden_state: [batch, seq, 768]
        let hidden = outputs[0]
            .to_array_view::<f32>()
            .context("extracting model output")?;

        for b in 0..batch {
            let mut emb = vec![0f32; LOCAL_DIM];
            let mut count = 0f32;
            for s in 0..seq_len {
                if attention_mask[b * seq_len + s] > 0 {
                    for d in 0..LOCAL_DIM {
                        emb[d] += hidden[[b, s, d]];
                    }
                    count += 1.0;
                }
            }
            if count > 0.0 {
                for v in &mut emb {
                    *v /= count;
                }
            }
            all_embeddings.push(emb);
        }
    }
    Ok(all_embeddings)
}

// ---------------------------------------------------------------------------
// Factory
// ---------------------------------------------------------------------------

pub fn make_backend(cfg: &EmbeddingsConfig) -> Box<dyn EmbeddingProvider> {
    match cfg.backend {
        EmbeddingBackend::Voyage => Box::new(VoyageBackend::new(
            cfg.api_key.clone().unwrap_or_default(),
            cfg.model.clone(),
        )),
        EmbeddingBackend::OpenAi => Box::new(OpenAiBackend::new(
            cfg.api_key.clone().unwrap_or_default(),
            cfg.model.clone(),
        )),
        EmbeddingBackend::Local => {
            Box::new(LocalBackend::new(cfg.batch_size, cfg.cache_dir.clone()))
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn parse_embeddings(resp: &serde_json::Value) -> Result<Vec<Vec<f32>>> {
    let data = resp["data"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("missing 'data' array in embedding response"))?;
    data.iter()
        .map(|item| {
            item["embedding"]
                .as_array()
                .ok_or_else(|| anyhow::anyhow!("missing 'embedding' in data item"))?
                .iter()
                .map(|v| {
                    v.as_f64()
                        .map(|f| f as f32)
                        .ok_or_else(|| anyhow::anyhow!("non-numeric value in embedding"))
                })
                .collect::<Result<Vec<f32>>>()
        })
        .collect()
}
