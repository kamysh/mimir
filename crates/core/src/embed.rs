use anyhow::Result;
use fastembed::{EmbeddingModel, InitOptions, TextEmbedding};
use std::future::Future;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::{Arc, Mutex};

use crate::config::{EmbeddingBackend, EmbeddingsConfig};

// ---------------------------------------------------------------------------
// Trait
// ---------------------------------------------------------------------------

pub trait EmbeddingProvider: Send + Sync {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
    ) -> Pin<Box<dyn Future<Output = Result<Vec<Vec<f32>>>> + Send + 'a>>;
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
        Self { api_key, model, http: reqwest::Client::new() }
    }
}

impl EmbeddingProvider for VoyageBackend {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
    ) -> Pin<Box<dyn Future<Output = Result<Vec<Vec<f32>>>> + Send + 'a>> {
        Box::pin(async move {
            let body = serde_json::json!({
                "input": texts,
                "model": self.model,
                "input_type": "document"
            });
            let resp: serde_json::Value = self.http
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
        Self { api_key, model, http: reqwest::Client::new() }
    }
}

impl EmbeddingProvider for OpenAiBackend {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
    ) -> Pin<Box<dyn Future<Output = Result<Vec<Vec<f32>>>> + Send + 'a>> {
        Box::pin(async move {
            let body = serde_json::json!({
                "input": texts,
                "model": self.model
            });
            let resp: serde_json::Value = self.http
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
// Local (fastembed + ONNX Runtime)
// ---------------------------------------------------------------------------

const LOCAL_MODEL: EmbeddingModel = EmbeddingModel::BGEBaseENV15;
pub const LOCAL_DIM: usize = 768;

pub struct LocalBackend {
    // Outer Mutex serialises first-time init (only one thread calls try_new,
    // which may download ~120 MB on first use). Inner Arc<Mutex<>> is shared
    // across embed() calls after init.
    model: Mutex<Option<Arc<Mutex<TextEmbedding>>>>,
    batch_size: Option<usize>,
    cache_dir: Option<PathBuf>,
}

impl LocalBackend {
    fn new(batch_size: usize, cache_dir: Option<String>) -> Self {
        let batch_size = if batch_size == 0 { None } else { Some(batch_size) };
        let cache_dir = cache_dir.and_then(|p| {
            let t = p.trim().to_string();
            if t.is_empty() { None } else { Some(PathBuf::from(t)) }
        });
        Self { model: Mutex::new(None), batch_size, cache_dir }
    }

    fn init_model(&self) -> Result<Arc<Mutex<TextEmbedding>>> {
        let mut guard = self.model
            .lock()
            .map_err(|_| anyhow::anyhow!("local model init mutex poisoned"))?;
        if let Some(ref m) = *guard {
            return Ok(Arc::clone(m));
        }
        let show_progress = std::env::var("MIMIR_LOCAL_SHOW_PROGRESS")
            .map(|v| !v.eq_ignore_ascii_case("false") && v != "0")
            .unwrap_or(true);
        tracing::info!(
            "initialising local embedding model (BGE-Base-EN-v1.5, 768 dims){}",
            if show_progress { " — downloading on first use, please wait" } else { "" }
        );
        let mut options = InitOptions::new(LOCAL_MODEL)
            .with_show_download_progress(show_progress);
        if let Some(ref dir) = self.cache_dir {
            options = options.with_cache_dir(dir.clone());
        }
        let model = Arc::new(Mutex::new(TextEmbedding::try_new(options)?));
        *guard = Some(Arc::clone(&model));
        Ok(model)
    }
}

impl EmbeddingProvider for LocalBackend {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
    ) -> Pin<Box<dyn Future<Output = Result<Vec<Vec<f32>>>> + Send + 'a>> {
        let texts = texts.to_vec();
        let batch_size = self.batch_size;
        Box::pin(async move {
            if texts.is_empty() {
                return Ok(vec![]);
            }
            let model = self.init_model()?;
            tokio::task::spawn_blocking(move || {
                let mut guard = model
                    .lock()
                    .map_err(|_| anyhow::anyhow!("local embedder mutex poisoned"))?;
                guard.embed(&texts, batch_size).map_err(anyhow::Error::from)
            })
            .await
            .map_err(|e| anyhow::anyhow!("local embeddings task failed: {}", e))?
        })
    }
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
        EmbeddingBackend::Local => Box::new(LocalBackend::new(
            cfg.batch_size,
            cfg.cache_dir.clone(),
        )),
    }
}

// ---------------------------------------------------------------------------
// Vector literal for pgvector SQL interpolation.
// Produces `[f1,f2,...]` — safe to string-interpolate since f32::to_string
// only produces digits, dots, `-`, `e`, `inf`, `nan` (no SQL metacharacters).
// ---------------------------------------------------------------------------

pub fn vec_literal(v: &[f32]) -> String {
    let inner: Vec<String> = v.iter().map(|f| f.to_string()).collect();
    format!("[{}]", inner.join(","))
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
