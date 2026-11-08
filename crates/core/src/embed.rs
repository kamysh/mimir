use anyhow::{Context, Result};
use std::future::Future;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use tokenizers::Tokenizer;
use tract_onnx::prelude::*;

use crate::config::{EmbeddingBackend, EmbeddingsConfig};
mod local_worker;
#[cfg(test)]
mod selection_tests;
pub use local_worker::worker_entrypoint;

// ---------------------------------------------------------------------------
// Trait
// ---------------------------------------------------------------------------

/// Boxed, sendable future returned by [`EmbeddingProvider::embed`].
pub type EmbedFuture<'a> = Pin<Box<dyn Future<Output = Result<Vec<Vec<f32>>>> + Send + 'a>>;

pub trait EmbeddingProvider: Send + Sync {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
        cancellation: EmbeddingCancellation,
    ) -> EmbedFuture<'a>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Physical job state. Finished work can return either Ok or Err; inspect its result.
pub enum EmbeddingStatus {
    Running,
    Cancelled,
    Finished,
}

#[derive(Debug)]
pub struct EmbeddingCancelled;
impl std::fmt::Display for EmbeddingCancelled {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("embedding job was cancelled; no embedding result was accepted")
    }
}
impl std::error::Error for EmbeddingCancelled {}

#[derive(Clone)]
pub struct EmbeddingCancellation {
    state: tokio::sync::watch::Receiver<EmbeddingStatus>,
}
impl EmbeddingCancellation {
    pub fn status(&self) -> EmbeddingStatus {
        *self.state.borrow()
    }
    pub fn check(&self) -> Result<()> {
        match self.status() {
            EmbeddingStatus::Running => Ok(()),
            EmbeddingStatus::Cancelled => Err(EmbeddingCancelled.into()),
            EmbeddingStatus::Finished => anyhow::bail!("embedding job has already finished"),
        }
    }
    pub async fn ended(&mut self) -> EmbeddingStatus {
        loop {
            let state = self.status();
            if state != EmbeddingStatus::Running {
                return state;
            }
            if self.state.changed().await.is_err() {
                return EmbeddingStatus::Cancelled;
            }
        }
    }
}

#[derive(Clone)]
pub struct EmbeddingStopHandle {
    state: tokio::sync::watch::Sender<EmbeddingStatus>,
}
impl EmbeddingStopHandle {
    /// Return whether this call stopped a running job. Finished results remain intact.
    pub fn cancel(&self) -> bool {
        self.state.send_if_modified(|state| {
            if *state == EmbeddingStatus::Running {
                *state = EmbeddingStatus::Cancelled;
                true
            } else {
                false
            }
        })
    }
    pub fn status(&self) -> EmbeddingStatus {
        *self.state.borrow()
    }
}

struct EmbeddingOwner {
    control: EmbeddingStopHandle,
}
impl EmbeddingOwner {
    fn finish(self) -> bool {
        self.control.state.send_if_modified(|state| {
            if *state == EmbeddingStatus::Running {
                *state = EmbeddingStatus::Finished;
                true
            } else {
                false
            }
        })
    }
}
impl Drop for EmbeddingOwner {
    fn drop(&mut self) {
        self.control.cancel();
    }
}

#[must_use = "await the embedding job or cancel it; dropping it requests cancellation"]
pub struct EmbeddingJob<'a> {
    future: EmbedFuture<'a>,
    control: EmbeddingStopHandle,
}
impl EmbeddingJob<'_> {
    pub fn stop_handle(&self) -> EmbeddingStopHandle {
        self.control.clone()
    }
}
impl Future for EmbeddingJob<'_> {
    type Output = Result<Vec<Vec<f32>>>;
    fn poll(
        self: Pin<&mut Self>,
        context: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        self.get_mut().future.as_mut().poll(context)
    }
}

/// Every service embedding request enters through this owned wrapper.
pub struct OwnedEmbeddingBackend {
    provider: Box<dyn EmbeddingProvider>,
}
impl OwnedEmbeddingBackend {
    #[cfg(test)]
    pub(crate) fn for_test(provider: Box<dyn EmbeddingProvider>) -> Self {
        Self { provider }
    }

    pub fn embed<'a>(&'a self, texts: &'a [String]) -> EmbeddingJob<'a> {
        let (state, received) = tokio::sync::watch::channel(EmbeddingStatus::Running);
        let control = EmbeddingStopHandle { state };
        let owner = EmbeddingOwner {
            control: control.clone(),
        };
        let cancellation = EmbeddingCancellation { state: received };
        let future = Box::pin(async move {
            cancellation.check()?;
            let mut ended = cancellation.clone();
            let result = tokio::select! {
                biased;
                _ = ended.ended() => return Err(EmbeddingCancelled.into()),
                result = self.provider.embed(texts, cancellation) => result,
            };
            // This transition is serialized with cancel(). A cancellation that
            // won the race cannot subsequently become an accepted result.
            if owner.finish() {
                result
            } else {
                Err(EmbeddingCancelled.into())
            }
        });
        EmbeddingJob { future, control }
    }
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

    fn request_body(&self, texts: &[String]) -> serde_json::Value {
        serde_json::json!({
            "input": texts,
            "model": self.model,
            "input_type": "document",
            "truncation": false
        })
    }
}

impl EmbeddingProvider for VoyageBackend {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
        _cancellation: EmbeddingCancellation,
    ) -> EmbedFuture<'a> {
        Box::pin(async move {
            let body = self.request_body(texts);
            let response = self
                .http
                .post("https://api.voyageai.com/v1/embeddings")
                .bearer_auth(&self.api_key)
                .json(&body)
                .send()
                .await?;
            remote_embeddings(response, texts.len(), &self.api_key).await
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
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
        _cancellation: EmbeddingCancellation,
    ) -> EmbedFuture<'a> {
        Box::pin(async move {
            let body = serde_json::json!({
                "input": texts,
                "model": self.model
            });
            let response = self
                .http
                .post("https://api.openai.com/v1/embeddings")
                .bearer_auth(&self.api_key)
                .json(&body)
                .send()
                .await?;
            remote_embeddings(response, texts.len(), &self.api_key).await
        })
    }
}

// ---------------------------------------------------------------------------
// Local (tract ONNX + HuggingFace tokenizers)
// ---------------------------------------------------------------------------

const HF_MODEL_ID: &str = "BAAI/bge-base-en-v1.5";
// BGE's declared position-table capacity, including special tokens. This
// external model requirement was explicitly approved; it never selects a
// shorter source prefix. See docs/EXTERNAL-MODEL-CONSTRAINTS.md.
const LOCAL_MAX_POSITIONS: usize = 512;
pub const LOCAL_DIM: usize = 768;

type TractPlan = SimplePlan<TypedFact, Box<dyn TypedOp>, Graph<TypedFact, Box<dyn TypedOp>>>;

async fn remote_embeddings(
    response: reqwest::Response,
    count: usize,
    api_key: &str,
) -> Result<Vec<Vec<f32>>> {
    let status = response.status();
    if !status.is_success() {
        let detail = response.text().await?;
        let detail = if api_key.is_empty() {
            detail
        } else {
            detail.replace(api_key, "[redacted API key]")
        };
        anyhow::bail!("Embedding provider returned HTTP {status}: {detail}");
    }
    let body = response.json().await?;
    parse_embeddings(&body, count)
}

struct EmbedState {
    tokenizer: Tokenizer,
    model: Mutex<TractPlan>,
}

struct LocalModel {
    state: Mutex<Option<Arc<EmbedState>>>,
    batch_size: Option<usize>,
    cache_dir: Option<PathBuf>,
}

impl LocalModel {
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
    use std::io::{Read, Write};

    if let Some(parent) = dest.parent() {
        std::fs::create_dir_all(parent)
            .with_context(|| format!("creating {}", parent.display()))?;
    }
    let name = dest
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_else(|| url.to_string());
    tracing::info!(url, dest = %dest.display(), "downloading model file");
    let client = reqwest::blocking::Client::builder()
        .timeout(None)
        .redirect(reqwest::redirect::Policy::custom(|attempt| {
            attempt.follow()
        }))
        .build()
        .context("building HTTP client")?;
    let mut resp = client
        .get(url)
        .send()
        .with_context(|| format!("GET {url}"))?
        .error_for_status()
        .with_context(|| format!("HTTP error for {url}"))?;

    let total = resp.content_length();
    let bar = match total {
        Some(len) => indicatif::ProgressBar::new(len).with_style(
            indicatif::ProgressStyle::with_template(
                "mimir: downloading {msg} {bar:40.cyan/blue} {bytes}/{total_bytes} ({bytes_per_sec}, ETA {eta})",
            )
            .unwrap(),
        ),
        None => indicatif::ProgressBar::new_spinner().with_style(
            indicatif::ProgressStyle::with_template("mimir: downloading {msg} {bytes} ({bytes_per_sec})").unwrap(),
        ),
    };
    bar.set_message(name.clone());

    // Unique per-process suffix: two mimir-mcp processes cold-starting the same
    // model concurrently must not share one .part path, or their interleaved
    // writes race and the loser's fd ends up writing into an unlinked inode
    // after the winner's rename.
    let tmp = dest.with_extension(format!("part-{}", std::process::id()));
    let mut file =
        std::fs::File::create(&tmp).with_context(|| format!("creating {}", tmp.display()))?;
    let mut buf = [0u8; 64 * 1024];
    loop {
        let n = resp
            .read(&mut buf)
            .with_context(|| format!("reading body of {url}"))?;
        if n == 0 {
            break;
        }
        file.write_all(&buf[..n])
            .with_context(|| format!("writing {}", tmp.display()))?;
        bar.inc(n as u64);
    }
    bar.finish_with_message(format!("{name} ready"));

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

    let mut tokenizer = Tokenizer::from_file(&tokenizer_path)
        .map_err(|e| anyhow::anyhow!("loading tokenizer: {e}"))?;
    configure_complete_tokenizer(&mut tokenizer)?;

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

fn configure_complete_tokenizer(tokenizer: &mut Tokenizer) -> Result<()> {
    tokenizer
        .with_truncation(None)
        .map_err(|error| anyhow::anyhow!("disabling tokenizer truncation: {error}"))?;
    tokenizer.with_padding(None);
    Ok(())
}

fn complete_sequence_length(encodings: &[tokenizers::Encoding]) -> Result<usize> {
    let mut longest = 0;
    for (index, encoding) in encodings.iter().enumerate() {
        let positions = encoding.get_ids().len();
        anyhow::ensure!(positions <= LOCAL_MAX_POSITIONS,
            "Embedding input {index} in this batch contains {positions} encoded positions, including special tokens; {HF_MODEL_ID} supports {LOCAL_MAX_POSITIONS}. No input was truncated. Open a user dialog to choose an appropriate backend or revise the input; do not split the source, change models, or invent a processing policy automatically.");
        longest = longest.max(positions);
    }
    Ok(longest)
}

#[cfg(test)]
mod complete_input_tests {
    use super::*;

    fn encoded(count: usize) -> tokenizers::Encoding {
        tokenizers::Encoding::from_tokens(
            (0..count)
                .map(|index| tokenizers::Token {
                    id: index as u32,
                    value: format!("token{index}"),
                    offsets: (index, index + 1),
                })
                .collect(),
            0,
        )
    }

    #[test]
    fn full_encodings_are_checked_without_discarding_the_last_condition() {
        let accepted = vec![encoded(3), encoded(LOCAL_MAX_POSITIONS)];
        assert_eq!(
            complete_sequence_length(&accepted).unwrap(),
            LOCAL_MAX_POSITIONS
        );
        assert_eq!(accepted[1].get_ids().last(), Some(&511));
        let oversized = vec![encoded(3), encoded(LOCAL_MAX_POSITIONS + 1)];
        let ids = oversized[1].get_ids().to_vec();
        let report = complete_sequence_length(&oversized)
            .unwrap_err()
            .to_string();
        assert!(report.contains(HF_MODEL_ID));
        assert!(report.contains("513") && report.contains("512"));
        assert!(report.contains("Open a user dialog"));
        assert_eq!(oversized[1].get_ids(), ids);
        assert_eq!(oversized[1].get_ids().last(), Some(&512));
    }

    #[test]
    fn loaded_tokenizer_settings_cannot_silently_clip_or_pad_input() {
        let mut tokenizer = Tokenizer::new(tokenizers::models::wordlevel::WordLevel::default());
        tokenizer
            .with_truncation(Some(tokenizers::TruncationParams {
                max_length: 8,
                ..Default::default()
            }))
            .unwrap();
        tokenizer.with_padding(Some(tokenizers::PaddingParams::default()));
        configure_complete_tokenizer(&mut tokenizer).unwrap();
        assert!(tokenizer.get_truncation().is_none());
        assert!(tokenizer.get_padding().is_none());
    }

    #[test]
    fn voyage_request_disables_provider_clipping_and_preserves_complete_text() {
        let backend =
            VoyageBackend::new("fixture-only-no-account".into(), "configured-model".into());
        let texts = vec![
            format!(
                "{}final important condition",
                "complete source π ".repeat(4000)
            ),
            "second complete input".into(),
        ];
        let body = backend.request_body(&texts);
        assert_eq!(body["truncation"], false);
        assert_eq!(body["input"], serde_json::json!(texts));
        assert_eq!(body["model"], "configured-model");
        assert!(body.get("max_tokens").is_none());
    }

    #[tokio::test]
    async fn provider_rejection_retains_complete_cause_without_exposing_the_key() -> Result<()> {
        use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await?;
        let address = listener.local_addr()?;
        let explanation = format!(
            "{} input has 8193 positions; configured provider accepts 8192; fixture-api-key",
            "complete provider explanation; ".repeat(400)
        );
        let body = serde_json::json!({"error":{"message":explanation}}).to_string();
        let server = tokio::spawn(async move {
            let (stream, _) = listener.accept().await?;
            let mut stream = BufReader::new(stream);
            loop {
                let mut line = String::new();
                if stream.read_line(&mut line).await? == 0 || line == "\r\n" {
                    break;
                }
            }
            stream.get_mut().write_all(format!("HTTP/1.1 400 Bad Request\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}", body.len()).as_bytes()).await?;
            stream.get_mut().shutdown().await?;
            Ok::<_, anyhow::Error>(())
        });
        let response = reqwest::Client::new()
            .get(format!("http://{address}/"))
            .send()
            .await?;
        let report = remote_embeddings(response, 1, "fixture-api-key")
            .await
            .unwrap_err()
            .to_string();
        server.await??;
        assert!(report.contains(&explanation.replace("fixture-api-key", "[redacted API key]")));
        assert!(report.contains("8193") && report.contains("8192"));
        assert!(!report.contains("fixture-api-key"));
        Ok(())
    }
}

fn embed_with_state(
    state: &EmbedState,
    texts: &[String],
    batch_size: Option<usize>,
    cancellation: &EmbeddingCancellation,
) -> Result<Vec<Vec<f32>>> {
    let chunk_size = batch_size.unwrap_or(texts.len()).max(1);
    let mut all_embeddings = Vec::with_capacity(texts.len());

    for chunk in texts.chunks(chunk_size) {
        cancellation.check()?;
        let mut encodings = state
            .tokenizer
            .encode_batch(chunk.to_vec(), true)
            .map_err(|e| anyhow::anyhow!("tokenizer encode_batch: {e}"))?;

        // Validate complete encodings before any model call. Padding extends
        // shorter inputs; it never truncates a longer one.
        let seq_len = complete_sequence_length(&encodings)?;
        let batch = chunk.len();

        let mut input_ids = vec![0i64; batch * seq_len];
        let mut attention_mask = vec![0i64; batch * seq_len];
        let mut token_type_ids = vec![0i64; batch * seq_len];

        for (b, enc) in encodings.iter_mut().enumerate() {
            let ids = enc.get_ids();
            let masks = enc.get_attention_mask();
            let types = enc.get_type_ids();
            let len = ids.len();
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

        let model = state
            .model
            .lock()
            .map_err(|_| anyhow::anyhow!("model mutex poisoned"))?;
        cancellation.check()?;
        let outputs = model
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

pub fn make_backend(cfg: &EmbeddingsConfig) -> OwnedEmbeddingBackend {
    let provider: Box<dyn EmbeddingProvider> = match cfg.backend {
        EmbeddingBackend::Voyage => Box::new(VoyageBackend::new(
            cfg.api_key.clone().unwrap_or_default(),
            cfg.model.clone(),
        )),
        EmbeddingBackend::OpenAi => Box::new(OpenAiBackend::new(
            cfg.api_key.clone().unwrap_or_default(),
            cfg.model.clone(),
        )),
        EmbeddingBackend::Local => Box::new(local_worker::LocalBackend::new(
            cfg.batch_size,
            cfg.cache_dir.clone(),
            None,
        )),
    };
    OwnedEmbeddingBackend { provider }
}

/// For SDK hosts that do not implement `worker_entrypoint`, name a compatible
/// Mimir executable explicitly. No installed executable is selected implicitly.
pub fn make_backend_with_worker(
    cfg: &EmbeddingsConfig,
    executable: PathBuf,
) -> OwnedEmbeddingBackend {
    if matches!(cfg.backend, EmbeddingBackend::Local) {
        OwnedEmbeddingBackend {
            provider: Box::new(local_worker::LocalBackend::new(
                cfg.batch_size,
                cfg.cache_dir.clone(),
                Some(executable),
            )),
        }
    } else {
        make_backend(cfg)
    }
}

#[cfg(test)]
mod ownership_tests {
    use super::*;
    use std::{collections::VecDeque, future::poll_fn, task::Poll};
    use tokio::sync::oneshot;

    type Vectors = Vec<Vec<f32>>;
    type Control = (
        oneshot::Sender<EmbeddingCancellation>,
        oneshot::Receiver<Vectors>,
    );
    type Observer = (
        oneshot::Receiver<EmbeddingCancellation>,
        oneshot::Sender<Vectors>,
    );
    struct ControlledProvider {
        calls: Mutex<VecDeque<Control>>,
    }
    impl EmbeddingProvider for ControlledProvider {
        fn embed<'a>(
            &'a self,
            _texts: &'a [String],
            cancellation: EmbeddingCancellation,
        ) -> EmbedFuture<'a> {
            Box::pin(async move {
                let (entered, release) = self.calls.lock().unwrap().pop_front().unwrap();
                assert!(entered.send(cancellation.clone()).is_ok());
                let result = release.await?;
                cancellation.check()?;
                Ok(result)
            })
        }
    }

    fn controlled(count: usize) -> (OwnedEmbeddingBackend, Vec<Observer>) {
        let mut calls = VecDeque::new();
        let mut observers = Vec::new();
        for _ in 0..count {
            let (entered, observed) = oneshot::channel();
            let (release, result) = oneshot::channel();
            calls.push_back((entered, result));
            observers.push((observed, release));
        }
        (
            OwnedEmbeddingBackend {
                provider: Box::new(ControlledProvider {
                    calls: Mutex::new(calls),
                }),
            },
            observers,
        )
    }

    #[tokio::test]
    async fn dropping_a_job_notifies_its_cooperative_work() {
        let (backend, mut observers) = controlled(1);
        let (entered, _release) = observers.remove(0);
        let texts = vec!["owned input".into()];
        let mut job = Box::pin(backend.embed(&texts));
        assert!(poll_fn(|cx| Poll::Ready(job.as_mut().poll(cx).is_pending())).await);
        let mut cancellation = entered.await.unwrap();
        let control = job.stop_handle();
        let observed = tokio::spawn(async move { cancellation.ended().await });
        drop(job);
        assert_eq!(observed.await.unwrap(), EmbeddingStatus::Cancelled);
        assert_eq!(control.status(), EmbeddingStatus::Cancelled);
    }

    #[tokio::test]
    async fn cancellation_is_per_call_and_completion_releases_the_other_owner() {
        let (backend, mut observers) = controlled(2);
        let (entered_first, _release_first) = observers.remove(0);
        let (entered_second, release_second) = observers.remove(0);
        let texts = vec!["owned input".into()];
        let mut first = Box::pin(backend.embed(&texts));
        let mut second = Box::pin(backend.embed(&texts));
        assert!(poll_fn(|cx| Poll::Ready(first.as_mut().poll(cx).is_pending())).await);
        assert!(poll_fn(|cx| Poll::Ready(second.as_mut().poll(cx).is_pending())).await);
        let mut first_signal = entered_first.await.unwrap();
        let mut second_signal = entered_second.await.unwrap();
        let first_control = first.stop_handle();
        let second_control = second.stop_handle();
        assert!(first_control.cancel());
        assert!(first.await.unwrap_err().is::<EmbeddingCancelled>());
        assert_eq!(first_signal.ended().await, EmbeddingStatus::Cancelled);
        assert_eq!(second_control.status(), EmbeddingStatus::Running);
        release_second.send(vec![vec![1.0]]).unwrap();
        assert_eq!(second.await.unwrap(), vec![vec![1.0]]);
        assert_eq!(second_signal.ended().await, EmbeddingStatus::Finished);
        assert!(!second_control.cancel());
        assert_eq!(second_control.status(), EmbeddingStatus::Finished);
    }

    #[tokio::test]
    async fn cancellation_before_poll_never_starts_the_provider() {
        let (backend, mut observers) = controlled(1);
        let (mut entered, _release) = observers.remove(0);
        let texts = vec!["owned input".into()];
        let job = backend.embed(&texts);
        assert!(job.stop_handle().cancel());
        assert!(!job.stop_handle().cancel());
        assert!(job.await.unwrap_err().is::<EmbeddingCancelled>());
        assert!(matches!(
            entered.try_recv(),
            Err(oneshot::error::TryRecvError::Empty)
        ));
    }

    #[tokio::test]
    async fn cancellation_wins_before_an_already_ready_result_is_accepted() {
        let (backend, mut observers) = controlled(1);
        let (entered, release) = observers.remove(0);
        let texts = vec!["owned input".into()];
        let mut job = Box::pin(backend.embed(&texts));
        assert!(poll_fn(|cx| Poll::Ready(job.as_mut().poll(cx).is_pending())).await);
        let mut signal = entered.await.unwrap();
        release.send(vec![vec![1.0]]).unwrap();
        assert!(job.stop_handle().cancel());
        assert!(job.await.unwrap_err().is::<EmbeddingCancelled>());
        assert_eq!(signal.ended().await, EmbeddingStatus::Cancelled);
    }

    #[tokio::test]
    async fn a_provider_error_also_releases_ownership() {
        let (backend, mut observers) = controlled(1);
        let (entered, release) = observers.remove(0);
        let texts = vec!["owned input".into()];
        let job = backend.embed(&texts);
        let control = job.stop_handle();
        drop(release);
        let error = job.await.unwrap_err();
        assert!(!error.is::<EmbeddingCancelled>());
        let mut signal = entered.await.unwrap();
        assert_eq!(signal.ended().await, EmbeddingStatus::Finished);
        assert_eq!(control.status(), EmbeddingStatus::Finished);
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn parse_embeddings(resp: &serde_json::Value, count: usize) -> Result<Vec<Vec<f32>>> {
    let data = resp["data"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("missing 'data' array in embedding response"))?;
    anyhow::ensure!(
        data.len() == count,
        "embedding response count does not match input"
    );
    let mut vectors = vec![None; count];
    let mut dimension = None;
    for item in data {
        let index = item["index"]
            .as_u64()
            .and_then(|n| usize::try_from(n).ok())
            .ok_or_else(|| anyhow::anyhow!("invalid embedding response index"))?;
        anyhow::ensure!(index < count, "embedding response index is outside input");
        anyhow::ensure!(
            vectors[index].is_none(),
            "duplicate embedding response index"
        );
        let values = item["embedding"]
            .as_array()
            .ok_or_else(|| anyhow::anyhow!("missing 'embedding' in data item"))?;
        match dimension {
            None => dimension = Some(values.len()),
            Some(expected) => anyhow::ensure!(
                values.len() == expected,
                "inconsistent embedding dimensions"
            ),
        }
        vectors[index] = Some(
            values
                .iter()
                .map(|value| {
                    value
                        .as_f64()
                        .map(|number| number as f32)
                        .ok_or_else(|| anyhow::anyhow!("non-numeric value in embedding"))
                })
                .collect::<Result<Vec<_>>>()?,
        );
    }
    vectors
        .into_iter()
        .map(|vector| vector.ok_or_else(|| anyhow::anyhow!("missing embedding response index")))
        .collect()
}

#[cfg(test)]
mod response_tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn provider_order_does_not_change_input_association() {
        let response =
            json!({"data":[{"index":1,"embedding":[3.0,4.0]}, {"index":0,"embedding":[1.0,2.0]}]});
        assert_eq!(
            parse_embeddings(&response, 2).unwrap(),
            vec![vec![1.0, 2.0], vec![3.0, 4.0]]
        );
        assert!(parse_embeddings(&json!({"data":[]}), 0).unwrap().is_empty());
    }

    #[test]
    fn malformed_associations_are_rejected_without_truncation() {
        for data in [
            json!([]),
            json!([{"index":0,"embedding":[1.0]}]),
            json!([{"index":0,"embedding":[1.0]},{"index":0,"embedding":[2.0]}]),
            json!([{"index":0,"embedding":[1.0]},{"index":2,"embedding":[2.0]}]),
            json!([{"index":0,"embedding":[1.0]},{"index":1,"embedding":[2.0,3.0]}]),
            json!([{"index":0,"embedding":[1.0]},{"embedding":[2.0]}]),
            json!([{"index":0,"embedding":[1.0]},{"index":-1,"embedding":[2.0]}]),
            json!([{"index":0,"embedding":[1.0]},{"index":1,"embedding":["invalid"]}]),
        ] {
            assert!(parse_embeddings(&json!({"data":data}), 2).is_err());
        }
    }
}

#[cfg(test)]
mod download_tests {
    use super::*;
    use std::io::{BufRead, BufReader, Write};
    use std::net::TcpListener;
    use std::sync::mpsc;

    enum Event {
        BodyReady,
        Finished(Result<()>),
    }

    #[test]
    fn download_follows_the_complete_chain_and_waits_for_explicit_body_release() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let address = listener.local_addr().unwrap();
        let root = std::env::temp_dir().join(format!(
            "mimir-download-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&root).unwrap();
        let dest = root.join("model.fixture");
        let (events, observed) = mpsc::channel();
        let (release, body_release) = mpsc::channel();
        let server_events = events.clone();
        let server = std::thread::spawn(move || {
            for hop in 0..=12 {
                let (mut stream, _) = listener.accept().unwrap();
                let mut request = BufReader::new(stream.try_clone().unwrap());
                let mut line = String::new();
                request.read_line(&mut line).unwrap();
                assert!(line.starts_with(&format!("GET /{hop} ")));
                loop {
                    line.clear();
                    request.read_line(&mut line).unwrap();
                    if line == "\r\n" {
                        break;
                    }
                }
                if hop < 12 {
                    write!(stream,"HTTP/1.1 302 Found\r\nLocation: /{}\r\nContent-Length: 0\r\nConnection: close\r\n\r\n",hop + 1).unwrap();
                } else {
                    write!(
                        stream,
                        "HTTP/1.1 200 OK\r\nContent-Length: 8\r\nConnection: close\r\n\r\n"
                    )
                    .unwrap();
                    stream.flush().unwrap();
                    server_events.send(Event::BodyReady).unwrap();
                    body_release.recv().unwrap();
                    stream.write_all(b"complete").unwrap();
                }
            }
        });
        let output = dest.clone();
        let client = std::thread::spawn(move || {
            events
                .send(Event::Finished(download_blocking(
                    &format!("http://{address}/0"),
                    &output,
                )))
                .unwrap();
        });
        match observed.recv().unwrap() {
            Event::BodyReady => (),
            Event::Finished(result) => {
                panic!("download stopped before its response was released: {result:?}")
            }
        }
        assert!(matches!(
            observed.try_recv(),
            Err(mpsc::TryRecvError::Empty)
        ));
        release.send(()).unwrap();
        match observed.recv().unwrap() {
            Event::Finished(result) => result.unwrap(),
            Event::BodyReady => panic!("duplicate response release"),
        }
        client.join().unwrap();
        server.join().unwrap();
        assert_eq!(std::fs::read(&dest).unwrap(), b"complete");
        std::fs::remove_dir_all(root).unwrap();
    }
}
