use anyhow::{bail, Result};

use crate::config::{EmbeddingBackend, EmbeddingsConfig};

// ---------------------------------------------------------------------------
// EmbeddingClient — wraps voyage / openai / local embedding APIs.
// ---------------------------------------------------------------------------

pub struct EmbeddingClient {
    http: reqwest::Client,
    cfg: EmbeddingsConfig,
}

impl EmbeddingClient {
    pub fn new(cfg: EmbeddingsConfig) -> Result<Self> {
        let http = reqwest::Client::builder().build()?;
        Ok(Self { http, cfg })
    }

    /// Embed a single text string.
    pub async fn embed(&self, text: &str) -> Result<Vec<f32>> {
        let mut batch = self.embed_batch(&[text]).await?;
        batch.pop().ok_or_else(|| anyhow::anyhow!("empty embedding response"))
    }

    /// Embed multiple texts in one API round-trip.
    pub async fn embed_batch(&self, texts: &[&str]) -> Result<Vec<Vec<f32>>> {
        match self.cfg.backend {
            EmbeddingBackend::Voyage => self.embed_voyage(texts).await,
            EmbeddingBackend::OpenAi => self.embed_openai(texts).await,
            EmbeddingBackend::Local => bail!("local embedding backend not yet implemented"),
        }
    }

    async fn embed_voyage(&self, texts: &[&str]) -> Result<Vec<Vec<f32>>> {
        let body = serde_json::json!({
            "input": texts,
            "model": self.cfg.model,
        });
        let resp = self
            .http
            .post("https://api.voyageai.com/v1/embeddings")
            .bearer_auth(&self.cfg.api_key)
            .json(&body)
            .send()
            .await?;
        if !resp.status().is_success() {
            let status = resp.status();
            let msg = resp.text().await.unwrap_or_default();
            bail!("voyage API {}: {}", status, msg);
        }
        parse_data_embeddings(&resp.json::<serde_json::Value>().await?)
    }

    async fn embed_openai(&self, texts: &[&str]) -> Result<Vec<Vec<f32>>> {
        let input = if texts.len() == 1 {
            serde_json::json!(texts[0])
        } else {
            serde_json::json!(texts)
        };
        let body = serde_json::json!({
            "input": input,
            "model": self.cfg.model,
        });
        let resp = self
            .http
            .post("https://api.openai.com/v1/embeddings")
            .bearer_auth(&self.cfg.api_key)
            .json(&body)
            .send()
            .await?;
        if !resp.status().is_success() {
            let status = resp.status();
            let msg = resp.text().await.unwrap_or_default();
            bail!("openai API {}: {}", status, msg);
        }
        parse_data_embeddings(&resp.json::<serde_json::Value>().await?)
    }
}

fn parse_data_embeddings(json: &serde_json::Value) -> Result<Vec<Vec<f32>>> {
    let data = json["data"]
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

// ---------------------------------------------------------------------------
// Vector literal for pgvector SQL interpolation.
// Produces `[f1,f2,...]` — safe to string-interpolate since f32::to_string
// only produces digits, dots, `-`, `e`, `inf`, `nan` (no SQL metacharacters).
// ---------------------------------------------------------------------------

pub fn vec_literal(v: &[f32]) -> String {
    let inner: Vec<String> = v.iter().map(|f| f.to_string()).collect();
    format!("[{}]", inner.join(","))
}
