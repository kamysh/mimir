//! Stateless provider transports. The host, never the provider, executes MCP tools.
use super::{
    config::{Backend as Kind, LlmConfig, Provider},
    runner::{Action, Backend},
    state::SourceFailure,
};
use anyhow::{anyhow, bail, ensure, Result};
use mimir_core::learning::ExperienceState;
use reqwest::{header::HeaderValue, Client, StatusCode};
use serde_json::{json, Value};
use std::collections::{HashSet, VecDeque};
use std::future::Future;
use std::pin::Pin;
use std::time::Duration;
use uuid::Uuid;

const MAX_REQUEST: usize = 2 * 1024 * 1024;
const MAX_RESPONSE: usize = 8 * 1024 * 1024;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Wire {
    OpenAi,
    Anthropic,
    Chat,
}

struct Call {
    id: String,
    name: String,
    arguments: std::result::Result<Value, SourceFailure>,
}

impl Call {
    fn into_action(self) -> Action {
        match self.arguments {
            Ok(arguments) => Action::Tool {
                name: self.name,
                arguments,
            },
            Err(source) => Action::RejectedTool {
                name: self.name,
                source,
            },
        }
    }
}

pub struct ApiBackend<'a> {
    config: &'a LlmConfig,
    wire: Wire,
    url: String,
    client: Client,
    selected_id: Option<Uuid>,
    history: Vec<Value>,
    pending: VecDeque<Call>,
    awaiting: Option<String>,
    results: Vec<Value>,
}

impl<'a> ApiBackend<'a> {
    pub fn new(config: &'a LlmConfig) -> Result<Option<Self>> {
        if config.backend != Kind::Api {
            bail!("API backend requires llm.backend=api");
        }
        let (wire, default_base, endpoint) = match config.provider {
            Some(Provider::Openai) => (Wire::OpenAi, "https://api.openai.com/v1", "responses"),
            Some(Provider::Anthropic) => {
                (Wire::Anthropic, "https://api.anthropic.com/v1", "messages")
            }
            Some(Provider::Openrouter) => (
                Wire::Chat,
                "https://openrouter.ai/api/v1",
                "chat/completions",
            ),
            Some(Provider::Deepseek) => {
                (Wire::Chat, "https://api.deepseek.com", "chat/completions")
            }
            Some(Provider::Zai) => (
                Wire::Chat,
                "https://api.z.ai/api/paas/v4",
                "chat/completions",
            ),
            Some(Provider::Gemini) => (
                Wire::Chat,
                "https://generativelanguage.googleapis.com/v1beta/openai",
                "chat/completions",
            ),
            Some(Provider::OpenaiCompatible) => (Wire::Chat, "", "chat/completions"),
            None => return Ok(None),
        };
        ensure!(
            config.provider != Some(Provider::OpenaiCompatible) || config.base_url.is_some(),
            "llm.base_url is required for openai-compatible"
        );
        ensure!(
            config.provider != Some(Provider::Openrouter)
                || !matches!(config.model.as_str(), "auto" | "openrouter/auto"),
            "OpenRouter requires a specific model"
        );
        let base = config.base_url.as_deref().unwrap_or(default_base);
        let url = format!("{}/{}", base.trim_end_matches('/'), endpoint);
        let client = Client::builder()
            .redirect(reqwest::redirect::Policy::none())
            .connect_timeout(Duration::from_secs(5))
            .timeout(Duration::from_secs(config.timeout_seconds))
            .build()
            .map_err(|_| anyhow!("unable to initialize API transport"))?;
        Ok(Some(Self {
            config,
            wire,
            url,
            client,
            selected_id: None,
            history: Vec::new(),
            pending: VecDeque::new(),
            awaiting: None,
            results: Vec::new(),
        }))
    }

    fn reset(&mut self, selected: &ExperienceState) -> Result<()> {
        if self.selected_id == Some(selected.experience.id) {
            return Ok(());
        }
        self.selected_id = Some(selected.experience.id);
        self.pending.clear();
        self.awaiting = None;
        self.results.clear();
        let content = serde_json::to_string(selected)?;
        self.history = match self.wire {
            Wire::OpenAi => vec![json!({"role":"user","content":content})],
            Wire::Anthropic => {
                vec![json!({"role":"user","content":[{"type":"text","text":content}]})]
            }
            Wire::Chat => vec![
                json!({"role":"system","content":Self::instructions(selected)}),
                json!({"role":"user","content":content}),
            ],
        };
        Ok(())
    }

    fn instructions(selected: &ExperienceState) -> String {
        format!(
            "Review only this pinned experience. Use the supplied functions for evidence and review; never claim database completion in text. {} The host enforces project {}, experience {}, source revision {}, and review revision {}. Stop after the review is submitted.",
            super::review_guidance(),
            selected.experience.project,
            selected.experience.id,
            selected.revision,
            selected.review_revision
        )
    }

    fn definitions(&self, tools: &[Value]) -> Result<Vec<Value>> {
        tools
            .iter()
            .map(|tool| {
                let name = tool["name"]
                    .as_str()
                    .ok_or_else(|| anyhow!("invalid MCP tool definition"))?;
                let schema = tool["inputSchema"]
                    .as_object()
                    .ok_or_else(|| anyhow!("invalid MCP tool schema"))?;
                let description = tool["description"].as_str().unwrap_or("");
                Ok(match self.wire {
                    Wire::OpenAi => json!({"type":"function","name":name,
                        "description":description,"parameters":schema,"strict":false}),
                    Wire::Anthropic => json!({"name":name,"description":description,
                        "input_schema":schema}),
                    Wire::Chat => json!({"type":"function","function":{"name":name,
                        "description":description,"parameters":schema}}),
                })
            })
            .collect()
    }

    fn flush_results(&mut self) -> Result<()> {
        if self.results.is_empty() {
            return Ok(());
        }
        match self.wire {
            Wire::OpenAi | Wire::Chat => self.history.append(&mut self.results),
            Wire::Anthropic => {
                self.history
                    .push(json!({"role":"user","content":self.results}));
                self.results.clear();
            }
        }
        Ok(())
    }

    fn request(&self, selected: &ExperienceState, tools: &[Value]) -> Result<Value> {
        let definitions = self.definitions(tools)?;
        let request = match self.wire {
            Wire::OpenAi => json!({
                "model":self.config.model,
                "instructions":Self::instructions(selected),
                "input":self.history,
                "tools":definitions,
                "parallel_tool_calls":true,
                "store":false,
                "max_output_tokens":self.config.max_output_tokens,
                "truncation":"disabled"
            }),
            Wire::Anthropic => json!({
                "model":self.config.model,
                "system":Self::instructions(selected),
                "messages":self.history,
                "tools":definitions,
                "max_tokens":self.config.max_output_tokens
            }),
            Wire::Chat => {
                let mut request = json!({"model":self.config.model,"messages":self.history,
                    "tools":definitions,"max_tokens":self.config.max_output_tokens,"stream":false});
                if self.config.provider == Some(Provider::Openrouter) {
                    request["provider"] =
                        json!({"allow_fallbacks":false,"require_parameters":true});
                }
                request
            }
        };
        // The caller serializes once, so the cap includes replayed reasoning.
        ensure!(
            serde_json::to_vec(&request)?.len() <= MAX_REQUEST,
            "API context exceeded limit"
        );
        Ok(request)
    }

    async fn send(&self, request: Value) -> Result<Value> {
        let key = self
            .config
            .api_key
            .as_deref()
            .ok_or_else(|| anyhow!("missing API key"))?;
        let mut builder = self.client.post(&self.url).json(&request);
        builder = match self.wire {
            Wire::OpenAi | Wire::Chat => builder.bearer_auth(key),
            Wire::Anthropic => {
                let header =
                    HeaderValue::from_str(key).map_err(|_| anyhow!("invalid API key header"))?;
                builder
                    .header("x-api-key", header)
                    .header("anthropic-version", "2023-06-01")
            }
        };
        let mut response = builder.send().await.map_err(|error| {
            if error.is_timeout() {
                anyhow!("provider request timed out")
            } else {
                anyhow!("provider transport failed")
            }
        })?;
        let status = response.status();
        let mut bytes = Vec::new();
        while let Some(chunk) = response
            .chunk()
            .await
            .map_err(|_| anyhow!("provider body failed"))?
        {
            ensure!(
                bytes.len() + chunk.len() <= MAX_RESPONSE,
                "provider response exceeded limit"
            );
            bytes.extend_from_slice(&chunk);
        }
        if !status.is_success() {
            bail!("{}", classify_error(status, &bytes));
        }
        serde_json::from_slice(&bytes)
            .map_err(|error| SourceFailure::json("invalid provider JSON", &bytes, error).into())
    }

    fn parse_openai(&mut self, reply: &Value) -> Result<()> {
        ensure!(
            reply["status"] == "completed",
            "OpenAI response is incomplete"
        );
        if let Some(usage) = reply["usage"]["output_tokens"].as_u64() {
            ensure!(
                usage <= self.config.max_output_tokens as u64,
                "OpenAI output exceeded token limit"
            );
        }
        let output = reply["output"]
            .as_array()
            .ok_or_else(|| anyhow!("invalid OpenAI output"))?;
        let mut seen = HashSet::new();
        let mut calls = VecDeque::new();
        for item in output {
            ensure!(
                item["status"].is_null() || item["status"] == "completed",
                "incomplete OpenAI output item"
            );
            match item["type"].as_str() {
                Some("function_call") => {
                    let id = item["call_id"]
                        .as_str()
                        .ok_or_else(|| anyhow!("missing OpenAI call ID"))?;
                    let name = item["name"]
                        .as_str()
                        .ok_or_else(|| anyhow!("missing OpenAI function name"))?;
                    let arguments = match item["arguments"].as_str() {
                        Some(encoded) => serde_json::from_str(encoded).map_err(|error| {
                            SourceFailure::json(
                                "invalid OpenAI function arguments",
                                encoded.as_bytes(),
                                error,
                            )
                        }),
                        None => Err(SourceFailure::input(
                            "invalid OpenAI function arguments",
                            item["arguments"].to_string().as_bytes(),
                            "function arguments must be JSON text",
                        )),
                    };
                    ensure!(
                        !id.is_empty() && id.len() <= 128 && seen.insert(id),
                        "invalid OpenAI function call"
                    );
                    calls.push_back(Call {
                        id: id.into(),
                        name: name.into(),
                        arguments,
                    });
                }
                Some("reasoning" | "message") => {}
                _ => bail!("unexpected OpenAI output item"),
            }
        }
        ensure!(
            calls.len() <= self.config.max_calls,
            "too many OpenAI calls"
        );
        // Replay the complete output, including encrypted reasoning items.
        self.history.extend(output.iter().cloned());
        self.pending = calls;
        Ok(())
    }

    fn parse_anthropic(&mut self, reply: &Value) -> Result<()> {
        if let Some(usage) = reply["usage"]["output_tokens"].as_u64() {
            ensure!(
                usage <= self.config.max_output_tokens as u64,
                "Anthropic output exceeded token limit"
            );
        }
        let content = reply["content"]
            .as_array()
            .ok_or_else(|| anyhow!("invalid Anthropic content"))?;
        let mut seen = HashSet::new();
        let mut calls = VecDeque::new();
        for block in content {
            match block["type"].as_str() {
                Some("tool_use") => {
                    let id = block["id"]
                        .as_str()
                        .ok_or_else(|| anyhow!("missing Anthropic tool ID"))?;
                    let name = block["name"]
                        .as_str()
                        .ok_or_else(|| anyhow!("missing Anthropic tool name"))?;
                    let arguments = block["input"].clone();
                    ensure!(
                        !id.is_empty() && id.len() <= 128 && seen.insert(id),
                        "invalid Anthropic tool call"
                    );
                    let arguments = if arguments.is_object() {
                        Ok(arguments)
                    } else {
                        Err(SourceFailure::input(
                            "invalid Anthropic tool arguments",
                            arguments.to_string().as_bytes(),
                            "tool input must be a JSON object",
                        ))
                    };
                    calls.push_back(Call {
                        id: id.into(),
                        name: name.into(),
                        arguments,
                    });
                }
                Some("thinking") => {
                    ensure!(
                        block["thinking"].is_string() && block["signature"].is_string(),
                        "invalid Anthropic thinking block"
                    );
                }
                Some("redacted_thinking") => {
                    ensure!(
                        block["data"].is_string(),
                        "invalid Anthropic reasoning block"
                    );
                }
                Some("text") => {}
                _ => bail!("unexpected Anthropic content block"),
            }
        }
        match reply["stop_reason"].as_str() {
            Some("tool_use") => ensure!(!calls.is_empty(), "Anthropic tool stop without calls"),
            Some("end_turn") => ensure!(calls.is_empty(), "Anthropic calls without tool stop"),
            _ => bail!("Anthropic response is incomplete"),
        }
        ensure!(
            calls.len() <= self.config.max_calls,
            "too many Anthropic calls"
        );
        // Preserve thinking/signatures and their original order verbatim.
        self.history
            .push(json!({"role":"assistant","content":content}));
        self.pending = calls;
        Ok(())
    }

    fn parse_chat(&mut self, reply: &Value) -> Result<()> {
        if let Some(usage) = reply["usage"]["completion_tokens"].as_u64() {
            ensure!(
                usage <= self.config.max_output_tokens as u64,
                "provider output exceeded token limit"
            );
        }
        let choices = reply["choices"]
            .as_array()
            .ok_or_else(|| anyhow!("invalid chat choices"))?;
        ensure!(choices.len() == 1, "invalid chat choice count");
        let choice = &choices[0];
        let message = &choice["message"];
        ensure!(
            message["role"] == "assistant" && message.is_object(),
            "invalid chat assistant message"
        );
        let raw_calls = match message.get("tool_calls") {
            None | Some(Value::Null) => &[][..],
            Some(Value::Array(calls)) => calls.as_slice(),
            _ => bail!("invalid chat tool calls"),
        };
        match choice["finish_reason"].as_str() {
            Some("tool_calls") => ensure!(!raw_calls.is_empty(), "chat tool stop without calls"),
            Some("stop") => ensure!(raw_calls.is_empty(), "chat calls without tool stop"),
            _ => bail!("chat response is incomplete"),
        }
        ensure!(
            raw_calls.len() <= self.config.max_calls,
            "too many chat calls"
        );
        let mut seen = HashSet::new();
        let mut calls = VecDeque::new();
        for call in raw_calls {
            let id = call["id"]
                .as_str()
                .ok_or_else(|| anyhow!("missing chat call ID"))?;
            let name = call["function"]["name"]
                .as_str()
                .ok_or_else(|| anyhow!("missing chat function name"))?;
            ensure!(
                call["type"] == "function"
                    && !id.is_empty()
                    && id.len() <= 128
                    && seen.insert(id)
                    && !name.is_empty(),
                "invalid chat function call"
            );
            let arguments = match &call["function"]["arguments"] {
                Value::String(encoded) => serde_json::from_str(encoded).map_err(|error| {
                    SourceFailure::json(
                        "invalid chat function arguments",
                        encoded.as_bytes(),
                        error,
                    )
                }),
                Value::Object(object) if self.config.provider == Some(Provider::Zai) => {
                    Ok(Value::Object(object.clone()))
                }
                other => Err(SourceFailure::input(
                    "invalid chat function arguments",
                    other.to_string().as_bytes(),
                    "function arguments must be JSON text",
                )),
            };
            calls.push_back(Call {
                id: id.into(),
                name: name.into(),
                arguments,
            });
        }
        // Retain reasoning_content and Gemini's thought signature in their
        // original assistant message. Send every parallel tool result after it.
        self.history.push(message.clone());
        self.pending = calls;
        Ok(())
    }

    async fn step(
        &mut self,
        selected: &ExperienceState,
        last: Option<&Value>,
        tools: &[Value],
    ) -> Result<Action> {
        self.reset(selected)?;
        match (self.awaiting.take(), last) {
            (Some(id), Some(result)) => {
                let content = serde_json::to_string(result)?;
                self.results.push(match self.wire {
                    Wire::OpenAi => {
                        json!({"type":"function_call_output","call_id":id,"output":content})
                    }
                    Wire::Anthropic => {
                        json!({"type":"tool_result","tool_use_id":id,"content":content})
                    }
                    Wire::Chat => json!({"role":"tool","tool_call_id":id,"content":content}),
                });
            }
            (None, None) => {}
            _ => bail!("provider tool result sequence is invalid"),
        }
        if let Some(call) = self.pending.pop_front() {
            self.awaiting = Some(call.id.clone());
            return Ok(call.into_action());
        }
        self.flush_results()?;
        let request = self.request(selected, tools)?;
        let reply = self.send(request).await?;
        match self.wire {
            Wire::OpenAi => self.parse_openai(&reply)?,
            Wire::Anthropic => self.parse_anthropic(&reply)?,
            Wire::Chat => self.parse_chat(&reply)?,
        }
        if let Some(call) = self.pending.pop_front() {
            self.awaiting = Some(call.id.clone());
            Ok(call.into_action())
        } else {
            Ok(Action::Done)
        }
    }
}

impl Backend for ApiBackend<'_> {
    fn will_call_model(&self, selected: &ExperienceState) -> bool {
        self.selected_id != Some(selected.experience.id) || self.pending.is_empty()
    }

    fn next<'a>(
        &'a mut self,
        selected: &'a ExperienceState,
        last: Option<&'a Value>,
        tools: &'a [Value],
    ) -> Pin<Box<dyn Future<Output = Result<Action>> + Send + 'a>> {
        Box::pin(self.step(selected, last, tools))
    }
}

fn classify_error(status: StatusCode, bytes: &[u8]) -> &'static str {
    let code = serde_json::from_slice::<Value>(bytes)
        .ok()
        .and_then(|v| v["error"]["code"].as_str().map(str::to_owned));
    match status.as_u16() {
        401 | 403 => "provider authentication failed",
        402 => "provider quota exhausted",
        429 if code.as_deref() == Some("insufficient_quota") => "provider quota exhausted",
        429 => "provider rate limit reached",
        400 | 404 | 422 if code.as_deref().is_some_and(|c| c.contains("model")) => {
            "provider model is unsupported"
        }
        400 | 404 | 422
            if code.as_deref().is_some_and(|c| {
                c.contains("tool") || c.contains("function") || c.contains("unsupported_parameter")
            }) =>
        {
            "provider model or requested tools are unsupported"
        }
        400 | 404 | 422 => "provider rejected request",
        408 | 504 => "provider request timed out",
        500..=599 => "provider service failed",
        _ => "provider request failed",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mimir_core::learning::{Experience, ObservationSource, Outcome};
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    use tokio::net::TcpListener;

    struct Captured {
        path: String,
        headers: String,
        body: Value,
    }

    async fn fixture(
        replies: Vec<(u16, Value)>,
    ) -> (String, tokio::task::JoinHandle<Vec<Captured>>) {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let url = format!("http://{}/v1", listener.local_addr().unwrap());
        let task = tokio::spawn(async move {
            let mut captured = Vec::new();
            for (status, body) in replies {
                let (mut socket, _) = listener.accept().await.unwrap();
                let mut bytes = Vec::new();
                let mut chunk = [0u8; 4096];
                let boundary = loop {
                    let read = socket.read(&mut chunk).await.unwrap();
                    assert!(read > 0 && bytes.len() + read < MAX_REQUEST);
                    bytes.extend_from_slice(&chunk[..read]);
                    if let Some(index) = bytes.windows(4).position(|part| part == b"\r\n\r\n") {
                        break index + 4;
                    }
                };
                let headers = String::from_utf8(bytes[..boundary].to_vec()).unwrap();
                let length: usize = headers
                    .lines()
                    .find_map(|line| {
                        line.to_ascii_lowercase()
                            .strip_prefix("content-length: ")
                            .and_then(|value| value.trim().parse().ok())
                    })
                    .unwrap();
                while bytes.len() - boundary < length {
                    let read = socket.read(&mut chunk).await.unwrap();
                    assert!(read > 0 && bytes.len() + read < MAX_REQUEST);
                    bytes.extend_from_slice(&chunk[..read]);
                }
                let path = headers.split_whitespace().nth(1).unwrap().to_owned();
                captured.push(Captured {
                    path,
                    headers,
                    body: serde_json::from_slice(&bytes[boundary..boundary + length]).unwrap(),
                });
                let body = serde_json::to_vec(&body).unwrap();
                let response = format!(
                    "HTTP/1.1 {status} fixture\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                    body.len()
                );
                socket.write_all(response.as_bytes()).await.unwrap();
                socket.write_all(&body).await.unwrap();
            }
            captured
        });
        (url, task)
    }

    fn config(provider: Provider, base_url: String) -> LlmConfig {
        LlmConfig {
            backend: Kind::Api,
            model: "fixture-model".into(),
            reasoning_effort: None,
            timeout_seconds: 5,
            max_calls: 8,
            max_output_tokens: 256,
            max_budget_usd: None,
            provider: Some(provider),
            api_key: Some("fixture-secret".into()),
            base_url: Some(base_url),
            command: None,
            args: Vec::new(),
        }
    }

    fn selected() -> ExperienceState {
        ExperienceState {
            experience: Experience {
                id: Uuid::new_v4(),
                project: "fixture-project".into(),
                context: "test incident".into(),
                action: "inspect".into(),
                outcome: Outcome::Success,
                source: ObservationSource::ToolResult,
                evidence: vec!["local fixture".into()],
                belief_ids: Vec::new(),
                pattern_id: None,
            },
            revision: 1,
            review_revision: 0,
            reviewed_revision: 0,
            candidate_ids: Default::default(),
        }
    }

    fn tools() -> Vec<Value> {
        vec![
            json!({"name":"get_experience","description":"Read pinned experience",
            "inputSchema":{"type":"object","properties":{"id":{"type":"string"}},
            "required":["id"]}}),
        ]
    }

    #[tokio::test]
    async fn openai_replays_multiple_calls_and_encrypted_reasoning() {
        let selected = selected();
        let args = json!({"id":selected.experience.id}).to_string();
        let (url, server) = fixture(vec![
            (200, json!({"status":"completed","usage":{"output_tokens":20},"output":[
                {"type":"reasoning","id":"rs_1","summary":[],"encrypted_content":"cipher"},
                {"type":"function_call","call_id":"call_1","name":"get_experience","arguments":args},
                {"type":"function_call","call_id":"call_2","name":"get_experience","arguments":args}
            ]})),
            (200, json!({"status":"completed","usage":{"output_tokens":8},"output":[
                {"type":"message","role":"assistant","content":[{"type":"output_text","text":"done"}]}
            ]})),
        ]).await;
        let config = config(Provider::Openai, url);
        let mut backend = ApiBackend::new(&config).unwrap().unwrap();
        let tools = tools();
        assert!(matches!(
            backend.next(&selected, None, &tools).await.unwrap(),
            Action::Tool { .. }
        ));
        assert!(!backend.will_call_model(&selected));
        assert!(matches!(
            backend
                .next(&selected, Some(&json!({"one":1})), &tools)
                .await
                .unwrap(),
            Action::Tool { .. }
        ));
        assert!(backend.will_call_model(&selected));
        assert!(matches!(
            backend
                .next(&selected, Some(&json!({"two":2})), &tools)
                .await
                .unwrap(),
            Action::Done
        ));
        let requests = server.await.unwrap();
        assert_eq!(requests.len(), 2);
        assert_eq!(requests[0].path, "/v1/responses");
        assert!(
            requests[0]
                .headers
                .contains("authorization: Bearer fixture-secret")
                || requests[0]
                    .headers
                    .contains("Authorization: Bearer fixture-secret")
        );
        assert_eq!(requests[0].body["store"], false);
        assert_eq!(requests[0].body["max_output_tokens"], 256);
        assert_eq!(requests[0].body["tools"][0]["name"], "get_experience");
        assert!(requests[0].body.get("previous_response_id").is_none());
        let input = requests[1].body["input"].as_array().unwrap();
        assert!(input
            .iter()
            .any(|item| item["encrypted_content"] == "cipher"));
        assert_eq!(
            input
                .iter()
                .filter(|item| item["type"] == "function_call_output")
                .count(),
            2
        );
        assert_eq!(input[input.len() - 2]["call_id"], "call_1");
        assert_eq!(input[input.len() - 1]["call_id"], "call_2");
    }

    #[tokio::test]
    async fn anthropic_replays_signed_thinking_and_paired_results() {
        let selected = selected();
        let args = json!({"id":selected.experience.id});
        let (url, server) = fixture(vec![
            (
                200,
                json!({"stop_reason":"tool_use","usage":{"output_tokens":25},"content":[
                    {"type":"thinking","thinking":"reasoning","signature":"signed"},
                    {"type":"tool_use","id":"toolu_1","name":"get_experience","input":args},
                    {"type":"tool_use","id":"toolu_2","name":"get_experience","input":args}
                ]}),
            ),
            (
                200,
                json!({"stop_reason":"end_turn","usage":{"output_tokens":8},"content":[
                    {"type":"text","text":"done"}
                ]}),
            ),
        ])
        .await;
        let config = config(Provider::Anthropic, url);
        let mut backend = ApiBackend::new(&config).unwrap().unwrap();
        let tools = tools();
        assert!(matches!(
            backend.next(&selected, None, &tools).await.unwrap(),
            Action::Tool { .. }
        ));
        assert!(!backend.will_call_model(&selected));
        assert!(matches!(
            backend
                .next(&selected, Some(&json!({"one":1})), &tools)
                .await
                .unwrap(),
            Action::Tool { .. }
        ));
        assert!(matches!(
            backend
                .next(&selected, Some(&json!({"two":2})), &tools)
                .await
                .unwrap(),
            Action::Done
        ));
        let requests = server.await.unwrap();
        assert_eq!(requests[0].path, "/v1/messages");
        assert!(requests[0].headers.contains("x-api-key: fixture-secret"));
        assert!(requests[0]
            .headers
            .contains("anthropic-version: 2023-06-01"));
        assert_eq!(requests[0].body["max_tokens"], 256);
        let messages = requests[1].body["messages"].as_array().unwrap();
        assert_eq!(messages[1]["content"][0]["signature"], "signed");
        assert_eq!(messages[1]["content"][1]["id"], "toolu_1");
        assert_eq!(messages[2]["content"][0]["tool_use_id"], "toolu_1");
        assert_eq!(messages[2]["content"][1]["tool_use_id"], "toolu_2");
    }

    #[tokio::test]
    async fn chat_provider_fixtures_replay_parallel_calls_and_metadata() {
        for provider in [
            Provider::Openrouter,
            Provider::Deepseek,
            Provider::Zai,
            Provider::Gemini,
            Provider::OpenaiCompatible,
        ] {
            let selected = selected();
            let arguments = json!({"id":selected.experience.id});
            let wire_args = if provider == Provider::Zai {
                arguments.clone()
            } else {
                json!(arguments.to_string())
            };
            let (url, server) = fixture(vec![
                (
                    200,
                    json!({"usage":{"completion_tokens":20},"choices":[{
                    "finish_reason":"tool_calls","message":{"role":"assistant",
                    "content":null,"reasoning_content":"reasoning",
                    "tool_calls":[
                        {"id":"call_1","type":"function","function":{
                            "name":"get_experience","arguments":wire_args},
                            "extra_content":{"google":{"thought_signature":"signed"}}},
                        {"id":"call_2","type":"function","function":{
                            "name":"get_experience","arguments":wire_args}}
                    ]}}]}),
                ),
                (
                    200,
                    json!({"usage":{"completion_tokens":8},"choices":[{
                    "finish_reason":"stop","message":{"role":"assistant","content":"done"}}]}),
                ),
            ])
            .await;
            let config = config(provider, url);
            let mut backend = ApiBackend::new(&config).unwrap().unwrap();
            let tools = tools();
            assert!(matches!(
                backend.next(&selected, None, &tools).await.unwrap(),
                Action::Tool { .. }
            ));
            assert!(!backend.will_call_model(&selected));
            assert!(matches!(
                backend
                    .next(&selected, Some(&json!({"one":1})), &tools)
                    .await
                    .unwrap(),
                Action::Tool { .. }
            ));
            assert!(backend.will_call_model(&selected));
            assert!(matches!(
                backend
                    .next(&selected, Some(&json!({"two":2})), &tools)
                    .await
                    .unwrap(),
                Action::Done
            ));
            let requests = server.await.unwrap();
            assert_eq!(requests.len(), 2);
            assert_eq!(requests[0].path, "/v1/chat/completions");
            assert!(requests[0]
                .headers
                .to_ascii_lowercase()
                .contains("authorization: bearer fixture-secret"));
            assert_eq!(requests[0].body["model"], "fixture-model");
            assert_eq!(requests[0].body["max_tokens"], 256);
            assert_eq!(requests[0].body["stream"], false);
            assert_eq!(
                requests[0].body["tools"][0]["function"]["name"],
                "get_experience"
            );
            assert_eq!(requests[0].body["messages"][0]["role"], "system");
            if provider == Provider::Openrouter {
                assert_eq!(
                    requests[0].body["provider"],
                    json!({"allow_fallbacks":false,"require_parameters":true})
                );
            } else {
                assert!(requests[0].body.get("provider").is_none());
            }
            let messages = requests[1].body["messages"].as_array().unwrap();
            assert_eq!(messages[2]["reasoning_content"], "reasoning");
            assert_eq!(
                messages[2]["tool_calls"][0]["extra_content"]["google"]["thought_signature"],
                "signed"
            );
            assert_eq!(messages[3]["tool_call_id"], "call_1");
            assert_eq!(messages[4]["tool_call_id"], "call_2");
            assert_eq!(messages[3]["role"], "tool");
        }
    }

    #[test]
    fn chat_parser_rejects_incompatible_or_partial_responses() {
        let compatible = config(Provider::OpenaiCompatible, "http://127.0.0.1:1/v1".into());
        let mut backend = ApiBackend::new(&compatible).unwrap().unwrap();
        for reply in [
            json!({"choices":[{"finish_reason":"length","message":{"role":"assistant","content":"partial"}}]}),
            json!({"choices":[{"finish_reason":"tool_calls","message":{"role":"assistant","tool_calls":[]}}]}),
            json!({"choices":[{"finish_reason":"stop","message":{"role":"assistant","tool_calls":[
                {"id":"a","type":"function","function":{"name":"get_experience","arguments":"{}"}}]}}]}),
            json!({"usage":{"completion_tokens":257},"choices":[{"finish_reason":"stop",
                "message":{"role":"assistant","content":"done"}}]}),
        ] {
            assert!(backend.parse_chat(&reply).is_err());
        }
        backend
            .parse_chat(&json!({"choices":[{"finish_reason":"tool_calls",
                "message":{"role":"assistant","tool_calls":[{"id":"bad-args",
                    "type":"function","function":{"name":"get_experience",
                        "arguments":"not-json"}}]}}]}))
            .unwrap();
        let call = backend.pending.pop_front().unwrap();
        assert_eq!(call.id, "bad-args");
        assert!(matches!(call.into_action(), Action::RejectedTool { .. }));
        backend
            .parse_chat(&json!({"choices":[{"finish_reason":"tool_calls",
                "message":{"role":"assistant","tool_calls":[{"id":"wrong-type",
                    "type":"function","function":{"name":"get_experience",
                        "arguments":null}}]}}]}))
            .unwrap();
        assert!(matches!(
            backend.pending.pop_front().unwrap().into_action(),
            Action::RejectedTool { .. }
        ));
        let mut auto = config(Provider::Openrouter, "http://127.0.0.1:1/v1".into());
        auto.model = "openrouter/auto".into();
        assert!(ApiBackend::new(&auto).is_err());
    }

    #[test]
    fn anthropic_non_object_tool_input_is_recoverable() {
        let config = config(Provider::Anthropic, "http://127.0.0.1:1/v1".into());
        let mut backend = ApiBackend::new(&config).unwrap().unwrap();
        backend
            .parse_anthropic(&json!({"stop_reason":"tool_use","content":[
                {"type":"tool_use","id":"bad-input","name":"get_experience","input":42}
            ]}))
            .unwrap();
        assert!(matches!(
            backend.pending.pop_front().unwrap().into_action(),
            Action::RejectedTool { .. }
        ));
    }

    #[test]
    fn chat_provider_presets_use_documented_endpoints() {
        for (provider, endpoint) in [
            (
                Provider::Openrouter,
                "https://openrouter.ai/api/v1/chat/completions",
            ),
            (
                Provider::Deepseek,
                "https://api.deepseek.com/chat/completions",
            ),
            (
                Provider::Zai,
                "https://api.z.ai/api/paas/v4/chat/completions",
            ),
            (
                Provider::Gemini,
                "https://generativelanguage.googleapis.com/v1beta/openai/chat/completions",
            ),
        ] {
            let mut settings = config(provider, "unused".into());
            settings.base_url = None;
            assert_eq!(ApiBackend::new(&settings).unwrap().unwrap().url, endpoint);
        }
        let mut compatible = config(Provider::OpenaiCompatible, "unused".into());
        compatible.base_url = None;
        assert!(ApiBackend::new(&compatible).is_err());
    }

    #[tokio::test]
    async fn partial_and_error_responses_fail_closed() {
        let selected = selected();
        for (provider, status, reply) in [
            (
                Provider::Openai,
                200,
                json!({"status":"incomplete","output":[]}),
            ),
            (
                Provider::Anthropic,
                200,
                json!({"stop_reason":"max_tokens","content":[]}),
            ),
            (
                Provider::Openai,
                401,
                json!({"error":{"message":"secret","code":"invalid_api_key"}}),
            ),
            (
                Provider::Anthropic,
                429,
                json!({"error":{"message":"secret","code":"insufficient_quota"}}),
            ),
            (
                Provider::Openai,
                302,
                json!({"error":{"message":"redirect"}}),
            ),
        ] {
            let (url, server) = fixture(vec![(status, reply)]).await;
            let config = config(provider, url);
            let mut backend = ApiBackend::new(&config).unwrap().unwrap();
            let error = match backend.next(&selected, None, &tools()).await {
                Ok(_) => panic!("partial or failed response was accepted"),
                Err(error) => error.to_string(),
            };
            assert!(!error.contains("secret"));
            server.await.unwrap();
        }
    }

    #[test]
    fn rejects_bad_calls_usage_and_classifies_provider_errors() {
        let config = config(Provider::Openai, "http://127.0.0.1:1/v1".into());
        let mut backend = ApiBackend::new(&config).unwrap().unwrap();
        backend
            .parse_openai(&json!({"status":"completed","output":[
                {"type":"function_call","call_id":"one","name":"get_experience","arguments":"not JSON"}
            ]}))
            .unwrap();
        assert!(matches!(
            backend.pending.pop_front().unwrap().into_action(),
            Action::RejectedTool { .. }
        ));
        backend
            .parse_openai(&json!({"status":"completed","output":[
                {"type":"function_call","call_id":"two","name":"get_experience","arguments":42}
            ]}))
            .unwrap();
        assert!(matches!(
            backend.pending.pop_front().unwrap().into_action(),
            Action::RejectedTool { .. }
        ));
        assert!(backend
            .parse_openai(&json!({"status":"completed","usage":{"output_tokens":257},"output":[]}))
            .is_err());
        assert!(backend
            .parse_openai(&json!({"status":"completed","output":[
                {"type":"message","status":"incomplete","role":"assistant","content":[]}
            ]}))
            .is_err());
        assert!(backend
            .parse_openai(&json!({"status":"completed","output":[
                {"type":"function_call","call_id":"one","name":"get_experience","arguments":"{}"},
                {"type":"function_call","call_id":"one","name":"get_experience","arguments":"{}"}
            ]}))
            .is_err());
        assert_eq!(
            classify_error(StatusCode::UNAUTHORIZED, b"{}"),
            "provider authentication failed"
        );
        assert_eq!(
            classify_error(StatusCode::PAYMENT_REQUIRED, b"{}"),
            "provider quota exhausted"
        );
        assert_eq!(
            classify_error(
                StatusCode::TOO_MANY_REQUESTS,
                br#"{"error":{"code":"insufficient_quota"}}"#
            ),
            "provider quota exhausted"
        );
        assert_eq!(
            classify_error(
                StatusCode::BAD_REQUEST,
                br#"{"error":{"code":"model_not_found"}}"#
            ),
            "provider model is unsupported"
        );
        assert_eq!(
            classify_error(
                StatusCode::UNPROCESSABLE_ENTITY,
                br#"{"error":{"code":"unsupported_parameter","message":"private detail"}}"#
            ),
            "provider model or requested tools are unsupported"
        );
    }

    #[tokio::test]
    async fn timeout_and_oversized_body_are_rejected() {
        let selected = selected();
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let url = format!("http://{}/v1", listener.local_addr().unwrap());
        let stalled = tokio::spawn(async move {
            let (_socket, _) = listener.accept().await.unwrap();
            tokio::time::sleep(Duration::from_secs(2)).await;
        });
        let mut slow_config = config(Provider::Openai, url);
        slow_config.timeout_seconds = 1;
        let mut backend = ApiBackend::new(&slow_config).unwrap().unwrap();
        let error = match backend.next(&selected, None, &tools()).await {
            Ok(_) => panic!("stalled provider was accepted"),
            Err(error) => error.to_string(),
        };
        assert!(error.contains("timed out"));
        stalled.abort();

        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let url = format!("http://{}/v1", listener.local_addr().unwrap());
        let oversized = tokio::spawn(async move {
            let (mut socket, _) = listener.accept().await.unwrap();
            let mut request = [0u8; 4096];
            let _ = socket.read(&mut request).await.unwrap();
            let header = format!(
                "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                MAX_RESPONSE + 1
            );
            socket.write_all(header.as_bytes()).await.unwrap();
            let chunk = [b'x'; 8192];
            for _ in 0..=(MAX_RESPONSE / chunk.len()) {
                if socket.write_all(&chunk).await.is_err() {
                    break;
                }
            }
        });
        let config = config(Provider::Openai, url);
        let mut backend = ApiBackend::new(&config).unwrap().unwrap();
        let error = match backend.next(&selected, None, &tools()).await {
            Ok(_) => panic!("oversized provider body was accepted"),
            Err(error) => error.to_string(),
        };
        assert!(error.contains("exceeded limit"));
        oversized.await.unwrap();
    }

    #[tokio::test]
    async fn isolated_runner_requires_database_receipt_after_api_claim() {
        let Ok(path) = std::env::var("MIMIR_STEP5_TEST_CONFIG") else {
            return;
        };
        let mcp = std::env::var("MIMIR_STEP5_MCP_BIN").expect("isolated MCP binary");
        let project = format!("step7-{}", Uuid::new_v4());
        let mut settings = super::super::config::load(Some(std::path::Path::new(&path))).unwrap();
        settings.judge.project = Some(project.clone());
        settings.judge.mcp_command = mcp;
        settings.judge.batch_size = 1;
        let core = mimir_core::config::Config::load_from_path(&settings.path).unwrap();
        let service = mimir_core::MimirService::connect(&core).await.unwrap();
        let mut selected = selected();
        selected.experience.project = project.clone();
        service
            .record_experience(&selected.experience, 0)
            .await
            .unwrap();
        let state_path =
            std::path::PathBuf::from(format!("/var/tmp/mimir/step7/state-{}", Uuid::new_v4()));
        let state = super::super::state::State::lock(state_path.clone())
            .unwrap()
            .unwrap();

        let (url, server) = fixture(vec![(
            200,
            json!({"status":"completed","output":[
                {"type":"message","role":"assistant","content":[
                    {"type":"output_text","text":"I reviewed it"}
                ]}
            ]}),
        )])
        .await;
        settings.llm = config(Provider::Openai, url);
        let mut backend = ApiBackend::new(&settings.llm).unwrap().unwrap();
        let report = super::super::runner::run(&settings, &state, &mut backend).await;
        assert_eq!(report.status, "blocked");
        assert_eq!(report.confirmed, 0);
        assert_eq!(
            service
                .get_experience(selected.experience.id)
                .await
                .unwrap()
                .unwrap()
                .reviewed_revision,
            0
        );
        server.await.unwrap();

        let review = json!({"expected_review_revision":0,"review":{
            "experience_id":selected.experience.id,"experience_revision":1,
            "reviewer":"untrusted-provider","rationale":"local API fixture review"
        }});
        let (url, server) = fixture(vec![
            (
                200,
                json!({"status":"completed","output":[
                    {"type":"function_call","call_id":"call_read","name":"get_experience",
                        "arguments":json!({"id":selected.experience.id}).to_string()},
                    {"type":"function_call","call_id":"call_review","name":"review_experience",
                        "arguments":review.to_string()}
                ]}),
            ),
            (200, json!({"status":"completed","output":[]})),
        ])
        .await;
        settings.llm = config(Provider::Openai, url);
        // Two provider requests and two host tools; the queued second tool is
        // not charged as a third provider request.
        settings.llm.max_calls = 2;
        let mut backend = ApiBackend::new(&settings.llm).unwrap().unwrap();
        let report = super::super::runner::run(&settings, &state, &mut backend).await;
        assert_eq!(report.status, "complete");
        assert_eq!(report.confirmed, 1);
        assert_eq!(
            service
                .get_experience(selected.experience.id)
                .await
                .unwrap()
                .unwrap()
                .reviewed_revision,
            1
        );
        server.await.unwrap();
        service.delete_project(&project).await.unwrap();
        drop(state);
        std::fs::remove_dir_all(state_path).unwrap();
    }
}
