use anyhow::Result;
use serde_json::{json, Value};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tracing::error;

use ai_mem_core::{
    graph::EdgeType,
    AiMemService,
};

// ---------------------------------------------------------------------------
// JSON-RPC helpers
// ---------------------------------------------------------------------------

fn ok_response(id: &Value, result: Value) -> Value {
    json!({ "jsonrpc": "2.0", "id": id, "result": result })
}

fn err_response(id: &Value, code: i64, message: &str) -> Value {
    json!({
        "jsonrpc": "2.0",
        "id": id,
        "error": { "code": code, "message": message }
    })
}

// ---------------------------------------------------------------------------
// Tool list
// ---------------------------------------------------------------------------

fn tools_list() -> Value {
    json!([
        {
            "name": "add_belief",
            "description": "Add a new belief to the graph.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "content":     { "type": "string" },
                    "probability": { "type": "number", "minimum": 0.0, "maximum": 1.0 },
                    "confidence":  { "type": "number", "minimum": 0.0, "maximum": 1.0 }
                },
                "required": ["content", "probability", "confidence"]
            }
        },
        {
            "name": "add_pattern",
            "description": "Add a new pattern to the graph.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "situation":   { "type": "string" },
                    "approach":    { "type": "string" },
                    "success_rate": { "type": "number", "minimum": 0.0, "maximum": 1.0 }
                },
                "required": ["situation", "approach", "success_rate"]
            }
        },
        {
            "name": "add_edge",
            "description": "Add an edge between two beliefs.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "from_id":   { "type": "string" },
                    "to_id":     { "type": "string" },
                    "edge_type": { "type": "string", "enum": ["Supports", "Defeats", "Causes", "Contradicts"] },
                    "weight":    { "type": "number", "minimum": 0.0, "maximum": 1.0 }
                },
                "required": ["from_id", "to_id", "edge_type", "weight"]
            }
        },
        {
            "name": "get_belief",
            "description": "Get a belief by ID.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "id": { "type": "string" }
                },
                "required": ["id"]
            }
        },
        {
            "name": "list_beliefs",
            "description": "List all beliefs.",
            "inputSchema": {
                "type": "object",
                "properties": {}
            }
        },
        {
            "name": "list_patterns",
            "description": "List all patterns.",
            "inputSchema": {
                "type": "object",
                "properties": {}
            }
        },
        {
            "name": "detect_contradictions",
            "description": "Find all actively contradicting belief pairs.",
            "inputSchema": {
                "type": "object",
                "properties": {}
            }
        },
        {
            "name": "decay_beliefs",
            "description": "Apply time decay to all beliefs and return count of updated beliefs.",
            "inputSchema": {
                "type": "object",
                "properties": {}
            }
        },
        {
            "name": "query_relevant",
            "description": "Search beliefs by content substring, ordered by probability descending.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "query": { "type": "string" }
                },
                "required": ["query"]
            }
        },
        {
            "name": "propagate_from",
            "description": "Run defeat propagation from a seed belief ID.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "id": { "type": "string" }
                },
                "required": ["id"]
            }
        }
    ])
}

// ---------------------------------------------------------------------------
// Tool dispatch
// ---------------------------------------------------------------------------

async fn handle_tool_call(
    svc: &AiMemService,
    name: &str,
    args: &Value,
) -> Result<Value> {
    match name {
        "add_belief" => {
            let content = args["content"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'content'"))?;
            let probability = args["probability"]
                .as_f64()
                .ok_or_else(|| anyhow::anyhow!("missing 'probability'"))?;
            let confidence = args["confidence"]
                .as_f64()
                .ok_or_else(|| anyhow::anyhow!("missing 'confidence'"))?;
            let belief = svc.add_belief(content, probability, confidence).await?;
            Ok(serde_json::to_value(&belief)?)
        }

        "add_pattern" => {
            let situation = args["situation"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'situation'"))?;
            let approach = args["approach"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'approach'"))?;
            let success_rate = args["success_rate"]
                .as_f64()
                .ok_or_else(|| anyhow::anyhow!("missing 'success_rate'"))?;
            let pattern = svc.add_pattern(situation, approach, success_rate).await?;
            Ok(serde_json::to_value(&pattern)?)
        }

        "add_edge" => {
            let from_str = args["from_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'from_id'"))?;
            let to_str = args["to_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'to_id'"))?;
            let edge_type_str = args["edge_type"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'edge_type'"))?;
            let weight = args["weight"]
                .as_f64()
                .ok_or_else(|| anyhow::anyhow!("missing 'weight'"))?;

            let from_id = uuid::Uuid::parse_str(from_str)?;
            let to_id = uuid::Uuid::parse_str(to_str)?;
            let edge_type = parse_edge_type(edge_type_str)?;

            svc.add_edge(from_id, to_id, edge_type, weight).await?;
            Ok(json!({ "ok": true }))
        }

        "get_belief" => {
            let id_str = args["id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'id'"))?;
            let id = uuid::Uuid::parse_str(id_str)?;
            let belief = svc.get_belief(id).await?;
            Ok(serde_json::to_value(&belief)?)
        }

        "list_beliefs" => {
            let beliefs = svc.list_beliefs().await?;
            Ok(serde_json::to_value(&beliefs)?)
        }

        "list_patterns" => {
            let patterns = svc.list_patterns().await?;
            Ok(serde_json::to_value(&patterns)?)
        }

        "detect_contradictions" => {
            let pairs = svc.detect_contradictions().await?;
            let result: Vec<Value> = pairs
                .into_iter()
                .map(|(a, b)| json!([a.to_string(), b.to_string()]))
                .collect();
            Ok(json!(result))
        }

        "decay_beliefs" => {
            let count = svc.decay_beliefs().await?;
            Ok(json!({ "decayed": count }))
        }

        "query_relevant" => {
            let query = args["query"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'query'"))?;
            let beliefs = svc.query_relevant(query).await?;
            Ok(serde_json::to_value(&beliefs)?)
        }

        "propagate_from" => {
            let id_str = args["id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'id'"))?;
            let id = uuid::Uuid::parse_str(id_str)?;
            let updates = svc.propagate_from(id).await?;
            let result: Vec<Value> = updates
                .into_iter()
                .map(|(uid, prob)| {
                    json!({ "id": uid.to_string(), "new_probability": prob.value() })
                })
                .collect();
            Ok(json!(result))
        }

        other => anyhow::bail!("unknown tool: {}", other),
    }
}

fn parse_edge_type(s: &str) -> Result<EdgeType> {
    match s {
        "Supports" => Ok(EdgeType::Supports),
        "Defeats" => Ok(EdgeType::Defeats),
        "Causes" => Ok(EdgeType::Causes),
        "Contradicts" => Ok(EdgeType::Contradicts),
        other => anyhow::bail!("unknown edge_type: {}", other),
    }
}

// ---------------------------------------------------------------------------
// Main loop
// ---------------------------------------------------------------------------

#[tokio::main]
async fn main() -> Result<()> {
    // Init tracing to stderr (stdout is reserved for JSON-RPC responses).
    tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_env_filter(
            tracing_subscriber::EnvFilter::from_default_env()
                .add_directive(tracing::Level::WARN.into()),
        )
        .init();

    // Read DSN from environment.
    let dsn = match std::env::var("AI_MEM_DSN") {
        Ok(v) => v,
        Err(_) => {
            eprintln!("error: AI_MEM_DSN environment variable is not set");
            std::process::exit(1);
        }
    };

    // Connect to database.
    let svc = AiMemService::connect(&dsn).await?;

    // Async I/O on stdin/stdout.
    let stdin = tokio::io::stdin();
    let mut stdout = tokio::io::stdout();
    let mut reader = BufReader::new(stdin);
    let mut line = String::new();

    loop {
        line.clear();
        let n = reader.read_line(&mut line).await?;
        if n == 0 {
            // EOF
            break;
        }

        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        let request: Value = match serde_json::from_str(trimmed) {
            Ok(v) => v,
            Err(e) => {
                error!("parse error: {}", e);
                // No id available — use null
                let resp = err_response(&Value::Null, -32700, &format!("parse error: {e}"));
                let mut out = resp.to_string();
                out.push('\n');
                stdout.write_all(out.as_bytes()).await?;
                stdout.flush().await?;
                continue;
            }
        };

        let id = request.get("id").cloned().unwrap_or(Value::Null);
        let method = request
            .get("method")
            .and_then(|v| v.as_str())
            .unwrap_or("");
        let params = request
            .get("params")
            .cloned()
            .unwrap_or(Value::Object(serde_json::Map::new()));

        let response = match method {
            "initialize" => ok_response(
                &id,
                json!({
                    "protocolVersion": "2024-11-05",
                    "capabilities": { "tools": {} },
                    "serverInfo": { "name": "ai-mem", "version": "0.1.0" }
                }),
            ),

            "tools/list" => ok_response(&id, json!({ "tools": tools_list() })),

            "tools/call" => {
                let tool_name = params
                    .get("name")
                    .and_then(|v| v.as_str())
                    .unwrap_or("");
                let empty_obj = Value::Object(serde_json::Map::new());
                let arguments = params.get("arguments").unwrap_or(&empty_obj);

                match handle_tool_call(&svc, tool_name, arguments).await {
                    Ok(result) => ok_response(&id, json!({ "content": [{ "type": "text", "text": result.to_string() }] })),
                    Err(e) => err_response(&id, -32000, &e.to_string()),
                }
            }

            other => {
                error!("unknown method: {}", other);
                err_response(&id, -32601, "Method not found")
            }
        };

        let mut out = response.to_string();
        out.push('\n');
        stdout.write_all(out.as_bytes()).await?;
        stdout.flush().await?;
    }

    Ok(())
}