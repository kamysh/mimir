use anyhow::Result;
use serde_json::{json, Value};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tracing::error;

use mimir_core::{
    config::Config,
    graph::{EdgeType, MemoryType},
    MimirService,
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
            "name": "insert_belief",
            "description": "Add a new belief to the graph.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "content":     { "type": "string" },
                    "probability": { "type": "number", "minimum": 0.0, "maximum": 1.0 },
                    "confidence":  { "type": "number", "minimum": 0.0, "maximum": 1.0 },
                    "project":     { "type": "string", "description": "Optional project scope. Beliefs in a project can be bulk-deleted with delete_project when the project is done." },
                    "memory_type": { "type": "string", "enum": ["fact", "experiential", "working"], "description": "Functional memory type. 'fact' (default): declarative knowledge that decays over time absent reinforcement. 'experiential': a hard-won working lesson (gotcha, corrected approach) — exempt from time-decay, since its truth doesn't erode with elapsed time. 'working': task-local scratch memory, excluded from cross-session query_relevant retrieval." }
                },
                "required": ["content", "probability", "confidence"]
            }
        },
        {
            "name": "delete_belief",
            "description": "Delete a belief and all its edges by ID. Returns {\"deleted\": true} if found, {\"deleted\": false} if not found.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "id": { "type": "string" }
                },
                "required": ["id"]
            }
        },
        {
            "name": "delete_project",
            "description": "Delete all beliefs tagged with a project name, along with their edges. Use this to forget project-specific knowledge when a project is complete.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "project": { "type": "string" }
                },
                "required": ["project"]
            }
        },
        {
            "name": "delete_pattern",
            "description": "Delete a pattern and all its edges by ID. Returns {\"deleted\": true} if found, {\"deleted\": false} if not found.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "id": { "type": "string" }
                },
                "required": ["id"]
            }
        },
        {
            "name": "insert_pattern",
            "description": "Add a new pattern to the graph.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "situation":    { "type": "string" },
                    "approach":     { "type": "string" },
                    "success_rate": { "type": "number", "minimum": 0.0, "maximum": 1.0 }
                },
                "required": ["situation", "approach", "success_rate"]
            }
        },
        {
            "name": "record_support",
            "description": "Add a SUPPORTS edge from one belief to another.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "from_id": { "type": "string" },
                    "to_id":   { "type": "string" },
                    "weight":  { "type": "number", "minimum": 0.0, "maximum": 1.0 }
                },
                "required": ["from_id", "to_id", "weight"]
            }
        },
        {
            "name": "record_cause",
            "description": "Add a CAUSES edge from one belief to another (from_id causes to_id). Causal edges are what query_intervention traverses for counterfactual do(...) queries; unlike record_defeat this does NOT trigger propagation.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "from_id": { "type": "string" },
                    "to_id":   { "type": "string" },
                    "weight":  { "type": "number", "minimum": 0.0, "maximum": 1.0 }
                },
                "required": ["from_id", "to_id", "weight"]
            }
        },
        {
            "name": "record_defeat",
            "description": "Add a DEFEATS edge and trigger defeat propagation cascade.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "from_id": { "type": "string" },
                    "to_id":   { "type": "string" },
                    "weight":  { "type": "number", "minimum": 0.0, "maximum": 1.0 }
                },
                "required": ["from_id", "to_id", "weight"]
            }
        },
        {
            "name": "record_contradiction",
            "description": "Add a bidirectional CONTRADICTS relationship between two beliefs.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "id_a":   { "type": "string" },
                    "id_b":   { "type": "string" },
                    "weight": { "type": "number", "minimum": 0.0, "maximum": 1.0, "default": 1.0 }
                },
                "required": ["id_a", "id_b"]
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
            "description": "List beliefs. If project is given, restricts to that project's beliefs plus untagged (global) beliefs; omit to list everything.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "project": { "type": "string", "description": "Restrict to this project's beliefs plus untagged (global) beliefs. Omit to list everything." },
                    "memory_type": { "type": "string", "enum": ["fact", "experiential", "working"], "description": "Restrict to this memory type. Useful for orphan cleanup of leftover Working beliefs from an interrupted prior session — NOT a substitute for tracking the IDs of Working beliefs your own session wrote, since this filter has no session-identity concept and cannot distinguish your in-flight Working beliefs from a concurrent session's on a shared DB." }
                }
            }
        },
        {
            "name": "list_patterns",
            "description": "List patterns. If project is given, restricts to that project's patterns plus untagged (global) patterns; omit to list everything.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "project": { "type": "string", "description": "Restrict to this project's patterns plus untagged (global) patterns. Omit to list everything." }
                }
            }
        },
        {
            "name": "get_contradictions",
            "description": "Find all actively contradicting belief pairs. If project is given, restricts to pairs where both beliefs are visible in that project's scope (tagged with project or untagged).",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "project": { "type": "string", "description": "Only consider pairs where both beliefs are tagged with this project or untagged (global). Omit to consider every pair." }
                }
            }
        },
        {
            "name": "decay_all",
            "description": "Apply time decay to beliefs and return count of updated beliefs. If project is given, restricts the sweep to that project's beliefs plus untagged (global) beliefs.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "decay_factor": { "type": "number", "minimum": 0.0, "maximum": 1.0, "default": 0.99 },
                    "project": { "type": "string", "description": "Restrict the decay sweep to this project's beliefs plus untagged (global) beliefs. Omit to decay everything." }
                }
            }
        },
        {
            "name": "sweep_expired_defeated",
            "description": "Delete defeated beliefs whose grace period has elapsed (attenuated deletion — a defeated belief is deleted only once its probability has decayed below prob_threshold AND grace_hours have passed since it was last defeated, giving a wrong record_defeat call time to be caught and reversed first). Returns count of beliefs deleted. If project is given, restricts the sweep to that project's beliefs plus untagged (global) beliefs.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "prob_threshold": { "type": "number", "minimum": 0.0, "maximum": 1.0, "default": 0.3, "description": "Probability below which a defeated belief becomes eligible for deletion." },
                    "grace_hours": { "type": "number", "minimum": 0.0, "default": 24.0, "description": "Hours since the belief was last defeated before it can be deleted." },
                    "project": { "type": "string", "description": "Restrict the sweep to this project's beliefs plus untagged (global) beliefs. Omit to sweep everything." }
                }
            }
        },
        {
            "name": "query_relevant",
            "description": "Hybrid retrieval: text match + graph-proximity expansion, ordered by probability. Set include_evidence=true to also return, per belief, the document passages that ground it (with weights). If project is given, restricts the candidate pool to that project's beliefs plus untagged (global) beliefs.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "context":          { "type": "string" },
                    "limit":            { "type": "integer", "minimum": 0, "default": 10 },
                    "include_evidence":   { "type": "boolean", "default": false },
                    "evidence_per_belief":{ "type": "integer", "minimum": 0, "default": 3 },
                    "project":          { "type": "string", "description": "Restrict the candidate pool to this project's beliefs plus untagged (global) beliefs. Omit to search everything." }
                },
                "required": ["context"]
            }
        },
        {
            "name": "add_evidence",
            "description": "Ground a belief in a document passage: create a GROUNDS edge from a DocumentChunk to a Belief. Read-only w.r.t. belief inference — purely provenance. Get chunk_id from query_document results.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "belief_id": { "type": "string" },
                    "chunk_id":  { "type": "string" },
                    "weight":    { "type": "number", "minimum": 0.0, "maximum": 1.0, "default": 1.0 }
                },
                "required": ["belief_id", "chunk_id"]
            }
        },
        {
            "name": "get_evidence",
            "description": "Return the document passages grounding a belief (its GROUNDS edges), strongest first.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "belief_id": { "type": "string" }
                },
                "required": ["belief_id"]
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
        },
        {
            "name": "query_intervention",
            "description": "Counterfactual query P(downstream | do(target = value)). Severs the target's incoming edges and propagates along CAUSES edges only. READ-ONLY: returns projected probabilities for causal descendants; does NOT modify the graph. Use for 'if I change X, what downstream is affected?' — distinct from query_relevant (evidential association) and propagate_from (which mutates).",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "id":    { "type": "string" },
                    "value": { "type": "number", "minimum": 0.0, "maximum": 1.0 }
                },
                "required": ["id", "value"]
            }
        },
        {
            "name": "load_document",
            "description": "Parse a markdown file into heading-bounded chunks, embed each chunk, and index them for semantic search. Replaces existing chunks for the same path on reload. Requires [embeddings] in config.toml.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "path":    { "type": "string", "description": "Absolute or repo-relative path to the markdown file." },
                    "project": { "type": "string", "description": "Optional project tag. Chunks tagged with a project can be bulk-deleted via delete_project." }
                },
                "required": ["path"]
            }
        },
        {
            "name": "query_document",
            "description": "Semantic search over indexed document chunks. Embeds the query context and returns the most similar chunks ordered by cosine similarity. Requires [embeddings] in config.toml.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "context": { "type": "string", "description": "Query text to embed and search." },
                    "project": { "type": "string", "description": "Restrict search to chunks tagged with this project." },
                    "limit":   { "type": "integer", "minimum": 0, "default": 5, "description": "Maximum results (0 = no limit)." }
                },
                "required": ["context"]
            }
        },
        {
            "name": "clear_document",
            "description": "Remove all chunks and embeddings for a given document path. Returns {\"cleared\": N}. No-op if the path was never loaded.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "path": { "type": "string" }
                },
                "required": ["path"]
            }
        }
    ])
}

// ---------------------------------------------------------------------------
// Tool dispatch
// ---------------------------------------------------------------------------

async fn handle_tool_call(svc: &MimirService, name: &str, args: &Value) -> Result<Value> {
    match name {
        "insert_belief" => {
            let content = args["content"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'content'"))?;
            let probability = args["probability"]
                .as_f64()
                .ok_or_else(|| anyhow::anyhow!("missing 'probability'"))?;
            let confidence = args["confidence"]
                .as_f64()
                .ok_or_else(|| anyhow::anyhow!("missing 'confidence'"))?;
            let memory_type = match args["memory_type"].as_str() {
                Some(s) => s
                    .parse::<MemoryType>()
                    .map_err(|e| anyhow::anyhow!("invalid 'memory_type': {e}"))?,
                None => MemoryType::default(),
            };
            let belief = match args["project"].as_str() {
                Some(project) => {
                    svc.add_belief_in_project(
                        content,
                        probability,
                        confidence,
                        project,
                        memory_type,
                    )
                    .await?
                }
                None => {
                    svc.add_belief(content, probability, confidence, memory_type)
                        .await?
                }
            };
            Ok(serde_json::to_value(&belief)?)
        }

        "delete_belief" => {
            let id_str = args["id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'id'"))?;
            let id = uuid::Uuid::parse_str(id_str)?;
            let deleted = svc.delete_belief(id).await?;
            Ok(json!({ "deleted": deleted }))
        }

        "delete_project" => {
            let project = args["project"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'project'"))?;
            let count = svc.delete_project(project).await?;
            Ok(json!({ "deleted": count }))
        }

        "delete_pattern" => {
            let id_str = args["id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'id'"))?;
            let id = uuid::Uuid::parse_str(id_str)?;
            let deleted = svc.delete_pattern(id).await?;
            Ok(json!({ "deleted": deleted }))
        }

        "insert_pattern" => {
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

        "record_support" => {
            let from_str = args["from_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'from_id'"))?;
            let to_str = args["to_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'to_id'"))?;
            let weight = args["weight"]
                .as_f64()
                .ok_or_else(|| anyhow::anyhow!("missing 'weight'"))?;

            let from_id = uuid::Uuid::parse_str(from_str)?;
            let to_id = uuid::Uuid::parse_str(to_str)?;
            svc.add_edge(from_id, to_id, EdgeType::Supports, weight)
                .await?;
            Ok(json!({ "ok": true }))
        }

        "record_cause" => {
            let from_str = args["from_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'from_id'"))?;
            let to_str = args["to_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'to_id'"))?;
            let weight = args["weight"]
                .as_f64()
                .ok_or_else(|| anyhow::anyhow!("missing 'weight'"))?;

            let from_id = uuid::Uuid::parse_str(from_str)?;
            let to_id = uuid::Uuid::parse_str(to_str)?;
            svc.add_edge(from_id, to_id, EdgeType::Causes, weight)
                .await?;
            Ok(json!({ "ok": true }))
        }

        "record_defeat" => {
            let from_str = args["from_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'from_id'"))?;
            let to_str = args["to_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'to_id'"))?;
            let weight = args["weight"]
                .as_f64()
                .ok_or_else(|| anyhow::anyhow!("missing 'weight'"))?;

            let from_id = uuid::Uuid::parse_str(from_str)?;
            let to_id = uuid::Uuid::parse_str(to_str)?;
            // Propagation happens automatically inside add_edge for EdgeType::Defeats
            svc.add_edge(from_id, to_id, EdgeType::Defeats, weight)
                .await?;
            Ok(json!({ "ok": true }))
        }

        "record_contradiction" => {
            let id_a_str = args["id_a"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'id_a'"))?;
            let id_b_str = args["id_b"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'id_b'"))?;
            let weight = args["weight"].as_f64().unwrap_or(1.0);

            let id_a = uuid::Uuid::parse_str(id_a_str)?;
            let id_b = uuid::Uuid::parse_str(id_b_str)?;
            svc.add_edge(id_a, id_b, EdgeType::Contradicts, weight)
                .await?;
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
            let project = args["project"].as_str();
            let memory_type = match args["memory_type"].as_str() {
                Some(s) => Some(
                    s.parse::<MemoryType>()
                        .map_err(|e| anyhow::anyhow!("invalid 'memory_type': {e}"))?,
                ),
                None => None,
            };
            let beliefs = svc.list_beliefs_filtered(project, memory_type).await?;
            Ok(serde_json::to_value(&beliefs)?)
        }

        "list_patterns" => {
            let project = args["project"].as_str();
            let patterns = svc.list_patterns(project).await?;
            Ok(serde_json::to_value(&patterns)?)
        }

        "get_contradictions" => {
            let project = args["project"].as_str();
            let pairs = svc.get_contradictions(project).await?;
            let result: Vec<Value> = pairs
                .into_iter()
                .map(|(a, b)| json!([a.to_string(), b.to_string()]))
                .collect();
            Ok(json!(result))
        }

        "decay_all" => {
            let decay_factor = args["decay_factor"].as_f64();
            let project = args["project"].as_str();
            let count = svc.decay_beliefs(decay_factor, project).await?;
            Ok(json!({ "decayed": count }))
        }

        "sweep_expired_defeated" => {
            let prob_threshold = args["prob_threshold"].as_f64().unwrap_or(0.3);
            let grace_hours = args["grace_hours"].as_f64().unwrap_or(24.0);
            let project = args["project"].as_str();
            let count = svc
                .sweep_expired_defeated(prob_threshold, grace_hours, project)
                .await?;
            Ok(json!({ "deleted": count }))
        }

        "query_relevant" => {
            let query = args["context"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'context'"))?;
            let limit = args["limit"].as_u64().unwrap_or(10) as usize;
            let include_evidence = args["include_evidence"].as_bool().unwrap_or(false);
            let project = args["project"].as_str();
            if !include_evidence {
                let beliefs = svc.query_relevant(query, limit, project).await?;
                return Ok(serde_json::to_value(&beliefs)?);
            }
            let per = args["evidence_per_belief"].as_u64().unwrap_or(3) as usize;
            let grounded = svc
                .query_relevant_grounded(query, limit, per, project)
                .await?;
            let result: Vec<Value> = grounded
                .into_iter()
                .map(|gb| {
                    let mut belief_json = serde_json::to_value(&gb.belief).unwrap_or(json!({}));
                    let evidence: Vec<Value> = gb
                        .evidence
                        .into_iter()
                        .map(|e| {
                            json!({
                                "chunk_id":      e.chunk_id.to_string(),
                                "document_path": e.document_path,
                                "section_path":  e.section_path,
                                "snippet":       e.snippet,
                                "weight":        e.weight,
                            })
                        })
                        .collect();
                    if let Value::Object(ref mut map) = belief_json {
                        map.insert("evidence".to_string(), json!(evidence));
                    }
                    belief_json
                })
                .collect();
            Ok(json!(result))
        }

        "add_evidence" => {
            let belief_str = args["belief_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'belief_id'"))?;
            let chunk_str = args["chunk_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'chunk_id'"))?;
            let weight = args["weight"].as_f64().unwrap_or(1.0);
            let belief_id = uuid::Uuid::parse_str(belief_str)?;
            let chunk_id = uuid::Uuid::parse_str(chunk_str)?;
            svc.add_evidence(belief_id, chunk_id, weight).await?;
            Ok(json!({ "ok": true }))
        }

        "get_evidence" => {
            let belief_str = args["belief_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'belief_id'"))?;
            let belief_id = uuid::Uuid::parse_str(belief_str)?;
            // query_relevant_grounded with a degenerate query would re-rank; instead
            // pull evidence directly for this one belief via the grounded path on an
            // exact id is overkill — use the store accessor through a tiny helper.
            let grounded = svc.evidence_for_belief(belief_id, 0).await?;
            let result: Vec<Value> = grounded
                .into_iter()
                .map(|e| {
                    json!({
                        "chunk_id":      e.chunk_id.to_string(),
                        "document_path": e.document_path,
                        "section_path":  e.section_path,
                        "snippet":       e.snippet,
                        "weight":        e.weight,
                    })
                })
                .collect();
            Ok(json!(result))
        }

        "propagate_from" => {
            let id_str = args["id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'id'"))?;
            let id = uuid::Uuid::parse_str(id_str)?;
            let updates = svc.propagate_from(id).await?;
            let result: Vec<Value> = updates
                .into_iter()
                .map(
                    |(uid, prob)| json!({ "id": uid.to_string(), "new_probability": prob.value() }),
                )
                .collect();
            Ok(json!(result))
        }

        "query_intervention" => {
            let id_str = args["id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'id'"))?;
            let value = args["value"]
                .as_f64()
                .ok_or_else(|| anyhow::anyhow!("missing 'value'"))?;
            let id = uuid::Uuid::parse_str(id_str)?;
            let updates = svc.query_intervention(id, value).await?;
            let result: Vec<Value> = updates
                .into_iter()
                .map(|(uid, prob)| {
                    json!({ "id": uid.to_string(), "projected_probability": prob.value() })
                })
                .collect();
            Ok(json!(result))
        }

        "load_document" => {
            let path = args["path"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'path'"))?;
            let project = args["project"].as_str();
            let count = svc.load_document(path, project).await?;
            Ok(json!({ "loaded": count }))
        }

        "query_document" => {
            let context = args["context"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'context'"))?;
            let project = args["project"].as_str();
            let limit = args["limit"].as_u64().unwrap_or(5) as usize;
            let results = svc.query_document(context, project, limit).await?;
            Ok(serde_json::to_value(&results)?)
        }

        "clear_document" => {
            let path = args["path"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'path'"))?;
            let count = svc.clear_document(path).await?;
            Ok(json!({ "cleared": count }))
        }

        other => anyhow::bail!("unknown tool: {}", other),
    }
}

// ---------------------------------------------------------------------------
// Main loop
// ---------------------------------------------------------------------------

#[tokio::main]
async fn main() -> Result<()> {
    // Handle --version / -V before any I/O or DB work, mirroring the CLI's clap
    // `--version` so both binaries answer the same way.
    if std::env::args()
        .skip(1)
        .any(|a| a == "--version" || a == "-V")
    {
        println!("mimir-mcp {}", env!("CARGO_PKG_VERSION"));
        return Ok(());
    }

    // Init tracing to stderr (stdout is reserved for JSON-RPC responses).
    tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_env_filter(
            tracing_subscriber::EnvFilter::from_default_env()
                .add_directive(tracing::Level::WARN.into()),
        )
        .init();

    // Read config from ~/.config/mimir/config.toml.
    let cfg = match Config::load() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    // Connect to database (and embedding client if configured).
    let svc = MimirService::connect(&cfg).await?;

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

        let is_notification = request.get("id").is_none();
        let id = request.get("id").cloned().unwrap_or(Value::Null);
        let method = request.get("method").and_then(|v| v.as_str()).unwrap_or("");
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
                    "serverInfo": { "name": "mimir", "version": env!("CARGO_PKG_VERSION") }
                }),
            ),

            "tools/list" => ok_response(&id, json!({ "tools": tools_list() })),

            "tools/call" => {
                let tool_name = params.get("name").and_then(|v| v.as_str()).unwrap_or("");
                let empty_obj = Value::Object(serde_json::Map::new());
                let arguments = params.get("arguments").unwrap_or(&empty_obj);

                match handle_tool_call(&svc, tool_name, arguments).await {
                    Ok(result) => ok_response(
                        &id,
                        json!({ "content": [{ "type": "text", "text": result.to_string() }] }),
                    ),
                    Err(e) => err_response(&id, -32000, &e.to_string()),
                }
            }

            other => {
                error!("unknown method: {}", other);
                err_response(&id, -32601, "Method not found")
            }
        };

        if !is_notification {
            let mut out = response.to_string();
            out.push('\n');
            stdout.write_all(out.as_bytes()).await?;
            stdout.flush().await?;
        }
    }

    Ok(())
}
