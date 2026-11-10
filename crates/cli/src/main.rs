use anyhow::{Context, Result};
use clap::{Parser, Subcommand};

use mimir_core::{config::Config, MimirService};
mod configuration;
mod corrections;
mod judge;

// ---------------------------------------------------------------------------
// CLI definition
// ---------------------------------------------------------------------------

/// Mimir belief-graph manager.
#[derive(Parser)]
#[command(name = "mimir", version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[cfg(test)]
mod sweep_policy_tests {
    use super::*;
    #[test]
    fn retention_has_no_per_call_flag() {
        assert!(Cli::try_parse_from(["mimir", "sweep-defeated"]).is_ok());
        assert!(Cli::try_parse_from(["mimir", "sweep-defeated", "--grace-hours", "0"]).is_err());
    }
    #[test]
    fn threshold_is_a_finite_probability_before_connecting() {
        for value in ["0", "0.3", "1"] {
            assert!(Cli::try_parse_from(["mimir", "sweep-defeated", "--threshold", value]).is_ok());
        }
        for value in ["NaN", "inf", "2", "-0.1"] {
            assert!(Cli::try_parse_from([
                "mimir",
                "sweep-defeated",
                &format!("--threshold={value}")
            ])
            .is_err());
        }
    }
}

fn probability_argument(raw: &str) -> std::result::Result<f64, String> {
    let value = raw
        .parse::<f64>()
        .map_err(|_| "Supply a finite probability between 0 and 1 inclusive.".to_owned())?;
    if value.is_finite() && (0.0..=1.0).contains(&value) {
        Ok(value)
    } else {
        Err("Supply a finite probability between 0 and 1 inclusive; do not clamp or guess a replacement.".into())
    }
}

#[cfg(test)]
mod selection_tests {
    use super::*;
    use clap::CommandFactory;

    #[test]
    fn result_selection_is_optional_positive_and_has_no_default() {
        let command = Cli::command();
        for name in ["list", "patterns", "query"] {
            let option = command
                .find_subcommand(name)
                .unwrap()
                .get_arguments()
                .find(|arg| arg.get_id() == "limit")
                .unwrap();
            assert!(!option.is_required_set());
            assert!(option.get_default_values().is_empty());
        }
        let option = command
            .find_subcommand("doc")
            .unwrap()
            .find_subcommand("query")
            .unwrap()
            .get_arguments()
            .find(|arg| arg.get_id() == "limit")
            .unwrap();
        assert!(!option.is_required_set());
        assert!(option.get_default_values().is_empty());
        for arguments in [
            vec!["mimir", "list"],
            vec!["mimir", "patterns"],
            vec!["mimir", "query", "needle"],
            vec!["mimir", "doc", "query", "needle"],
        ] {
            assert!(Cli::try_parse_from(arguments.clone()).is_ok());
            let mut invalid = arguments;
            invalid.extend(["--limit", "0"]);
            assert!(Cli::try_parse_from(invalid).is_err());
        }
    }
}

#[derive(Subcommand)]
enum Command {
    /// Check compatibility or upgrade an existing configuration offline.
    #[command(subcommand)]
    Config(configuration::Command),
    /// Configure and run the bounded learning judge.
    #[command(subcommand)]
    Judge(judge::JudgeCommand),

    /// Create a configuration file.
    ///
    /// With no arguments: writes a commented template to
    /// ~/.config/mimir/config.toml (or $XDG_CONFIG_HOME/mimir/config.toml) and
    /// opens the existing config (or creates a template) in $EDITOR.
    /// With KEY=VALUE arguments: writes a config built
    /// from those overrides non-interactively (no $EDITOR). Recognised keys:
    /// host, port, dbname, user, password, pgpassfile, ssl_mode, ssl_root_cert, ssl_client_cert,
    /// ssl_client_key, backend, model, api_key, cache_dir.
    /// An existing valid config is left unchanged when the explicit overrides
    /// already match. Conflicting overrides ask for a decision. With no
    /// arguments, an existing config is preserved and reported as an error.
    Init {
        /// KEY=VALUE pairs (e.g. `host=localhost port=5450 backend=local`).
        /// Omit to get the interactive $EDITOR flow.
        #[arg(value_parser = parse_kv)]
        pairs: Vec<(String, String)>,
    },

    /// Print a summary of the belief graph (vertex and edge counts).
    Stats,

    /// List beliefs, optionally filtered by project.
    List {
        /// Show beliefs tagged with this project, plus untagged (global) beliefs.
        #[arg(long, short)]
        project: Option<String>,

        /// Positive result count; omit for all matching records.
        #[arg(long, short)]
        limit: Option<std::num::NonZeroUsize>,
    },

    /// List patterns.
    Patterns {
        /// Show patterns tagged with this project, plus untagged (global) patterns.
        #[arg(long, short)]
        project: Option<String>,

        /// Positive result count; omit for all matching records.
        #[arg(long, short)]
        limit: Option<std::num::NonZeroUsize>,
    },

    /// Hybrid search: text match plus graph expansion via SUPPORTS/CAUSES edges.
    Query {
        /// Search text (case-insensitive substring match).
        text: String,

        /// Positive result count; omit for all matching records.
        #[arg(long, short)]
        limit: Option<std::num::NonZeroUsize>,

        /// Also show the document passages that ground each belief.
        #[arg(long)]
        evidence: bool,

        /// Restrict the candidate pool to this project plus untagged beliefs.
        #[arg(long, short)]
        project: Option<String>,

        /// Nudge ranking toward this memory type (fact/experiential/working) —
        /// a soft preference, not a filter. Omit for the default, type-neutral
        /// ranking.
        #[arg(long)]
        prefer_type: Option<mimir_core::graph::MemoryType>,
    },

    /// Manage evidence (document passages that ground a belief).
    #[command(subcommand)]
    Evidence(EvidenceCmd),

    /// Delete a belief or pattern by UUID.
    #[command(subcommand)]
    Delete(DeleteCmd),

    /// Delete all beliefs tagged with a project.
    Forget {
        /// Project name whose beliefs should be deleted.
        project: String,
    },

    /// Apply time-decay to all belief confidences.
    Decay {
        /// Decay factor per day (default 0.99 ≈ 1% per day).
        #[arg(long, short, default_value_t = 0.99)]
        factor: f64,

        /// Restrict the decay sweep to this project plus untagged beliefs.
        #[arg(long, short)]
        project: Option<String>,
    },

    /// List active contradictions in the graph.
    Contradictions {
        /// Only consider pairs where both beliefs are visible in this project's scope.
        #[arg(long, short)]
        project: Option<String>,
    },

    /// Delete defeated beliefs whose grace period has elapsed (attenuated
    /// deletion — soft-retirement via record_defeat, not immediate hard
    /// deletion, so a wrong defeat can still be caught before it's gone).
    /// Requires the user's [retirement].grace_hours configuration; no default
    /// or per-call retention override is selected.
    SweepDefeated {
        /// Probability below which a defeated belief becomes eligible for deletion.
        #[arg(long, short, default_value_t = 0.3, value_parser = probability_argument)]
        threshold: f64,

        /// Restrict the sweep to this project plus untagged beliefs.
        #[arg(long, short)]
        project: Option<String>,
    },

    /// Manage indexed documents (load, semantic search, clear).
    ///
    /// Requires [embeddings] in config.toml.
    #[command(subcommand)]
    Doc(DocCmd),

    /// Backfill `belief_embeddings` for any beliefs missing a vector.
    ///
    /// Idempotent — beliefs whose embeddings are already stored are skipped.
    /// New beliefs added via `insert_belief` get their vectors automatically
    /// going forward; this command is for one-time backfill of beliefs that
    /// existed before the embedding pipeline was wired in.
    /// Requires [embeddings] in config.toml.
    Reembed,

    /// Counterfactual query: P(downstream | do(belief = value)).
    ///
    /// Severs the target belief's incoming edges and propagates the clamped
    /// value along CAUSES edges only. READ-ONLY — prints the projected
    /// probabilities of causal descendants; does NOT modify the graph.
    Intervene {
        /// UUID of the belief to intervene on (clamp).
        id: String,
        /// The value to clamp it to, in [0.0, 1.0].
        value: f64,
    },

    /// Handle Claude Code hook events — read JSON from stdin, inject relevant
    /// beliefs into the response. Always exits 0; never blocks a tool call.
    Hook {
        #[command(subcommand)]
        event: HookEvent,
    },
}

/// Claude Code hook event variants.
#[derive(Subcommand)]
enum HookEvent {
    /// UserPromptSubmit hook — inject beliefs relevant to the user's prompt.
    ///
    /// Reads {"prompt": "..."} from stdin, prints matching beliefs as plain
    /// text to stdout. Claude Code injects stdout into the conversation
    /// context for this hook event.
    Prompt,

    /// PreToolUse hook — inject beliefs relevant to the file or command.
    ///
    /// Reads {"tool_input": {"file_path"|"path"|"command": "..."}} from stdin,
    /// prints a JSON object with hookSpecificOutput.additionalContext to stdout.
    Pretooluse,

    /// Stop hook — block the turn from ending while memory_type=working
    /// beliefs are still live, forcing consolidation (promote to fact/
    /// experiential via insert_belief, or discard via delete_belief) instead
    /// of relying on the calling agent to remember to do it. This is the
    /// enforcement mechanism the Working+consolidation design (docs
    /// belief history: 99d9b202, 422e325d) never had — a prose protocol
    /// with no gate gets skipped under load, the same way the
    /// knowledge-writeback line in this environment's own Stop hooks did
    /// until it was made blocking. Unlike Prompt/Pretooluse, this CAN exit
    /// non-zero (Claude Code's convention for a Stop hook that blocks).
    ///
    /// Reads {"stop_hook_active": bool, ...} from stdin (same shape as this
    /// environment's other Stop hooks). If stop_hook_active is true, exits 0
    /// immediately — the hook has already fired once this turn and Claude
    /// Code is re-invoking after a block; re-blocking would loop forever.
    Stop {
        /// Restrict the check to Working beliefs tagged with this project
        /// (plus untagged/global ones — `list_beliefs_by_project`'s
        /// inclusion semantics, `n.project = $project OR n.project IS NULL`,
        /// same as every other project-scoped mimir query). The mimir DB is
        /// shared across concurrent sessions/projects — scoping isolates
        /// cross-PROJECT interference (a yovico Working belief won't block a
        /// mimir session), but an UNTAGGED Working belief from any session
        /// still matches every scoped check, same limitation already
        /// documented on `list_beliefs_filtered`. Omit to check globally.
        #[arg(long, short)]
        project: Option<String>,
    },

    /// Declare this Claude Code session's project, for `hook prompt`/`hook
    /// pretooluse` to scope their belief injection by (issue #9,
    /// spec/Mimir/Session.agda).
    ///
    /// NOT a Claude Code hook event — there is no hook that fires "the agent
    /// decided something mid-conversation". This is invoked directly by the
    /// agent via the Bash tool, after asking the user (or stating a guess
    /// and letting them correct it) which project the session is about.
    /// Reads the session id from $CLAUDE_CODE_SESSION_ID (present in every
    /// Bash tool subprocess's environment — verified live, not assumed; see
    /// mimir belief 71b82a15), NOT from stdin JSON, since a plain Bash
    /// invocation has none. Writes /tmp/mimir-session-project-<sid>, upsert
    /// (overwrite) semantics — spec/Mimir/Session.agda's setSessionProject.
    /// Silently no-ops (still exits 0) if the env var is unset, e.g. run
    /// outside a Claude Code session.
    SetProject {
        /// The project name to scope this session's hook-injected queries to.
        name: String,
    },
}

/// Evidence (GROUNDS edges) subcommands.
#[derive(Subcommand)]
enum EvidenceCmd {
    /// Ground a belief in a document chunk: add a GROUNDS edge.
    Add {
        /// UUID of the document chunk (from `mimir query-doc` output).
        chunk_id: String,
        /// UUID of the belief to ground.
        belief_id: String,
        /// Grounding strength in [0.0, 1.0].
        #[arg(long, default_value_t = 1.0)]
        weight: f64,
    },
    /// List the document passages grounding a belief.
    List {
        /// UUID of the belief.
        belief_id: String,
    },
}

/// `mimir delete <belief|pattern> <id>` subcommands.
#[derive(Subcommand)]
enum DeleteCmd {
    /// Delete a belief (and all its edges) by UUID.
    Belief {
        /// UUID of the belief to delete.
        id: String,
    },
    /// Delete a pattern by UUID.
    Pattern {
        /// UUID of the pattern to delete.
        id: String,
    },
}

/// `mimir doc <load|query|clear>` subcommands.
#[derive(Subcommand)]
enum DocCmd {
    /// Parse a markdown file into chunks, embed, and index for semantic search.
    ///
    /// Re-indexing the same path replaces existing chunks.
    Load {
        /// Path to the markdown file to index.
        path: String,

        /// Tag all chunks with this project (optional).
        #[arg(long, short)]
        project: Option<String>,
    },
    /// Semantic search over indexed document chunks.
    Query {
        /// Query text to embed and search.
        context: String,

        /// Restrict search to chunks tagged with this project.
        #[arg(long, short)]
        project: Option<String>,

        /// Positive result count; omit for all matching records.
        #[arg(long, short)]
        limit: Option<std::num::NonZeroUsize>,
    },
    /// Remove all chunks and embeddings for a document path.
    Clear {
        /// Path of the document to remove.
        path: String,
    },
}

/// Parse a `KEY=VALUE` CLI argument into a `(key, value)` pair.
fn parse_kv(s: &str) -> Result<(String, String), String> {
    match s.split_once('=') {
        Some((k, v)) if !k.is_empty() => Ok((k.to_string(), v.to_string())),
        _ => Err(format!("expected KEY=VALUE, got `{s}`")),
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

fn main() -> Result<()> {
    if let Some(result) = mimir_core::embed::worker_entrypoint() {
        return result;
    }
    application_main()
}

#[tokio::main]
async fn application_main() -> Result<()> {
    let cli = match Cli::try_parse() {
        Ok(cli) => cli,
        Err(error) => {
            if matches!(
                error.kind(),
                clap::error::ErrorKind::DisplayHelp | clap::error::ErrorKind::DisplayVersion
            ) {
                error.exit();
            }
            println!("{}", mimir_json::to_string(&corrections::parser(&error))?);
            return Ok(());
        }
    };

    if let Some(correction) = corrections::command(&cli.command) {
        println!("{}", mimir_json::to_string(&correction)?);
        return Ok(());
    }

    match cli.command {
        Command::Judge(command) => std::process::exit(judge::dispatch(command).await),
        Command::Init { pairs } => cmd_init(pairs)?,
        Command::Config(command) => configuration::dispatch(command)?,
        Command::Stats => cmd_stats().await?,
        Command::List { project, limit } => cmd_list(project, limit).await?,
        Command::Patterns { project, limit } => cmd_patterns(project, limit).await?,
        Command::Query {
            text,
            limit,
            evidence,
            project,
            prefer_type,
        } => cmd_query(&text, limit, evidence, project.as_deref(), prefer_type).await?,
        Command::Evidence(cmd) => cmd_evidence(cmd).await?,
        Command::Delete(DeleteCmd::Belief { id }) => cmd_delete(&id).await?,
        Command::Delete(DeleteCmd::Pattern { id }) => cmd_delete_pattern(&id).await?,
        Command::Forget { project } => cmd_forget(&project).await?,
        Command::Decay { factor, project } => cmd_decay(factor, project.as_deref()).await?,
        Command::Contradictions { project } => cmd_contradictions(project.as_deref()).await?,
        Command::SweepDefeated { threshold, project } => {
            cmd_sweep_defeated(threshold, project.as_deref()).await?
        }
        Command::Doc(DocCmd::Load { path, project }) => cmd_load(&path, project.as_deref()).await?,
        Command::Doc(DocCmd::Query {
            context,
            project,
            limit,
        }) => cmd_query_doc(&context, project.as_deref(), limit).await?,
        Command::Doc(DocCmd::Clear { path }) => cmd_clear_doc(&path).await?,
        Command::Reembed => cmd_reembed().await?,
        Command::Intervene { id, value } => cmd_intervene(&id, value).await?,
        // Prompt/Pretooluse must never exit non-zero — discard any error
        // silently. Stop is the one exception: it can legitimately block by
        // exiting non-zero (Claude Code's Stop-hook convention), and does so
        // itself via std::process::exit inside cmd_hook_stop.
        Command::Hook { event } => {
            let _ = cmd_hook(event).await;
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

async fn connect() -> Result<MimirService> {
    let (cfg, operations) = Config::load_with_operations(&Config::config_path())?;
    operations.logging.prepare()?;
    MimirService::connect(&cfg).await
}

// ---------------------------------------------------------------------------
// mimir init
// ---------------------------------------------------------------------------

fn cmd_init(pairs: Vec<(String, String)>) -> Result<()> {
    if pairs.is_empty() {
        let path = match Config::create_template()? {
            mimir_core::config::TemplatePreparation::Created(path) => {
                println!("Created: {}", path.display());
                path
            }
            mimir_core::config::TemplatePreparation::Existing(path) => {
                println!("Opening existing configuration: {}", path.display());
                path
            }
        };
        println!("Opening in $EDITOR… (save and close to finish)");
        let editor = std::env::var("EDITOR").unwrap_or_else(|_| "vi".to_string());
        let status = std::process::Command::new(&editor)
            .arg(&path)
            .status()
            .with_context(|| format!("Unable to start the editor for {}. Choose a working EDITOR and rerun `mimir init`; the configuration was not replaced or removed by Mimir.", path.display()))?;
        anyhow::ensure!(
            status.success(),
            "The editor did not finish successfully ({status}) for {}. Mimir did not replace or remove the configuration. Inspect that file and rerun `mimir init` to reopen it, or choose a working EDITOR.",
            path.display()
        );
    } else {
        match Config::create_from_kv(&pairs)? {
            mimir_core::config::ConfigCreation::Created(path) => {
                println!("Created: {}", path.display())
            }
            mimir_core::config::ConfigCreation::AlreadyConfigured(path) => {
                println!("Already configured: {}", path.display())
            }
        }
    }
    println!("Restart Claude Code to activate the mimir MCP server.");
    Ok(())
}

// ---------------------------------------------------------------------------
// mimir stats
// ---------------------------------------------------------------------------

async fn cmd_stats() -> Result<()> {
    let svc = connect().await?;
    let s = svc.stats().await?;

    let contradicts_note = if s.contradicts % 2 != 0 {
        format!("{} (odd — graph may be inconsistent)", s.contradicts)
    } else {
        format!("{} ({} pairs)", s.contradicts, s.contradicts / 2)
    };

    println!("beliefs:  {:>6}", s.beliefs);
    println!("patterns: {:>6}", s.patterns);
    println!("edges");
    println!("  supports:    {:>6}", s.supports);
    println!("  defeats:     {:>6}", s.defeats);
    println!("  causes:      {:>6}", s.causes);
    println!("  contradicts: {}", contradicts_note);

    Ok(())
}

// ---------------------------------------------------------------------------
// mimir list
// ---------------------------------------------------------------------------

async fn cmd_list(project: Option<String>, limit: mimir_core::Selection) -> Result<()> {
    let svc = connect().await?;
    let mut beliefs = svc.list_beliefs(project.as_deref()).await?;

    // Sort by probability descending (consistent with query_relevant).
    beliefs.sort_by(|a, b| {
        b.probability
            .value()
            .partial_cmp(&a.probability.value())
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    if let Some(count) = limit {
        beliefs.truncate(count.get());
    }

    if beliefs.is_empty() {
        println!("(no beliefs)");
        return Ok(());
    }

    for b in &beliefs {
        let proj = b
            .project
            .as_deref()
            .map(|p| format!("  [{}]", p))
            .unwrap_or_default();
        // Fact is the default and the overwhelming majority — only call out
        // the type when it's non-default, to keep normal output uncluttered.
        let mt = if b.memory_type == mimir_core::graph::MemoryType::Fact {
            String::new()
        } else {
            format!("  <{}>", b.memory_type.as_str())
        };
        println!(
            "{}  p={:.3}  c={:.3}  {}{}{}",
            b.id,
            b.probability.value(),
            b.confidence.value(),
            b.content,
            mt,
            proj,
        );
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// mimir patterns
// ---------------------------------------------------------------------------

async fn cmd_patterns(project: Option<String>, limit: mimir_core::Selection) -> Result<()> {
    let svc = connect().await?;
    let mut patterns = svc.list_patterns(project.as_deref()).await?;

    // Sort by success rate descending.
    patterns.sort_by(|a, b| {
        b.success_rate
            .value()
            .partial_cmp(&a.success_rate.value())
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    if let Some(count) = limit {
        patterns.truncate(count.get());
    }

    if patterns.is_empty() {
        println!("(no patterns)");
        return Ok(());
    }

    for p in &patterns {
        println!(
            "{}  rate={:.3}  [{}] → [{}]",
            p.id,
            p.success_rate.value(),
            p.situation,
            p.approach,
        );
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// mimir query
// ---------------------------------------------------------------------------

async fn cmd_query(
    text: &str,
    limit: mimir_core::Selection,
    evidence: bool,
    project: Option<&str>,
    prefer_type: Option<mimir_core::graph::MemoryType>,
) -> Result<()> {
    let svc = connect().await?;

    if evidence {
        let grounded = svc
            .query_relevant_grounded_preferred(text, limit, None, project, prefer_type)
            .await?;
        println!("Search context: {}", grounded.retrieval.context);
        println!("{}", grounded.retrieval.message);
        println!("{}", grounded.retrieval.coverage);
        println!("Next step: {}", grounded.retrieval.next_step);
        let grounded = grounded.beliefs;
        if grounded.is_empty() {
            println!("(no results)");
            return Ok(());
        }
        for gb in &grounded {
            let b = &gb.belief;
            let proj = b
                .project
                .as_deref()
                .map(|p| format!("  [{}]", p))
                .unwrap_or_default();
            println!(
                "{}  p={:.3}  c={:.3}  {}{}",
                b.id,
                b.probability.value(),
                b.confidence.value(),
                b.content,
                proj,
            );
            for e in &gb.evidence {
                let section = if e.section_path.is_empty() {
                    String::new()
                } else {
                    format!(" § {}", e.section_path.join(" > "))
                };
                println!("    ↳ w={:.2}  {}{}", e.weight, e.document_path, section,);
                println!("        {}", e.snippet);
            }
        }
        return Ok(());
    }

    let beliefs = svc
        .query_relevant(text, limit, project, prefer_type)
        .await?;
    println!("Search context: {}", beliefs.retrieval.context);
    println!("{}", beliefs.retrieval.message);
    println!("{}", beliefs.retrieval.coverage);
    println!("Next step: {}", beliefs.retrieval.next_step);
    let beliefs = beliefs.beliefs;
    if beliefs.is_empty() {
        println!("(no results)");
        return Ok(());
    }

    for b in &beliefs {
        let proj = b
            .project
            .as_deref()
            .map(|p| format!("  [{}]", p))
            .unwrap_or_default();
        println!(
            "{}  p={:.3}  c={:.3}  {}{}",
            b.id,
            b.probability.value(),
            b.confidence.value(),
            b.content,
            proj,
        );
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// mimir evidence add / list
// ---------------------------------------------------------------------------

async fn cmd_evidence(cmd: EvidenceCmd) -> Result<()> {
    let svc = connect().await?;
    match cmd {
        EvidenceCmd::Add {
            chunk_id,
            belief_id,
            weight,
        } => {
            let chunk = chunk_id
                .parse::<uuid::Uuid>()
                .map_err(|_| anyhow::anyhow!("invalid chunk UUID: {}", chunk_id))?;
            let belief = belief_id
                .parse::<uuid::Uuid>()
                .map_err(|_| anyhow::anyhow!("invalid belief UUID: {}", belief_id))?;
            if corrections::reference(svc.add_evidence(belief, chunk, weight).await)?.is_none() {
                return Ok(());
            }
            println!("grounded {} ← {}  (w={:.2})", belief, chunk, weight);
        }
        EvidenceCmd::List { belief_id } => {
            let belief = belief_id
                .parse::<uuid::Uuid>()
                .map_err(|_| anyhow::anyhow!("invalid belief UUID: {}", belief_id))?;
            let refs = svc.evidence_for_belief(belief, None).await?;
            if refs.is_empty() {
                println!("(no evidence)");
                return Ok(());
            }
            for e in &refs {
                let section = if e.section_path.is_empty() {
                    String::new()
                } else {
                    format!(" § {}", e.section_path.join(" > "))
                };
                println!(
                    "{}  w={:.2}  {}{}",
                    e.chunk_id, e.weight, e.document_path, section
                );
                println!("    {}", e.snippet);
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// mimir intervene — counterfactual do(belief = value), read-only
// ---------------------------------------------------------------------------

async fn cmd_intervene(id: &str, value: f64) -> Result<()> {
    let target = id
        .parse::<uuid::Uuid>()
        .map_err(|_| anyhow::anyhow!("invalid UUID: {}", id))?;

    let svc = connect().await?;
    let Some((updates, beliefs)) =
        corrections::reference(svc.query_intervention_with_beliefs(target, value).await)?
    else {
        return Ok(());
    };
    let beliefs: std::collections::HashMap<_, _> =
        beliefs.iter().map(|belief| (belief.id, belief)).collect();

    if updates.is_empty() {
        println!("(no causal descendants affected)");
        return Ok(());
    }

    for (uid, prob) in &updates {
        // Fetch content for a readable line; fall back to the bare id.
        let content = beliefs
            .get(uid)
            .map(|belief| belief.content.as_str())
            .unwrap_or_default();
        println!("{}  p_proj={:.3}  {}", uid, prob.value(), content);
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// mimir delete
// ---------------------------------------------------------------------------

async fn cmd_delete(id: &str) -> Result<()> {
    let uuid = id
        .parse::<uuid::Uuid>()
        .map_err(|_| anyhow::anyhow!("invalid UUID: {}", id))?;

    let svc = connect().await?;
    if svc.delete_belief(uuid).await? {
        println!("deleted");
    } else {
        println!("not found");
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// mimir delete-pattern
// ---------------------------------------------------------------------------

async fn cmd_delete_pattern(id: &str) -> Result<()> {
    let uuid = id
        .parse::<uuid::Uuid>()
        .map_err(|_| anyhow::anyhow!("invalid UUID: {}", id))?;

    let svc = connect().await?;
    if svc.delete_pattern(uuid).await? {
        println!("deleted");
    } else {
        println!("not found");
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// mimir forget
// ---------------------------------------------------------------------------

async fn cmd_forget(project: &str) -> Result<()> {
    let svc = connect().await?;
    let count = svc.delete_project(project).await?;
    println!("deleted {}  [project: {}]", count, project);
    Ok(())
}

// ---------------------------------------------------------------------------
// mimir decay
// ---------------------------------------------------------------------------

async fn cmd_decay(factor: f64, project: Option<&str>) -> Result<()> {
    let svc = connect().await?;
    let count = svc.decay_beliefs(Some(factor), project).await?;
    println!("decayed {}  [factor: {:.3}]", count, factor);
    Ok(())
}

// ---------------------------------------------------------------------------
// mimir sweep-defeated
// ---------------------------------------------------------------------------

async fn cmd_sweep_defeated(threshold: f64, project: Option<&str>) -> Result<()> {
    let svc = connect().await?;
    let policy = match svc.retirement_policy() {
        Ok(policy) => policy,
        Err(issue) => {
            println!("{}", mimir_json::to_string(issue.correction())?);
            return Ok(());
        }
    };
    let count = svc.sweep_expired_defeated(threshold, project).await?;
    println!(
        "deleted {}  [threshold: {:.2}, configured grace: {}h]",
        count,
        threshold,
        policy.grace_hours()
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// mimir load
// ---------------------------------------------------------------------------

async fn cmd_load(path: &str, project: Option<&str>) -> Result<()> {
    let svc = connect().await?;
    let count = svc.load_document(path, project).await?;
    let proj_note = project
        .map(|p| format!("  [project: {}]", p))
        .unwrap_or_default();
    println!("loaded {} chunk(s)  {}{}", count, path, proj_note);
    Ok(())
}

// ---------------------------------------------------------------------------
// mimir query-doc
// ---------------------------------------------------------------------------

fn document_result_display(result: &mimir_core::documents::QueryResult) -> String {
    let section = if result.section_path.is_empty() {
        String::new()
    } else {
        format!("  § {}", result.section_path.join(" > "))
    };
    format!(
        "{}{}\n  {}\n",
        result.document_path, section, result.content
    )
}

#[cfg(test)]
mod document_output_tests {
    use super::*;

    #[test]
    fn full_document_passage_survives_display_with_unicode_and_whitespace() {
        let content = format!(
            "  {}\nlast supporting line\t ",
            "λ全文 passage ".repeat(300)
        );
        let result = mimir_core::documents::QueryResult {
            id: "display-only".into(),
            document_path: "/document.md".into(),
            section_path: vec!["complete section".into(), "detail".into()],
            content: content.clone(),
            parent_content: None,
        };
        let shown = document_result_display(&result);
        assert!(shown.starts_with("/document.md  § complete section > detail\n"));
        assert!(shown.contains(&content));
        assert!(!shown.contains('…'));
    }
}

async fn cmd_query_doc(
    context: &str,
    project: Option<&str>,
    limit: mimir_core::Selection,
) -> Result<()> {
    let svc = connect().await?;
    let Some(results) = corrections::reference(svc.query_document(context, project, limit).await)?
    else {
        return Ok(());
    };

    if results.is_empty() {
        println!("(no results)");
        return Ok(());
    }

    for r in &results {
        println!("{}", document_result_display(r));
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// mimir clear-doc
// ---------------------------------------------------------------------------

async fn cmd_clear_doc(path: &str) -> Result<()> {
    let svc = connect().await?;
    let count = svc.clear_document(path).await?;
    println!("cleared {}  {}", count, path);
    Ok(())
}

// ---------------------------------------------------------------------------
// mimir contradictions
// ---------------------------------------------------------------------------

async fn cmd_contradictions(project: Option<&str>) -> Result<()> {
    let svc = connect().await?;
    let (pairs, beliefs) = svc.get_contradictions_with_beliefs(project).await?;
    let beliefs: std::collections::HashMap<_, _> =
        beliefs.iter().map(|belief| (belief.id, belief)).collect();

    if pairs.is_empty() {
        println!("(no active contradictions)");
        return Ok(());
    }

    // Deduplicate: keep only (a, b) where a.to_string() < b.to_string().
    let mut seen = std::collections::HashSet::new();
    let mut deduped = Vec::new();
    for (a, b) in pairs {
        let key = if a.to_string() < b.to_string() {
            (a, b)
        } else {
            (b, a)
        };
        if seen.insert(key) {
            deduped.push(key);
        }
    }

    for (a, b) in &deduped {
        let ca = beliefs
            .get(a)
            .map(|b| b.content.clone())
            .unwrap_or_else(|| a.to_string());
        let cb = beliefs
            .get(b)
            .map(|b| b.content.clone())
            .unwrap_or_else(|| b.to_string());
        println!("  [{}]  ⟺  [{}]", ca, cb);
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// reembed — backfill belief_embeddings
// ---------------------------------------------------------------------------

async fn cmd_reembed() -> Result<()> {
    // Check prerequisites before startup or vector work. Report an actionable
    // incomplete operation, never a completed count for absent vectors.
    let cfg = Config::load()
        .map_err(|e| anyhow::anyhow!("{e}\nRun `mimir init` to create a config file."))?;
    if cfg.embeddings.is_none() {
        return print_backfill_decision(&[],0,None,
            "Embedding is not configured. Ask the user to choose or repair [embeddings] in Mimir configuration before re-embedding; do not choose a model automatically.",
            "not_attempted",None);
    }
    let svc = MimirService::connect(&cfg).await?;

    let beliefs = svc.list_beliefs(None).await?;
    if beliefs.is_empty() {
        println!("no beliefs to embed.");
        return Ok(());
    }

    let embedded_ids: std::collections::HashSet<uuid::Uuid> =
        svc.list_embedded_belief_ids().await?.into_iter().collect();

    let mut embedded = 0_usize;
    let mut skipped = 0_usize;
    let mut confirmed = Vec::new();
    for belief in &beliefs {
        if embedded_ids.contains(&belief.id) {
            skipped += 1;
            continue;
        }
        if let Err(error) = svc.embed_and_store_belief(belief).await {
            let preparation = error.downcast_ref::<mimir_core::preparation::PreparationRequired>();
            let publication = if preparation.is_some()
                || error.is::<mimir_core::store::BeliefEmbeddingTargetMissing>()
            {
                "not_attempted"
            } else {
                "unconfirmed"
            };
            return print_backfill_decision(
                &confirmed,
                skipped,
                Some(belief.id),
                &error.to_string(),
                publication,
                preparation.map(|value| value.correction()),
            );
        }
        confirmed.push(belief.id);
        embedded += 1;
        println!("  embedded {}  {}", belief.id, &belief.content);
    }

    println!(
        "\nembedded {embedded} belief{}; skipped {skipped} that already had vectors.",
        if embedded == 1 { "" } else { "s" }
    );
    Ok(())
}

fn print_backfill_decision(
    confirmed: &[uuid::Uuid],
    skipped: usize,
    current: Option<uuid::Uuid>,
    problem: &str,
    publication: &str,
    correction: Option<&mimir_core::interaction::NeedsInput>,
) -> Result<()> {
    println!(
        "{}",
        mimir_json::to_string(&serde_json::json!({
            "status":"needs_input","operation_status":"incomplete",
            "confirmed_counts":{"embedded":confirmed.len(),"skipped":skipped},
            "business_changes":{"embedded_belief_ids":confirmed},
            "current_belief_id":current,"current_vector_publication":publication,
            "problem":problem,"current_belief_correction":correction,
            "next_action":"open_user_dialog",
            "suggested_correction":"Explain this problem and the confirmed prior writes to the user. If the current vector outcome is unconfirmed, read it back before retrying; do not infer rollback or success from an error. Ask whether to repair the prerequisite or cancel. Do not silently change the model or report this run complete."
        }))?
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// mimir hook prompt / pretooluse
// ---------------------------------------------------------------------------

async fn cmd_hook(event: HookEvent) -> Result<()> {
    match event {
        HookEvent::Prompt => cmd_hook_prompt().await,
        HookEvent::Pretooluse => cmd_hook_pretooluse().await,
        HookEvent::Stop { project } => cmd_hook_stop(project.as_deref()).await,
        HookEvent::SetProject { name } => cmd_hook_set_project(&name).await,
    }
}

/// Path of the session-scoped project side channel (spec/Mimir/Session.agda
/// SessionProjectStore) for a given Claude Code session id.
fn session_project_path(session_id: &str) -> std::path::PathBuf {
    std::env::temp_dir().join(format!("mimir-session-project-{session_id}"))
}

/// `mimir hook set-project NAME` — see the HookEvent::SetProject doc comment
/// for why this reads $CLAUDE_CODE_SESSION_ID instead of stdin JSON. Fails
/// open (still exits 0) on any error — this must never block the agent's
/// turn, same posture as the other hook subcommands.
///
/// The moment a session declares its project is also the first moment any
/// *other* session's orphaned Working beliefs for that same project become
/// identifiable — before this, list_beliefs_filtered(project, Working) could
/// not be scoped at all. Rather than wait for `mimir hook stop` (which only
/// fires at a graceful end-of-turn the orphaning session never reached) or a
/// background sweep (which may not run for hours), surface them here,
/// directly on this command's stdout — this is invoked by the agent via
/// Bash, not by the Claude Code harness, so plain stdout is what the agent
/// sees, no hookSpecificOutput plumbing needed. Best-effort only: a DB
/// connect/query failure here must not block declaring the project, so any
/// error is swallowed silently, same fail-open posture as every other hook
/// subcommand.
async fn cmd_hook_set_project(name: &str) -> Result<()> {
    let Ok(session_id) = std::env::var("CLAUDE_CODE_SESSION_ID") else {
        return Ok(());
    };
    let _ = std::fs::write(session_project_path(&session_id), name);

    if let Ok(svc) = connect().await {
        if let Ok(working) = svc
            .list_beliefs_filtered(Some(name), Some(mimir_core::graph::MemoryType::Working))
            .await
        {
            if !working.is_empty() {
                println!(
                    "NOTE: {} pre-existing memory_type=working belief(s) found for project \
                     '{name}' — these were left by a prior session (most likely one that \
                     never reached a graceful end-of-turn, e.g. Ctrl-C or a crash) and were \
                     never consolidated. Consider triaging them now (promote via insert_belief \
                     as fact/experiential + delete_belief on the original, or discard via \
                     delete_belief) rather than leaving them for a background sweep:",
                    working.len()
                );
                for b in &working {
                    println!("  {}  {}", b.id, b.content);
                }
            }
        }
    }

    Ok(())
}

/// Read session_id from a hook's stdin JSON (harness-invoked hooks only —
/// see HookEvent::SetProject's doc comment for the two different ways a
/// process learns the session id) and look up its declared project, if any.
/// `None` when unset — the caller MUST treat that as "query unscoped", never
/// as license to guess (spec/Mimir/Session.agda getSessionProject's semantic
/// note).
fn session_project_from_hook_json(v: &serde_json::Value) -> Option<String> {
    let session_id = v["session_id"].as_str()?;
    std::fs::read_to_string(session_project_path(session_id))
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
}

/// Stop hook: block the turn from ending while `memory_type=working` beliefs
/// are still live. This is the enforcement half of the Working+consolidation
/// design — every belief is written as `working` during a task, and this
/// hook is the gate that forces promotion (fact/experiential) or discard
/// before the turn can actually end, instead of relying on remembering to
/// do it. Fails OPEN (exits 0) on any infrastructure error (can't connect,
/// bad JSON, etc.) — a broken hook must never permanently lock a session out
/// of ending; it should only block on the specific, real condition it exists
/// to catch.
/// Best-effort project-name inference from the current directory: the git
/// repo's toplevel basename, or the cwd basename if not inside a git repo.
/// `None` if neither is resolvable (e.g. cwd deleted out from under us).
fn infer_project_from_cwd() -> Option<String> {
    std::process::Command::new("git")
        .args(["rev-parse", "--show-toplevel"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| std::path::PathBuf::from(s.trim().to_string()))
        .or_else(|| std::env::current_dir().ok())
        .and_then(|p| p.file_name().map(|n| n.to_string_lossy().into_owned()))
}

async fn cmd_hook_stop(project: Option<&str>) -> Result<()> {
    use std::io::Read;
    let mut input = String::new();
    if std::io::stdin().read_to_string(&mut input).is_err() {
        return Ok(());
    }
    let v: serde_json::Value = match mimir_json::from_str(&input) {
        Ok(v) => v,
        Err(_) => return Ok(()),
    };

    // Loop-prevention: Claude Code sets stop_hook_active=true when re-invoking
    // after this hook already blocked once this turn. Do not block again —
    // that would loop forever. Same convention as this environment's other
    // Stop hooks (knowledge-writeback, critic).
    if v["stop_hook_active"].as_bool().unwrap_or(false) {
        return Ok(());
    }

    // This is wired globally (~/.claude/settings.json, every repo), so there
    // is no per-invocation --project flag in practice. Without scoping,
    // list_beliefs_filtered(None, ...) falls through to an unfiltered
    // cross-project scan, and a Working belief left by a concurrent session
    // in an unrelated project would block this one. Infer the project from
    // cwd (git toplevel basename, else cwd basename) instead — matching the
    // project string a model would naturally use when tagging beliefs from
    // that same directory. Untagged/global Working beliefs still participate
    // via list_beliefs_by_project's `OR n.project IS NULL`.
    let inferred;
    let project = match project {
        Some(p) => Some(p),
        None => {
            inferred = infer_project_from_cwd();
            inferred.as_deref()
        }
    };

    let svc = match connect().await {
        Ok(svc) => svc,
        Err(_) => return Ok(()), // fail open — infra issue, not a real block
    };
    let working = match svc
        .list_beliefs_filtered(project, Some(mimir_core::graph::MemoryType::Working))
        .await
    {
        Ok(b) => b,
        Err(_) => return Ok(()),
    };
    if working.is_empty() {
        return Ok(());
    }

    let mut msg = format!(
        "POLICY REQUIREMENT: {} working-memory belief(s) are still unconsolidated. \
         Every belief this session should have been written as memory_type=working; \
         consolidation (promote to fact/experiential via insert_belief, or discard via \
         delete_belief) must happen before the turn ends — not skipped, not deferred. \
         Resolve each one below, then finish:\n",
        working.len()
    );
    for b in &working {
        msg.push_str(&format!("  {}  {}\n", b.id, b.content));
    }
    eprintln!("{}", msg.trim_end());
    std::process::exit(2);
}

async fn cmd_hook_prompt() -> Result<()> {
    use std::io::Read;
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input)?;

    let v: serde_json::Value = mimir_json::from_str(&input)?;
    let prompt = v["prompt"].as_str().unwrap_or("").trim().to_string();
    if prompt.is_empty() {
        return Ok(());
    }

    let project = session_project_from_hook_json(&v);
    let svc = connect().await?;
    let beliefs = svc
        .query_relevant(&prompt, None, project.as_deref(), None)
        .await?;
    println!("Search context: {}", beliefs.retrieval.context);
    println!("{}", beliefs.retrieval.message);
    println!("{}", beliefs.retrieval.coverage);
    println!("Next step: {}", beliefs.retrieval.next_step);
    let beliefs = beliefs.beliefs;
    if beliefs.is_empty() {
        return Ok(());
    }

    println!(
        "[Prior knowledge from past sessions — apply directly, do not rediscover empirically:]"
    );
    for b in &beliefs {
        let proj = b
            .project
            .as_deref()
            .map(|p| format!("  [{}]", p))
            .unwrap_or_default();
        println!(
            "{}  p={:.3}  c={:.3}  {}{}",
            b.id,
            b.probability.value(),
            b.confidence.value(),
            b.content,
            proj,
        );
    }

    Ok(())
}

async fn cmd_hook_pretooluse() -> Result<()> {
    use std::io::Read;
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input)?;

    let v: serde_json::Value = mimir_json::from_str(&input)?;
    let ti = &v["tool_input"];
    let query_raw = ti["file_path"]
        .as_str()
        .or_else(|| ti["path"].as_str())
        .or_else(|| ti["command"].as_str())
        .unwrap_or("")
        .trim();
    if query_raw.is_empty() {
        return Ok(());
    }

    let project = session_project_from_hook_json(&v);
    let svc = connect().await?;
    let beliefs = svc
        .query_relevant(query_raw, None, project.as_deref(), None)
        .await?;
    let mut lines = format!(
        "Search context: {}\n{}\n{}\nNext step: {}\n",
        beliefs.retrieval.context,
        beliefs.retrieval.message,
        beliefs.retrieval.coverage,
        beliefs.retrieval.next_step
    );
    let beliefs = beliefs.beliefs;
    if !beliefs.is_empty() {
        lines.push_str("Prior knowledge relevant to this action — apply directly:\n");
    }
    for b in &beliefs {
        let proj = b
            .project
            .as_deref()
            .map(|p| format!("  [{}]", p))
            .unwrap_or_default();
        lines.push_str(&format!(
            "{}  p={:.3}  c={:.3}  {}{}\n",
            b.id,
            b.probability.value(),
            b.confidence.value(),
            b.content,
            proj,
        ));
    }

    let out = serde_json::json!({
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "additionalContext": lines.trim_end_matches('\n')
        }
    });
    println!("{}", out);

    Ok(())
}
