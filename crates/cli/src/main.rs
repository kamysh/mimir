use anyhow::Result;
use clap::{Parser, Subcommand};

use mimir_core::{config::Config, MimirService};

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

#[derive(Subcommand)]
enum Command {
    /// Create a configuration template and open it in $EDITOR.
    ///
    /// Creates ~/.config/mimir/config.toml (or $XDG_CONFIG_HOME/mimir/config.toml)
    /// and opens it for editing.  Exits non-zero if the config already exists.
    Init,

    /// Print a summary of the belief graph (vertex and edge counts).
    Stats,

    /// List beliefs, optionally filtered by project.
    List {
        /// Only show beliefs tagged with this project.
        #[arg(long, short)]
        project: Option<String>,

        /// Maximum number of results (0 = no limit).
        #[arg(long, short, default_value_t = 0)]
        limit: usize,
    },

    /// List patterns.
    Patterns {
        /// Maximum number of results (0 = no limit).
        #[arg(long, short, default_value_t = 0)]
        limit: usize,
    },

    /// Hybrid search: text match plus graph expansion via SUPPORTS/CAUSES edges.
    Query {
        /// Search text (case-insensitive substring match).
        text: String,

        /// Maximum number of results (0 = no limit).
        #[arg(long, short, default_value_t = 10)]
        limit: usize,
    },

    /// Delete a belief (and all its edges) by UUID.
    Delete {
        /// UUID of the belief to delete.
        id: String,
    },

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
    },

    /// List active contradictions in the graph.
    Contradictions,

    /// Parse a markdown file into chunks, embed, and index for semantic search.
    ///
    /// Requires [embeddings] in config.toml.
    /// Re-indexing the same path replaces existing chunks.
    Load {
        /// Path to the markdown file to index.
        path: String,

        /// Tag all chunks with this project (optional).
        #[arg(long, short)]
        project: Option<String>,
    },

    /// Semantic search over indexed document chunks.
    ///
    /// Requires [embeddings] in config.toml.
    QueryDoc {
        /// Query text to embed and search.
        context: String,

        /// Restrict search to chunks tagged with this project.
        #[arg(long, short)]
        project: Option<String>,

        /// Maximum number of results (0 = no limit).
        #[arg(long, short, default_value_t = 5)]
        limit: usize,
    },

    /// Remove all chunks and embeddings for a document path.
    ClearDoc {
        /// Path of the document to remove.
        path: String,
    },
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

#[tokio::main]
async fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Command::Init => cmd_init()?,
        Command::Stats => cmd_stats().await?,
        Command::List { project, limit } => cmd_list(project, limit).await?,
        Command::Patterns { limit } => cmd_patterns(limit).await?,
        Command::Query { text, limit } => cmd_query(&text, limit).await?,
        Command::Delete { id } => cmd_delete(&id).await?,
        Command::Forget { project } => cmd_forget(&project).await?,
        Command::Decay { factor } => cmd_decay(factor).await?,
        Command::Contradictions => cmd_contradictions().await?,
        Command::Load { path, project } => cmd_load(&path, project.as_deref()).await?,
        Command::QueryDoc { context, project, limit } => cmd_query_doc(&context, project.as_deref(), limit).await?,
        Command::ClearDoc { path } => cmd_clear_doc(&path).await?,
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

async fn connect() -> Result<MimirService> {
    let cfg = Config::load()
        .map_err(|e| anyhow::anyhow!("{e}\nRun `mimir init` to create a config file."))?;
    MimirService::connect(&cfg).await
}

fn trunc(s: &str, max: usize) -> String {
    let s = s.trim();
    if s.chars().count() <= max {
        s.to_string()
    } else {
        let end: usize = s.char_indices().nth(max - 1).map(|(i, _)| i).unwrap_or(s.len());
        format!("{}…", &s[..end])
    }
}

// ---------------------------------------------------------------------------
// mimir init
// ---------------------------------------------------------------------------

fn cmd_init() -> Result<()> {
    let path = Config::create_template()?;
    println!("Created: {}", path.display());
    println!("Opening in $EDITOR… (save and close to finish)");
    let editor = std::env::var("EDITOR").unwrap_or_else(|_| "vi".to_string());
    std::process::Command::new(&editor).arg(&path).status()?;
    println!("Done. Restart Claude Code to activate the mimir MCP server.");
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

async fn cmd_list(project: Option<String>, limit: usize) -> Result<()> {
    let svc = connect().await?;
    let mut beliefs = svc.list_beliefs().await?;

    if let Some(ref p) = project {
        beliefs.retain(|b| b.project.as_deref() == Some(p.as_str()));
    }

    // Sort by probability descending (consistent with query_relevant).
    beliefs.sort_by(|a, b| {
        b.probability
            .value()
            .partial_cmp(&a.probability.value())
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    if limit > 0 {
        beliefs.truncate(limit);
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
        println!(
            "{}  p={:.3}  c={:.3}  {}{}",
            b.id,
            b.probability.value(),
            b.confidence.value(),
            trunc(&b.content, 70),
            proj,
        );
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// mimir patterns
// ---------------------------------------------------------------------------

async fn cmd_patterns(limit: usize) -> Result<()> {
    let svc = connect().await?;
    let mut patterns = svc.list_patterns().await?;

    // Sort by success rate descending.
    patterns.sort_by(|a, b| {
        b.success_rate
            .value()
            .partial_cmp(&a.success_rate.value())
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    if limit > 0 {
        patterns.truncate(limit);
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
            trunc(&p.situation, 40),
            trunc(&p.approach, 40),
        );
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// mimir query
// ---------------------------------------------------------------------------

async fn cmd_query(text: &str, limit: usize) -> Result<()> {
    let svc = connect().await?;
    let beliefs = svc.query_relevant(text, limit).await?;

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
            trunc(&b.content, 70),
            proj,
        );
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

async fn cmd_decay(factor: f64) -> Result<()> {
    let svc = connect().await?;
    let count = svc.decay_beliefs(Some(factor)).await?;
    println!("decayed {}  [factor: {:.3}]", count, factor);
    Ok(())
}

// ---------------------------------------------------------------------------
// mimir load
// ---------------------------------------------------------------------------

async fn cmd_load(path: &str, project: Option<&str>) -> Result<()> {
    let svc = connect().await?;
    let count = svc.load_document(path, project).await?;
    let proj_note = project.map(|p| format!("  [project: {}]", p)).unwrap_or_default();
    println!("loaded {} chunk(s)  {}{}", count, path, proj_note);
    Ok(())
}

// ---------------------------------------------------------------------------
// mimir query-doc
// ---------------------------------------------------------------------------

async fn cmd_query_doc(context: &str, project: Option<&str>, limit: usize) -> Result<()> {
    let svc = connect().await?;
    let results = svc.query_document(context, project, limit).await?;

    if results.is_empty() {
        println!("(no results)");
        return Ok(());
    }

    for r in &results {
        let section = if r.section_path.is_empty() {
            String::new()
        } else {
            format!("  § {}", r.section_path.join(" > "))
        };
        println!("{}{}", r.document_path, section);
        println!("  {}", trunc(&r.content, 120));
        println!();
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

async fn cmd_contradictions() -> Result<()> {
    let svc = connect().await?;
    let pairs = svc.get_contradictions().await?;

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
        let ba = svc.get_belief(*a).await?;
        let bb = svc.get_belief(*b).await?;
        let ca = ba.as_ref().map(|b| trunc(&b.content, 50)).unwrap_or_else(|| a.to_string());
        let cb = bb.as_ref().map(|b| trunc(&b.content, 50)).unwrap_or_else(|| b.to_string());
        println!("  [{}]  ⟺  [{}]", ca, cb);
    }

    Ok(())
}
