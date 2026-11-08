use anyhow::Result;
use clap::Subcommand;
use mimir_core::{config::Config, operations};
use std::path::PathBuf;
#[derive(Subcommand)]
pub enum Command {
    /// Validate required settings offline, without running the judge.
    Check {
        #[arg(long)]
        config: Option<PathBuf>,
    },
    /// Upgrade operational metadata, preserving credentials and other settings.
    Upgrade {
        #[arg(long)]
        config: Option<PathBuf>,
        /// Required when the configuration has no logging.directory.
        #[arg(long)]
        log_directory: Option<PathBuf>,
    },
}
pub fn dispatch(command: Command) -> Result<()> {
    let (path, upgrade) = match command {
        Command::Check { config } => (config.unwrap_or_else(Config::config_path), None),
        Command::Upgrade {
            config,
            log_directory,
        } => (
            config.unwrap_or_else(Config::config_path),
            Some(log_directory),
        ),
    };
    if let Some(directory) = upgrade {
        operations::upgrade(&path, directory.as_deref())?;
    }
    let (core, operations) = Config::load_with_operations(&path)?;
    operations::check_retired_limits(&core)?;
    if core.retirement.is_some() {
        core.retirement_policy()?;
    }
    if core.judge.is_some() || core.llm.is_some() {
        super::judge::config::load(Some(&path))?;
    }
    println!("Configuration compatible with Mimir {} (format {}).\nConfig: {}\nLogs: {}\nLogs append complete entries; Mimir applies no rotation or retention limit.\nNo database or model request was made.",env!("CARGO_PKG_VERSION"),operations.config_version,path.display(),operations.logging.directory.display());
    Ok(())
}
