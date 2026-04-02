use anyhow::Result;

use mimir_core::config::Config;

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();

    match args.get(1).map(|s| s.as_str()) {
        Some("init") => {
            let path = Config::create_template()?;
            println!("Created: {}", path.display());
            println!("Opening in $EDITOR… (save and close to finish)");
            let editor = std::env::var("EDITOR").unwrap_or_else(|_| "vi".to_string());
            std::process::Command::new(&editor).arg(&path).status()?;
            println!("Done. Restart Claude Code to activate the mimir MCP server.");
        }
        Some(cmd) => {
            eprintln!("error: unknown command '{cmd}'");
            eprintln!("usage: mimir init");
            std::process::exit(1);
        }
        None => {
            eprintln!("usage: mimir init");
            std::process::exit(1);
        }
    }

    Ok(())
}