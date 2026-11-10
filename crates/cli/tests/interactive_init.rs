//! Interactive init uses only an owned config and an editor stub, offline.
#![cfg(unix)]

use anyhow::{ensure, Result};
use std::{os::unix::fs::PermissionsExt, path::PathBuf, process::Command};

struct Fixture {
    root: PathBuf,
    config: PathBuf,
    editor: PathBuf,
    record: PathBuf,
}

impl Fixture {
    fn new() -> Result<Self> {
        let root =
            std::env::temp_dir().join(format!("mimir-interactive-init-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir(&root)?;
        std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o700))?;
        let editor = root.join("editor-stub");
        std::fs::write(
            &editor,
            b"#!/bin/sh\nprintf '%s\\n' \"$1\" >>\"$MIMIR_INIT_EDITOR_RECORD\"\n",
        )?;
        std::fs::set_permissions(&editor, std::fs::Permissions::from_mode(0o700))?;
        Ok(Self {
            config: root.join("config.toml"),
            record: root.join("editor-calls"),
            root,
            editor,
        })
    }

    fn run(&self, name: &str, arguments: &[&str]) -> Result<std::process::Output> {
        let mut child = Command::new(env!("CARGO_BIN_EXE_mimir"));
        for (key, _) in std::env::vars_os() {
            let key_text = key.to_string_lossy();
            if key_text.starts_with("MIMIR_") || key_text.starts_with("PG") || key == "DATABASE_URL"
            {
                child.env_remove(key);
            }
        }
        let output = child
            .env("HOME", self.root.join("home"))
            .env("XDG_CONFIG_HOME", self.root.join("config"))
            .env("XDG_CACHE_HOME", self.root.join("cache"))
            .env("MIMIR_CONFIG", &self.config)
            .env("XDG_STATE_HOME", self.root.join("state"))
            .env("EDITOR", &self.editor)
            .env("MIMIR_INIT_EDITOR_RECORD", &self.record)
            .args(arguments)
            .output()?;
        std::fs::write(self.root.join(format!("{name}.stdout")), &output.stdout)?;
        std::fs::write(self.root.join(format!("{name}.stderr")), &output.stderr)?;
        std::fs::write(
            self.root.join(format!("{name}.exit")),
            format!("{:?}\n", output.status.code()),
        )?;
        Ok(output)
    }

    fn editor_calls(&self) -> Result<Vec<PathBuf>> {
        Ok(std::fs::read_to_string(&self.record)?
            .lines()
            .map(PathBuf::from)
            .collect())
    }
}

#[test]
fn bare_init_opens_existing_configuration_without_replacing_or_validating_it() -> Result<()> {
    let fixture = Fixture::new()?;
    let original = b"# existing user bytes\nthis is deliberately not valid TOML\n";
    std::fs::write(&fixture.config, original)?;
    std::fs::set_permissions(&fixture.config, std::fs::Permissions::from_mode(0o600))?;
    for name in ["existing", "existing-retry"] {
        let output = fixture.run(name, &["init"])?;
        ensure!(
            output.status.success(),
            "complete evidence: {}",
            fixture.root.display()
        );
        let stdout = String::from_utf8(output.stdout)?;
        ensure!(
            stdout.contains("Opening existing configuration:"),
            "{stdout}"
        );
        ensure!(!stdout.contains("Created:"), "{stdout}");
        ensure!(std::fs::read(&fixture.config)? == original);
    }
    ensure!(fixture.editor_calls()? == vec![fixture.config.clone(), fixture.config.clone()]);
    eprintln!(
        "Complete offline editor evidence: {}",
        fixture.root.display()
    );
    Ok(())
}

#[test]
fn bare_init_retry_after_template_publication_reaches_the_editor_without_replacing_the_file(
) -> Result<()> {
    let fixture = Fixture::new()?;
    let first = fixture.run("created", &["init"])?;
    ensure!(
        first.status.success(),
        "complete evidence: {}",
        fixture.root.display()
    );
    ensure!(String::from_utf8(first.stdout)?.contains("Created:"));
    let published = std::fs::read(&fixture.config)?;
    let parsed: toml::Value = toml::from_str(std::str::from_utf8(&published)?)?;
    ensure!(parsed.get("config_version").is_some());
    ensure!(parsed
        .get("logging")
        .and_then(|table| table.get("directory"))
        .is_some());
    let retry = fixture.run("published-retry", &["init"])?;
    ensure!(
        retry.status.success(),
        "complete evidence: {}",
        fixture.root.display()
    );
    ensure!(String::from_utf8(retry.stdout)?.contains("Opening existing configuration:"));
    ensure!(std::fs::read(&fixture.config)? == published);
    ensure!(fixture.editor_calls()? == vec![fixture.config.clone(), fixture.config.clone()]);
    eprintln!(
        "Complete publication/retry evidence: {}",
        fixture.root.display()
    );
    Ok(())
}

#[test]
fn failed_editor_reports_the_actual_exit_and_repair_without_claiming_completion() -> Result<()> {
    let fixture = Fixture::new()?;
    let original = b"# user configuration kept by Mimir\n";
    std::fs::write(&fixture.config, original)?;
    std::fs::write(
        &fixture.editor,
        b"#!/bin/sh\nprintf '%s\\n' \"$1\" >>\"$MIMIR_INIT_EDITOR_RECORD\"\nexit 23\n",
    )?;
    let failed = fixture.run("editor-exit-23", &["init"])?;
    ensure!(!failed.status.success());
    let stderr = String::from_utf8(failed.stderr)?;
    ensure!(stderr.contains("exit status: 23"), "{stderr}");
    ensure!(
        stderr.contains(&fixture.config.display().to_string()),
        "{stderr}"
    );
    ensure!(
        stderr.contains("mimir init") && stderr.contains("EDITOR"),
        "{stderr}"
    );
    ensure!(!String::from_utf8(failed.stdout)?.contains("Restart Claude Code"));
    ensure!(std::fs::read(&fixture.config)? == original);
    ensure!(fixture.editor_calls()? == vec![fixture.config.clone()]);
    eprintln!(
        "Complete failed-editor evidence: {}",
        fixture.root.display()
    );
    Ok(())
}

#[test]
fn existing_interactive_file_requires_parent_sync_before_opening_the_editor() -> Result<()> {
    if unsafe { libc::geteuid() } == 0 {
        eprintln!(
            "Interactive-init sync fault was not exercised: root bypasses directory permissions"
        );
        return Ok(());
    }
    let mut fixture = Fixture::new()?;
    let selected = fixture.root.join("selected");
    std::fs::create_dir(&selected)?;
    fixture.config = selected.join("config.toml");
    let original = b"# preserve even an invalid existing configuration\nnot TOML\n";
    std::fs::write(&fixture.config, original)?;
    std::fs::set_permissions(&fixture.config, std::fs::Permissions::from_mode(0o600))?;
    struct RestorePermissions(PathBuf);
    impl Drop for RestorePermissions {
        fn drop(&mut self) {
            let _ = std::fs::set_permissions(&self.0, std::fs::Permissions::from_mode(0o700));
        }
    }
    let restore = RestorePermissions(selected.clone());
    // The known file remains readable, but opening its parent to acknowledge
    // directory durability is denied. All evidence stays in the outer fixture.
    std::fs::set_permissions(&selected, std::fs::Permissions::from_mode(0o100))?;
    let output = fixture.run("existing-parent-sync", &["init"])?;
    std::fs::set_permissions(&selected, std::fs::Permissions::from_mode(0o700))?;
    drop(restore);
    ensure!(!output.status.success());
    let stderr = String::from_utf8(output.stderr)?;
    ensure!(
        stderr.contains("unable to open configuration directory for synchronization"),
        "{stderr}"
    );
    ensure!(
        stderr.contains(&fixture.config.display().to_string()) && stderr.contains("mimir init"),
        "{stderr}"
    );
    ensure!(!String::from_utf8(output.stdout)?.contains("Restart Claude Code"));
    ensure!(
        !fixture.record.exists(),
        "editor was invoked before directory acknowledgement"
    );
    ensure!(std::fs::read(&fixture.config)? == original);
    eprintln!(
        "Complete interactive-init sync-refusal evidence: {}",
        fixture.root.display()
    );
    Ok(())
}
