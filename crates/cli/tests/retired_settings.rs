//! Offline repair of retired settings preserves all unrelated user data.
use anyhow::{ensure, Result};
use std::{path::Path, process::Command};

fn run(root: &Path, name: &str, args: &[&str]) -> Result<std::process::Output> {
    let output = Command::new(env!("CARGO_BIN_EXE_mimir"))
        .env("MIMIR_CONFIG", root.join("init-only-config.toml"))
        .env("XDG_STATE_HOME", root.join("state"))
        .args(args)
        .output()?;
    std::fs::write(root.join(format!("{name}.stdout")), &output.stdout)?;
    std::fs::write(root.join(format!("{name}.stderr")), &output.stderr)?;
    std::fs::write(
        root.join(format!("{name}.exit")),
        format!("{:?}\n", output.status.code()),
    )?;
    Ok(output)
}

#[test]
fn retired_embedding_init_argument_explains_the_fix_without_creating_configuration() -> Result<()> {
    let root = std::env::temp_dir().join(format!(
        "mimir-retired-embedding-init-{}",
        uuid::Uuid::new_v4()
    ));
    std::fs::create_dir(&root)?;
    for (index, value) in ["0", "4", "private-retired-value"].into_iter().enumerate() {
        let argument = format!("batch_size={value}");
        let output = run(&root, &format!("init-{index}"), &["init", &argument])?;
        ensure!(!output.status.success());
        let diagnostic = String::from_utf8(output.stderr)?;
        ensure!(
            diagnostic.contains("embeddings.batch_size is obsolete")
                && diagnostic.contains("mimir config upgrade"),
            "{diagnostic}"
        );
        ensure!(!diagnostic.contains("private-retired-value"));
        ensure!(
            !root.join("init-only-config.toml").exists(),
            "retired argument created configuration"
        );
    }
    eprintln!("Complete init diagnostics retained at {}", root.display());
    Ok(())
}

#[test]
fn check_and_upgrade_share_retired_fields_and_preserve_user_configuration_offline() -> Result<()> {
    let root = std::env::temp_dir().join(format!("mimir-retired-config-{}", uuid::Uuid::new_v4()));
    std::fs::create_dir(&root)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o700))?;
    }
    for (index, (section, key)) in [
        ("logging", "max_file_bytes"),
        ("logging", "retained_files"),
        ("judge", "batch_size"),
        ("embeddings", "batch_size"),
        ("llm", "timeout_seconds"),
        ("llm", "max_calls"),
        ("llm", "max_output_tokens"),
        ("llm", "max_budget_usd"),
        ("email", "timeout_seconds"),
        ("email", "retry_seconds"),
        ("email", "max_attempts"),
    ]
    .into_iter()
    .enumerate()
    {
        let extra = |wanted: &str| {
            if section == wanted {
                format!("{key}='private-retired-value'\n")
            } else {
                String::new()
            }
        };
        let text=format!("config_version=1 # keep format comment\n[logging]\ndirectory={}\n{}[database]\nhost='127.0.0.1' # keep connection comment\nport=1\ndbname='offline-fixture'\nuser='fixture'\npassword='private-fixture-password'\n[embeddings]\nbackend='local'\ncache_dir='/fixture/model-cache' # preserve unrelated user setting\n{}[judge]\nproject='chosen-user-project'\n{}[llm]\nbackend='command'\nmodel='chosen-model' # preserve model comment\ncommand='/bin/true'\nargs=['one','two']\n{}[email]\nenabled=false\nusername='configured-user'\n{}[email.oauth]\nprovider='google'\nclient_id='configured-client'\nrefresh_token='private-fixture-refresh-token'\n[unrelated]\nuser_setting='preserve this'\n",toml::Value::String(root.join("logs").display().to_string()),extra("logging"),extra("embeddings"),extra("judge"),extra("llm"),extra("email"));
        let path = root.join(format!("{index}.toml"));
        std::fs::write(&path, &text)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600))?;
        }
        let path_arg = path.to_str().unwrap();
        let before = run(
            &root,
            &format!("{index}-before"),
            &["config", "check", "--config", path_arg],
        )?;
        ensure!(
            !before.status.success(),
            "retired {section}.{key} was accepted"
        );
        let diagnostic = String::from_utf8(before.stderr)?;
        ensure!(
            diagnostic.contains(&format!("{section}.{key}"))
                && diagnostic.contains("mimir config upgrade"),
            "retired field needs exact repair: {diagnostic}"
        );
        for secret in [
            "private-retired-value",
            "private-fixture-password",
            "private-fixture-refresh-token",
        ] {
            ensure!(!diagnostic.contains(secret));
        }
        let upgraded = run(
            &root,
            &format!("{index}-upgrade"),
            &["config", "upgrade", "--config", path_arg],
        )?;
        ensure!(
            upgraded.status.success(),
            "upgrade failed; logs retained at {}",
            root.display()
        );
        let first = std::fs::read_to_string(&path)?;
        let mut expected: toml::Value = toml::from_str(&text)?;
        expected[section].as_table_mut().unwrap().remove(key);
        ensure!(
            toml::from_str::<toml::Value>(&first)? == expected,
            "unrelated user value changed"
        );
        for comment in [
            "# keep format comment",
            "# keep connection comment",
            "# preserve unrelated user setting",
            "# preserve model comment",
        ] {
            ensure!(first.contains(comment), "lost unrelated comment {comment}");
        }
        let checked = run(
            &root,
            &format!("{index}-after"),
            &["config", "check", "--config", path_arg],
        )?;
        ensure!(checked.status.success());
        ensure!(
            String::from_utf8(checked.stdout)?.contains("No database or model request was made")
        );
        let repeated = run(
            &root,
            &format!("{index}-repeat"),
            &["config", "upgrade", "--config", path_arg],
        )?;
        ensure!(
            repeated.status.success() && std::fs::read_to_string(&path)? == first,
            "upgrade was not idempotent"
        );
    }
    // Email remains checkable even without any judge/model configuration.
    let path = root.join("email-only.toml");
    std::fs::write(&path,format!("config_version=1\n[logging]\ndirectory={}\n[database]\nhost='127.0.0.1'\nport=1\ndbname='offline-fixture'\nuser='fixture'\n[email]\nenabled=false\nmax_attempts=0\n",toml::Value::String(root.join("logs").display().to_string())))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600))?;
    }
    let value = run(
        &root,
        "email-only-before",
        &["config", "check", "--config", path.to_str().unwrap()],
    )?;
    ensure!(
        !value.status.success() && String::from_utf8(value.stderr)?.contains("email.max_attempts")
    );
    ensure!(run(
        &root,
        "email-only-upgrade",
        &["config", "upgrade", "--config", path.to_str().unwrap()]
    )?
    .status
    .success());
    eprintln!(
        "Complete configuration command output retained at {}",
        root.display()
    );
    Ok(())
}
