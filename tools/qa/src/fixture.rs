use anyhow::{bail, ensure, Context, Result};
use serde_json::Value;
use std::{env, fs, os::unix::fs::PermissionsExt, path::Path};

fn var(name: &str) -> Result<String> {
    env::var(name).with_context(|| format!("missing fixture setting {name}"))
}

fn field<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .with_context(|| format!("missing manifest field {key}"))
}

pub fn check() -> Result<()> {
    let root_text = var("MIMIR_TEST_ROOT")?;
    let root = Path::new(&root_text);
    let meta = fs::symlink_metadata(root).context("fixture root")?;
    ensure!(
        root.is_absolute()
            && meta.is_dir()
            && !meta.file_type().is_symlink()
            && meta.permissions().mode() & 0o077 == 0,
        "test root must be a private absolute directory"
    );
    let data: Value = serde_json::from_slice(&fs::read(root.join("fixture.json"))?)?;
    let token = field(&data, "token")?;
    let database = field(&data, "database")?;
    let user = field(&data, "user")?;
    ensure!(
        Path::new(field(&data, "mimir")?) == root.join("target/debug/mimir")
            && Path::new(field(&data, "mcp")?) == root.join("target/debug/mimir-mcp"),
        "fixture binaries must belong to the private test root"
    );
    let port = data
        .get("port")
        .and_then(Value::as_u64)
        .context("invalid fixture port")?;
    ensure!(
        field(&data, "root")? == root_text && token == var("MIMIR_TEST_TOKEN")?,
        "fixture ownership mismatch"
    );
    ensure!(
        database.starts_with("mimir_learning_test_")
            && user.starts_with("mimir_test_")
            && (1..65536).contains(&port),
        "invalid isolated test connection"
    );
    let expected = [
        ("MIMIR_HOST", "127.0.0.1".to_string()),
        ("MIMIR_PORT", port.to_string()),
        ("MIMIR_DBNAME", database.to_string()),
        ("MIMIR_USER", user.to_string()),
        (
            "MIMIR_CONFIG",
            root.join("config.toml").display().to_string(),
        ),
        (
            "MIMIR_TEST_CONFIG",
            root.join("config.toml").display().to_string(),
        ),
        ("PGPASSFILE", root.join("test.pgpass").display().to_string()),
        ("MIMIR_TEST_MIMIR", field(&data, "mimir")?.to_string()),
        ("MIMIR_TEST_MCP", field(&data, "mcp")?.to_string()),
    ];
    for (key, value) in expected {
        ensure!(
            var(key)? == value,
            "fixture connection/configuration differs: {key}"
        );
    }
    for key in ["PGPASSWORD", "PGSERVICE", "PGSERVICEFILE", "DATABASE_URL"] {
        ensure!(
            env::var(key).unwrap_or_default().is_empty(),
            "inherited database settings are forbidden: {key}"
        );
    }
    for name in ["config.toml", "database.toml", "test.pgpass"] {
        let meta = fs::symlink_metadata(root.join(name))?;
        ensure!(
            meta.is_file()
                && !meta.file_type().is_symlink()
                && meta.permissions().mode() & 0o077 == 0,
            "fixture files must be private regular files"
        );
    }
    let config: toml::Value = toml::from_str(&fs::read_to_string(root.join("config.toml"))?)?;
    ensure!(
        config
            .get("config_version")
            .and_then(toml::Value::as_integer)
            == Some(1),
        "fixture config version"
    );
    let db = config
        .get("database")
        .and_then(toml::Value::as_table)
        .context("fixture database configuration")?;
    for (key, expected) in [("host", "127.0.0.1"), ("dbname", database), ("user", user)] {
        ensure!(
            db.get(key).and_then(toml::Value::as_str) == Some(expected),
            "fixture configuration differs: {key}"
        );
    }
    ensure!(
        db.get("port").and_then(toml::Value::as_integer) == Some(port as i64),
        "fixture configuration differs: port"
    );
    ensure!(
        db.get("pgpassfile").and_then(toml::Value::as_str)
            == Some(root.join("test.pgpass").to_string_lossy().as_ref()),
        "fixture configuration differs: pgpassfile"
    );
    if db.contains_key("password") {
        bail!("fixture configuration must not contain a password");
    }
    Ok(())
}
