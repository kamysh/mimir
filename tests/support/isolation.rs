// Shared test-only connection guard. It never loads the installed application config.
use mimir_core::config::{DatabaseConfig, SslMode};
use serde::Deserialize;
use std::path::PathBuf;

#[derive(Deserialize)]
pub struct Fixture {
    pub root: PathBuf,
    token: String,
    database: String,
    user: String,
    port: u16,
    pub mimir: String,
    pub mcp: String,
}

pub fn fixture() -> Fixture {
    use std::os::unix::fs::PermissionsExt;
    let root =
        PathBuf::from(std::env::var("MIMIR_TEST_ROOT").expect("run scripts/test-isolated.py"));
    assert!(root.is_absolute() && !root.is_symlink());
    assert_eq!(
        std::fs::metadata(&root).unwrap().permissions().mode() & 0o077,
        0
    );
    let value: Fixture = serde_json::from_str(
        &std::fs::read_to_string(root.join("fixture.json")).expect("isolated fixture manifest"),
    )
    .expect("valid isolated fixture manifest");
    assert_eq!(value.root, root);
    assert_eq!(std::env::var("MIMIR_TEST_TOKEN").unwrap(), value.token);
    assert!(value.database.starts_with("mimir_learning_test_"));
    assert!(value.user.starts_with("mimir_test_"));
    assert_ne!(value.port, 0);
    for (key, expected) in [
        ("MIMIR_HOST", "127.0.0.1".to_owned()),
        ("MIMIR_PORT", value.port.to_string()),
        ("MIMIR_DBNAME", value.database.clone()),
        ("MIMIR_USER", value.user.clone()),
        ("PGPASSFILE", root.join("test.pgpass").display().to_string()),
        (
            "MIMIR_CONFIG",
            root.join("config.toml").display().to_string(),
        ),
        (
            "MIMIR_TEST_CONFIG",
            root.join("config.toml").display().to_string(),
        ),
        ("MIMIR_TEST_MIMIR", value.mimir.clone()),
        ("MIMIR_TEST_MCP", value.mcp.clone()),
    ] {
        assert_eq!(
            std::env::var(key).expect("isolated fixture setting required"),
            expected,
            "{key} does not match this test fixture"
        );
    }
    assert_eq!(PathBuf::from(&value.mimir), root.join("target/debug/mimir"));
    assert_eq!(
        PathBuf::from(&value.mcp),
        root.join("target/debug/mimir-mcp")
    );
    for key in ["PGPASSWORD", "PGSERVICE", "PGSERVICEFILE", "DATABASE_URL"] {
        assert!(
            std::env::var(key).unwrap_or_default().is_empty(),
            "inherited {key} is forbidden"
        );
    }
    for name in ["config.toml", "database.toml", "test.pgpass"] {
        let path = root.join(name);
        assert!(!path.is_symlink());
        assert_eq!(
            std::fs::metadata(path).unwrap().permissions().mode() & 0o077,
            0
        );
    }
    value
}

impl Fixture {
    pub fn database_config(&self) -> DatabaseConfig {
        DatabaseConfig {
            host: "127.0.0.1".into(),
            port: self.port,
            dbname: self.database.clone(),
            user: self.user.clone(),
            password: None,
            pgpassfile: Some(self.root.join("test.pgpass").display().to_string()),
            ssl_mode: SslMode::Disable,
            ssl_root_cert: None,
            ssl_client_cert: None,
            ssl_client_key: None,
        }
    }

    pub fn assert_database(&self, config: &DatabaseConfig) {
        assert_eq!(config.host, "127.0.0.1");
        assert_eq!(config.port, self.port);
        assert_eq!(config.dbname, self.database);
        assert_eq!(config.user, self.user);
        assert!(config.password.is_none());
        assert_eq!(
            config.pgpassfile,
            Some(self.root.join("test.pgpass").display().to_string())
        );
    }
}
