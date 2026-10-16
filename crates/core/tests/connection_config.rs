use mimir_core::config::DatabaseConfig;

#[test]
fn password_and_file_roundtrip_without_debug_disclosure() {
    let text = r#"
host = "localhost"
port = 5432
dbname = "test"
user = "tester"
password = ' secret:"quoted"\with spaces '
pgpassfile = '/private/passwords'
ssl_mode = "verify-full"
ssl_root_cert = '/private/root.pem'
ssl_client_cert = '/private/client.pem'
ssl_client_key = '/private/client.key'
"#;
    let config: DatabaseConfig = toml::from_str(text).unwrap();
    assert_eq!(
        config.password.as_deref(),
        Some(" secret:\"quoted\"\\with spaces ")
    );
    assert_eq!(config.pgpassfile.as_deref(), Some("/private/passwords"));
    let debug = format!("{config:?}");
    assert!(!debug.contains("secret"));
    assert!(debug.contains("[REDACTED]"));
    let serialized = toml::to_string(&config).unwrap();
    assert_eq!(
        config,
        toml::from_str::<DatabaseConfig>(&serialized).unwrap()
    );
}

#[test]
fn existing_configuration_needs_no_new_keys() {
    let config: DatabaseConfig =
        toml::from_str("host='localhost'\nport=5432\ndbname='test'\nuser='tester'\n").unwrap();
    assert_eq!(config.password, None);
    assert_eq!(config.pgpassfile, None);
    let serialized = toml::to_string(&config).unwrap();
    assert!(!serialized.contains("password"));
    assert!(!serialized.contains("pgpassfile"));
}
