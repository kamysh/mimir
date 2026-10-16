//! Shared certificate validation for every database connection.
use crate::config::SslMode;
use anyhow::{Context, Result};
use postgres_native_tls::MakeTlsConnector;

pub(crate) fn connector(
    mode: &SslMode,
    root: Option<&str>,
    cert: Option<&str>,
    key: Option<&str>,
) -> Result<MakeTlsConnector> {
    anyhow::ensure!(
        cert.is_some() == key.is_some(),
        "ssl_client_cert and ssl_client_key must be supplied together"
    );
    anyhow::ensure!(
        *mode != SslMode::Disable || (root.is_none() && cert.is_none()),
        "TLS certificate options cannot be used with ssl_mode=disable"
    );
    let mut builder = native_tls::TlsConnector::builder();
    match mode {
        SslMode::Prefer | SslMode::Require => {
            builder.danger_accept_invalid_certs(true);
            builder.danger_accept_invalid_hostnames(true);
        }
        SslMode::VerifyCa => {
            builder.danger_accept_invalid_hostnames(true);
        }
        _ => {}
    }
    if let Some(path) = root {
        let pem = std::fs::read_to_string(path).context("cannot read ssl_root_cert")?;
        let mut count = 0;
        for block in pem.split_inclusive("-----END CERTIFICATE-----") {
            if block.trim().is_empty() {
                continue;
            }
            builder.add_root_certificate(
                native_tls::Certificate::from_pem(block.as_bytes())
                    .context("invalid ssl_root_cert PEM certificate")?,
            );
            count += 1;
        }
        anyhow::ensure!(count > 0, "ssl_root_cert contains no certificates");
        builder.disable_built_in_roots(true);
    }
    if let (Some(cert), Some(key)) = (cert, key) {
        builder.identity(
            native_tls::Identity::from_pkcs8(
                &std::fs::read(cert).context("cannot read ssl_client_cert")?,
                &std::fs::read(key).context("cannot read ssl_client_key")?,
            )
            .context("invalid client certificate or unencrypted PKCS#8 key")?,
        );
    }
    Ok(MakeTlsConnector::new(builder.build()?))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn partial_identities_and_disabled_certificate_options_are_errors() {
        for (mode, root, cert, key) in [
            (SslMode::Require, None, Some("cert"), None),
            (SslMode::Require, None, None, Some("key")),
            (SslMode::Disable, Some("ca"), None, None),
            (SslMode::Disable, None, Some("cert"), Some("key")),
        ] {
            assert!(connector(&mode, root, cert, key).is_err());
        }
    }
}
