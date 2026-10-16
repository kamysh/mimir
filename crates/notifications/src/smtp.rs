use crate::{
    computer_name,
    config::{Auth, EmailConfig, Tls as EmailTls},
    Alert, AlertKind, Digest,
};
use anyhow::{anyhow, Result};
use lettre::{
    message::header::ContentType,
    transport::smtp::authentication::{Credentials, Mechanism},
    AsyncSmtpTransport, AsyncTransport, Message, Tokio1Executor,
};
use std::time::Duration;

pub(crate) fn message(config: &EmailConfig, alert: &Alert) -> Result<Message> {
    let from = config
        .from_address
        .as_deref()
        .ok_or_else(|| anyhow!("missing mail sender"))?;
    let computer = computer_name();
    let mut builder = Message::builder()
        .from(from.parse().map_err(|_| anyhow!("invalid mail sender"))?)
        .subject(match alert.kind {
            AlertKind::Failure => format!("Mimir [{computer}] notification: attention needed"),
            AlertKind::Recovery => format!("Mimir [{computer}] notification: recovered"),
        })
        .message_id(Some(format!("<mimir-{}@mimir.local>", alert.id)))
        .header(ContentType::TEXT_PLAIN);
    for recipient in &config.to {
        builder = builder.to(recipient
            .parse()
            .map_err(|_| anyhow!("invalid mail recipient"))?);
    }
    let details = alert
        .details
        .as_deref()
        .unwrap_or("Inspect the local component status for details.");
    let body = match alert.kind {
        AlertKind::Failure => format!(
            "Mimir reported a failure.\nComputer: {}\nSource: {}\nCode: {}\nSummary: {}\n\n{}\n",
            computer, alert.source, alert.code, alert.summary, details
        ),
        AlertKind::Recovery => format!(
            "Mimir reported recovery.\nComputer: {}\nSource: {}\n\n{}\n",
            computer, alert.source, details
        ),
    };
    builder
        .body(body)
        .map_err(|_| anyhow!("unable to construct notification"))
}

pub(crate) fn digest_message(config: &EmailConfig, digest: &Digest) -> Result<Message> {
    let from = config
        .from_address
        .as_deref()
        .ok_or_else(|| anyhow!("missing mail sender"))?;
    let computer = computer_name();
    let mut builder = Message::builder()
        .from(from.parse().map_err(|_| anyhow!("invalid mail sender"))?)
        .subject(format!(
            "Mimir [{computer}] daily statistics through {}",
            digest.through_day
        ))
        .message_id(Some(format!(
            "<mimir-daily-{}-{}@mimir.local>",
            digest.through_day, computer
        )))
        .header(ContentType::TEXT_PLAIN);
    for recipient in &config.to {
        builder = builder.to(recipient
            .parse()
            .map_err(|_| anyhow!("invalid mail recipient"))?);
    }
    builder
        .body(format!("Computer: {computer}\n{}", digest.body))
        .map_err(|_| anyhow!("unable to construct digest"))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SmtpFailure {
    Retryable,
    AuthRejected,
}

pub(crate) async fn send_with_root(
    config: &EmailConfig,
    message: Message,
    trusted_root: Option<&[u8]>,
    oauth_token: Option<&str>,
) -> std::result::Result<(), SmtpFailure> {
    let host = config.host.as_deref().ok_or(SmtpFailure::Retryable)?;
    let transport = match config.tls.ok_or(SmtpFailure::Retryable)? {
        EmailTls::Starttls => AsyncSmtpTransport::<Tokio1Executor>::starttls_relay(host),
        EmailTls::Tls => AsyncSmtpTransport::<Tokio1Executor>::relay(host),
    }
    .map_err(|_| SmtpFailure::Retryable)?;
    let mut transport = transport
        .port(config.port.ok_or(SmtpFailure::Retryable)?)
        .timeout(Some(Duration::from_secs(config.timeout_seconds)));
    if let Some(root) = trusted_root {
        use lettre::transport::smtp::client::{Certificate, Tls, TlsParameters};
        let cert = Certificate::from_der(root.to_vec()).map_err(|_| SmtpFailure::Retryable)?;
        let params = TlsParameters::builder(host.to_owned())
            .add_root_certificate(cert)
            .build()
            .map_err(|_| SmtpFailure::Retryable)?;
        transport = transport.tls(match config.tls.expect("TLS mode checked") {
            EmailTls::Starttls => Tls::Required(params),
            EmailTls::Tls => Tls::Wrapper(params),
        });
    }
    match config.auth.ok_or(SmtpFailure::Retryable)? {
        Auth::Password => {
            transport = transport.credentials(Credentials::new(
                config.username.clone().ok_or(SmtpFailure::Retryable)?,
                config.password.clone().ok_or(SmtpFailure::Retryable)?,
            ));
        }
        Auth::None => {}
        Auth::Oauth2 => {
            transport = transport
                .credentials(Credentials::new(
                    config.username.clone().ok_or(SmtpFailure::Retryable)?,
                    oauth_token.ok_or(SmtpFailure::Retryable)?.to_owned(),
                ))
                .authentication(vec![Mechanism::Xoauth2]);
        }
    }
    tokio::time::timeout(
        Duration::from_secs(config.timeout_seconds),
        transport.build().send(message),
    )
    .await
    .map_err(|_| SmtpFailure::Retryable)?
    .map_err(|error| match error.status().map(u16::from) {
        Some(530 | 534 | 535) => SmtpFailure::AuthRejected,
        _ => SmtpFailure::Retryable,
    })?;
    Ok(())
}
