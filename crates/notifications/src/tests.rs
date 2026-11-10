use super::*;
use crate::{
    config::{Auth, EmailConfig, OAuthConfig, OAuthProvider, Tls as EmailTls},
    oauth, smtp,
};
use base64::Engine;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use tokio::net::TcpListener;
use tokio_rustls::{
    rustls::{
        pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer},
        ServerConfig,
    },
    TlsAcceptor,
};

#[derive(Clone, Copy)]
enum ServerCase {
    Accept,
    RejectRecipient,
    FailQuit,
    OAuthAccept,
    AuthReject,
}

#[derive(Debug, Default)]
struct Captured {
    data: String,
    pre_tls: Vec<String>,
    authenticated: bool,
    auth_line: Option<String>,
    accepted: bool,
    quit_seen: bool,
}

fn certificate() -> (PathBuf, Vec<u8>, Vec<u8>, Vec<u8>) {
    let dir = std::env::temp_dir().join(format!("mimir-notification-cert-{}", Uuid::new_v4()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("root.pem");
    let root_key = dir.join("root-key.pem");
    let generated = std::process::Command::new("openssl")
        .args([
            "req",
            "-x509",
            "-newkey",
            "rsa:2048",
            "-nodes",
            "-days",
            "1",
            "-subj",
            "/CN=Mimir Fixture CA",
            "-addext",
            "basicConstraints=critical,CA:TRUE",
            "-keyout",
        ])
        .arg(&root_key)
        .arg("-out")
        .arg(&root)
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "fixture certificate generation failed"
    );
    let cert = dir.join("server.pem");
    let key = dir.join("server-key.pem");
    let request = dir.join("server.csr");
    let generated = std::process::Command::new("openssl")
        .args([
            "req",
            "-new",
            "-newkey",
            "rsa:2048",
            "-nodes",
            "-subj",
            "/CN=localhost",
            "-keyout",
        ])
        .arg(&key)
        .arg("-out")
        .arg(&request)
        .output()
        .unwrap();
    assert!(generated.status.success(), "fixture server request failed");
    let extensions = dir.join("extensions.cnf");
    std::fs::write(&extensions, "subjectAltName=DNS:localhost\nbasicConstraints=critical,CA:FALSE\nkeyUsage=digitalSignature,keyEncipherment\nextendedKeyUsage=serverAuth\n").unwrap();
    let signed = std::process::Command::new("openssl")
        .args(["x509", "-req", "-in"])
        .arg(&request)
        .arg("-CA")
        .arg(&root)
        .arg("-CAkey")
        .arg(&root_key)
        .args(["-CAcreateserial", "-days", "1", "-out"])
        .arg(&cert)
        .arg("-extfile")
        .arg(&extensions)
        .output()
        .unwrap();
    assert!(signed.status.success(), "fixture server signing failed");
    let root_der = dir.join("root.der");
    let converted = std::process::Command::new("openssl")
        .args(["x509", "-in"])
        .arg(&root)
        .args(["-outform", "DER", "-out"])
        .arg(&root_der)
        .output()
        .unwrap();
    assert!(converted.status.success());
    let cert_der = dir.join("cert.der");
    let converted = std::process::Command::new("openssl")
        .args(["x509", "-in"])
        .arg(&cert)
        .args(["-outform", "DER", "-out"])
        .arg(&cert_der)
        .output()
        .unwrap();
    assert!(converted.status.success());
    let key_der = dir.join("key.der");
    let converted = std::process::Command::new("openssl")
        .args(["pkcs8", "-topk8", "-nocrypt", "-in"])
        .arg(&key)
        .args(["-outform", "DER", "-out"])
        .arg(&key_der)
        .output()
        .unwrap();
    assert!(converted.status.success());
    (
        dir,
        std::fs::read(root_der).unwrap(),
        std::fs::read(cert_der).unwrap(),
        std::fs::read(key_der).unwrap(),
    )
}

async fn read_line<S: AsyncRead + Unpin>(stream: &mut S) -> Option<String> {
    let mut bytes = Vec::new();
    loop {
        let mut one = [0];
        if stream.read_exact(&mut one).await.is_err() {
            return None;
        }
        bytes.push(one[0]);
        if one[0] == b'\n' {
            break;
        }
    }
    Some(String::from_utf8(bytes).unwrap())
}

#[tokio::test]
async fn fixture_line_keeps_complete_text_beyond_the_previous_ceiling() {
    let expected = "x".repeat(65_536) + "\n";
    let input = expected.clone() + "next\n";
    let mut stream = std::io::Cursor::new(input.into_bytes());
    assert_eq!(read_line(&mut stream).await, Some(expected));
    assert_eq!(read_line(&mut stream).await.as_deref(), Some("next\n"));
    assert_eq!(read_line(&mut stream).await, None);
}

async fn write_line<S: AsyncWrite + Unpin>(stream: &mut S, line: &str) {
    stream.write_all(line.as_bytes()).await.unwrap();
}

async fn tls_dialogue<S: AsyncRead + AsyncWrite + Unpin>(
    stream: &mut S,
    case: ServerCase,
    capture: &mut Captured,
    greeting: bool,
) {
    if greeting {
        write_line(stream, "220 localhost ESMTP\r\n").await;
    }
    let ehlo = read_line(stream).await.unwrap();
    assert!(ehlo.starts_with("EHLO "));
    write_line(
        stream,
        "250-localhost\r\n250-AUTH PLAIN LOGIN XOAUTH2\r\n250 8BITMIME\r\n",
    )
    .await;
    loop {
        let Some(line) = read_line(stream).await else {
            break;
        };
        if line.starts_with("AUTH PLAIN") {
            capture.authenticated = true;
            capture.auth_line = Some(line.clone());
            if line.trim() == "AUTH PLAIN" {
                write_line(stream, "334 \r\n").await;
                read_line(stream).await.unwrap();
            }
            write_line(stream, "235 Authentication successful\r\n").await;
        } else if line.starts_with("AUTH LOGIN") {
            capture.authenticated = true;
            capture.auth_line = Some(line.clone());
            write_line(stream, "334 VXNlcm5hbWU6\r\n").await;
            read_line(stream).await.unwrap();
            write_line(stream, "334 UGFzc3dvcmQ6\r\n").await;
            read_line(stream).await.unwrap();
            write_line(stream, "235 Authentication successful\r\n").await;
        } else if line.starts_with("AUTH XOAUTH2") {
            capture.authenticated = true;
            capture.auth_line = Some(line.clone());
            if matches!(case, ServerCase::AuthReject) {
                write_line(stream, "535 Authentication rejected\r\n").await;
            } else {
                write_line(stream, "235 Authentication successful\r\n").await;
            }
        } else if line.starts_with("MAIL FROM:") {
            write_line(stream, "250 Sender accepted\r\n").await;
        } else if line.starts_with("RCPT TO:") {
            if matches!(case, ServerCase::RejectRecipient) {
                write_line(stream, "550 Recipient refused\r\n").await;
            } else {
                write_line(stream, "250 Recipient accepted\r\n").await;
            }
        } else if line.starts_with("DATA") {
            write_line(stream, "354 End data with dot\r\n").await;
            while let Some(part) = read_line(stream).await {
                if part == ".\r\n" {
                    break;
                }
                capture.data.push_str(&part);
            }
            capture.accepted = true;
            write_line(stream, "250 Message accepted\r\n").await;
        } else if line.starts_with("QUIT") {
            capture.quit_seen = true;
            if !matches!(case, ServerCase::FailQuit) {
                write_line(stream, "221 Bye\r\n").await;
            }
            break;
        } else if line.starts_with("RSET") {
            write_line(stream, "250 Reset\r\n").await;
        } else {
            panic!("unexpected SMTP fixture command");
        }
    }
}

async fn fixture(
    mode: EmailTls,
    case: ServerCase,
    cert: Vec<u8>,
    key: Vec<u8>,
) -> (u16, tokio::task::JoinHandle<Captured>) {
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let port = listener.local_addr().unwrap().port();
    let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key));
    let server = ServerConfig::builder()
        .with_no_client_auth()
        .with_single_cert(vec![CertificateDer::from(cert)], key)
        .unwrap();
    let acceptor = TlsAcceptor::from(Arc::new(server));
    let task = tokio::spawn(async move {
        let (mut socket, _) = listener.accept().await.unwrap();
        let mut capture = Captured::default();
        if mode == EmailTls::Starttls {
            write_line(&mut socket, "220 localhost ESMTP\r\n").await;
            let ehlo = read_line(&mut socket).await.unwrap();
            capture.pre_tls.push(ehlo);
            write_line(&mut socket, "250-localhost\r\n250 STARTTLS\r\n").await;
            let starttls = read_line(&mut socket).await.unwrap();
            capture.pre_tls.push(starttls.clone());
            assert!(starttls.starts_with("STARTTLS"));
            write_line(&mut socket, "220 Ready for TLS\r\n").await;
            if let Ok(mut tls) = acceptor.accept(socket).await {
                tls_dialogue(&mut tls, case, &mut capture, false).await;
            }
        } else if let Ok(mut tls) = acceptor.accept(socket).await {
            tls_dialogue(&mut tls, case, &mut capture, true).await;
        }
        capture
    });
    (port, task)
}

async fn oauth_fixture_twice(
    cert: Vec<u8>,
    key: Vec<u8>,
) -> (u16, tokio::task::JoinHandle<Vec<Captured>>) {
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let port = listener.local_addr().unwrap().port();
    let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key));
    let server = ServerConfig::builder()
        .with_no_client_auth()
        .with_single_cert(vec![CertificateDer::from(cert)], key)
        .unwrap();
    let acceptor = TlsAcceptor::from(Arc::new(server));
    let task = tokio::spawn(async move {
        let mut captures = Vec::new();
        for case in [ServerCase::AuthReject, ServerCase::OAuthAccept] {
            let (socket, _) = listener.accept().await.unwrap();
            let mut tls = acceptor.accept(socket).await.unwrap();
            let mut capture = Captured::default();
            tls_dialogue(&mut tls, case, &mut capture, true).await;
            captures.push(capture);
        }
        captures
    });
    (port, task)
}

fn config() -> EmailConfig {
    EmailConfig {
        enabled: true,
        host: Some("localhost".into()),
        port: Some(1),
        tls: Some(EmailTls::Starttls),
        from_address: Some("mimir@example.test".into()),
        to: vec!["owner@example.test".into()],
        username: None,
        auth: Some(Auth::None),
        password: None,
        oauth: None,
    }
}

#[test]
fn hostname_preserves_complete_os_text_without_an_alphabet_or_length_quota() {
    for name in [
        "計算機 café 💻/desk".to_owned(),
        "é".repeat(300),
        "host\r\nlabel\u{7}".to_owned(),
    ] {
        let mut bytes = name.as_bytes().to_vec();
        bytes.push(0);
        assert_eq!(hostname_text(&bytes), Some(name.as_str()));
    }
    // These are unavailable C/UTF-8 observations, rather than rejected names.
    for bytes in [&b"\0"[..], &b"\xff\0"[..], &b"not-terminated"[..]] {
        assert_eq!(hostname_text(bytes), None);
    }
}

#[test]
fn hostname_display_and_digest_identity_preserve_long_unicode() {
    use lettre::message::header::{ContentTransferEncoding, MessageId, Subject};
    let host = "計算機 café 💻/desk".repeat(40);
    let digest = Digest {
        through_day: "2026-11-10".into(),
        body: "Complete statistics\n".into(),
    };
    let message = smtp::digest_message_on(&config(), &digest, &host).unwrap();
    assert_eq!(
        message.headers().get::<Subject>().unwrap().as_ref(),
        format!("Mimir [{host}] daily statistics through 2026-11-10")
    );
    let id = message.headers().get::<MessageId>().unwrap();
    let repeated = smtp::digest_message_on(&config(), &digest, &host).unwrap();
    assert_eq!(id, repeated.headers().get::<MessageId>().unwrap());
    let encoded_host = id
        .as_ref()
        .strip_prefix("<mimir-daily-2026-11-10-")
        .unwrap()
        .strip_suffix("@mimir.local>")
        .unwrap();
    let (encoded_bytes, remainder) = encoded_host.as_bytes().as_chunks::<2>();
    assert!(remainder.is_empty());
    let decoded: Vec<u8> = encoded_bytes
        .iter()
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect();
    assert_eq!(decoded, host.as_bytes());
    assert_eq!(
        message.headers().get::<ContentTransferEncoding>(),
        Some(ContentTransferEncoding::Base64)
    );
    let formatted = String::from_utf8(message.formatted()).unwrap();
    let (_, body) = formatted.split_once("\r\n\r\n").unwrap();
    let decoded = base64::engine::general_purpose::STANDARD
        .decode(body.replace("\r\n", ""))
        .unwrap();
    assert_eq!(
        String::from_utf8(decoded).unwrap(),
        format!("Computer: {host}\r\nComplete statistics\r\n")
    );
}

#[test]
fn hostname_line_breaks_are_encoded_without_creating_mail_headers() {
    use lettre::message::header::Subject;
    let host = "計算機\r\nX-Injected: yes\u{7}";
    let event = failure("judge", "hostname-fixture", "blocked");
    let alert = Alert::new(AlertKind::Failure, &event, "blocked", "Fixture failed", 0);
    let digest = Digest {
        through_day: "2026-11-10".into(),
        body: "Complete statistics\n".into(),
    };
    for message in [
        smtp::message_on(&config(), &alert, host).unwrap(),
        smtp::digest_message_on(&config(), &digest, host).unwrap(),
    ] {
        assert!(message
            .headers()
            .get::<Subject>()
            .unwrap()
            .as_ref()
            .contains(host));
        let formatted = String::from_utf8(message.formatted()).unwrap();
        let (headers, _) = formatted.split_once("\r\n\r\n").unwrap();
        assert!(!headers
            .split("\r\n")
            .any(|line| line.starts_with("X-Injected:")));
        assert!(headers.contains("=?utf-8?b?"));
    }
}

fn directory() -> PathBuf {
    std::env::temp_dir().join(format!("mimir-notification-state-{}", Uuid::new_v4()))
}

fn failure(source: &str, incident: &str, code: &str) -> Event {
    Event {
        source: source.into(),
        incident_key: incident.into(),
        status: EventStatus::Failure {
            code: code.into(),
            summary: "Fixture failed".into(),
        },
        details: None,
    }
}

fn recovery(source: &str, incident: &str) -> Event {
    Event {
        source: source.into(),
        incident_key: incident.into(),
        status: EventStatus::Recovery,
        details: None,
    }
}

fn progress(source: &str, incident: &str) -> Event {
    Event {
        source: source.into(),
        incident_key: incident.into(),
        status: EventStatus::Progress,
        details: None,
    }
}

#[tokio::test]
async fn complete_notification_fields_reach_sender_and_survive_reopening() {
    let config = config();
    let path = std::env::temp_dir().join(format!("mimir-complete-notification-{}", Uuid::new_v4()));
    let notifier = Notifier::new(&config, &path).unwrap();
    let source = "source-component-".repeat(20);
    let incident_key = "complete-project-資料-".repeat(40);
    let code = "complete-reason-".repeat(20);
    let summary = "complete summary 資料 ".repeat(100);
    let details = format!(
        "{}\nlast-complete-notification-detail",
        "affected review details\n".repeat(50_000)
    );
    let event = Event {
        source: source.clone(),
        incident_key: incident_key.clone(),
        status: EventStatus::Failure {
            code: code.clone(),
            summary: summary.clone(),
        },
        details: Some(details.clone()),
    };
    event.validate().unwrap();
    let outcome = notifier
        .submit_with(&event, 100, |message| async move {
            let complete = String::from_utf8(message.formatted()).unwrap();
            assert!(complete.contains("last-complete-notification-detail"));
            Err(SendFailure::Retryable)
        })
        .await
        .unwrap();
    assert_eq!(outcome, Outcome::RetryPending);
    let saved: Outbox = StateDir::lock(&path).unwrap().read().unwrap().unwrap();
    let incident = &saved.incidents[&event.map_key()];
    assert_eq!(incident.source, source);
    assert_eq!(incident.incident_key, incident_key);
    let alert = incident.outbox.as_ref().unwrap();
    assert_eq!(alert.code, code);
    assert_eq!(alert.summary, summary);
    assert_eq!(alert.details.as_ref(), Some(&details));
    assert!(
        std::fs::metadata(path.join("notification-outbox.json"))
            .unwrap()
            .len()
            > 1024 * 1024
    );
    drop(saved);
    drop(notifier);
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn complete_large_daily_body_reaches_sender() {
    let config = config();
    let path = std::env::temp_dir().join(format!("mimir-complete-daily-{}", Uuid::new_v4()));
    let notifier = Notifier::new(&config, &path).unwrap();
    let digest = Digest {
        through_day: "2026-11-08".into(),
        body: format!(
            "{}final-daily-row-identifier\n",
            "daily statistics line\n".repeat(20_000)
        ),
    };
    assert!(digest.body.len() > 256 * 1024);
    let outcome = notifier
        .send_digest_at(
            &digest,
            100,
            Some(|message: lettre::Message| async move {
                let complete = String::from_utf8(message.formatted()).unwrap();
                assert_eq!(complete.matches("daily statistics line").count(), 20_000);
                assert!(complete.contains("final-daily-row-identifier"));
                Ok(())
            }),
        )
        .await
        .unwrap();
    assert_eq!(outcome, Outcome::Sent);
    assert_eq!(
        notifier.digest_state().unwrap().through_day.as_deref(),
        Some("2026-11-08")
    );
    drop(notifier);
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn independent_components_retry_restart_suppress_and_recover() {
    let config = config();
    let path = directory();
    let notifier = Notifier::new(&config, &path).unwrap();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let mut event = failure("judge", "project-a", "blocked");
    event.details = Some("Reason: model call limit reached\nDiagnostic ID: fixture".into());
    let collected = seen.clone();
    let result = notifier
        .submit_with(&event, 100, move |mail| async move {
            collected.lock().unwrap().push(mail.formatted());
            Err(SendFailure::Retryable)
        })
        .await
        .unwrap();
    assert_eq!(result, Outcome::RetryPending);
    let other = failure("mcp", "connection", "lost");
    assert_eq!(
        notifier
            .submit_with(&other, 101, |_| async { Ok(()) })
            .await
            .unwrap(),
        Outcome::Sent
    );
    let saved: Outbox = StateDir::lock(&path).unwrap().read().unwrap().unwrap();
    assert_eq!(saved.incidents.len(), 2);
    let first_id = saved.incidents[&event.map_key()]
        .outbox
        .as_ref()
        .unwrap()
        .id
        .clone();
    assert_eq!(
        saved.incidents[&other.map_key()].delivered_code.as_deref(),
        Some("lost")
    );
    drop(saved);
    drop(notifier);
    let notifier = Notifier::new(&config, &path).unwrap();
    assert_eq!(
        notifier
            .submit_with(&event, 100, |_| async { Err(SendFailure::Retryable) })
            .await
            .unwrap(),
        Outcome::RetryPending
    );
    let collected = seen.clone();
    assert_eq!(
        notifier
            .submit_with(&event, 110, move |mail| async move {
                collected.lock().unwrap().push(mail.formatted());
                Ok(())
            })
            .await
            .unwrap(),
        Outcome::Sent
    );
    {
        let messages = seen.lock().unwrap();
        assert_eq!(messages.len(), 2);
        for raw in messages.iter() {
            let message = String::from_utf8_lossy(raw);
            assert!(message.contains(&format!("Message-ID: <mimir-{first_id}@mimir.local>")));
            assert!(message.contains("Reason: model call limit reached"));
            assert!(message.contains("Diagnostic ID: fixture"));
        }
    }
    assert_eq!(
        notifier
            .submit_with(&event, 120, |_| async {
                panic!("identical failure is suppressed")
            })
            .await
            .unwrap(),
        Outcome::NotNeeded
    );
    let mut healthy = recovery("judge", "project-a");
    healthy.details = Some("Affected reviews: 1 confirmed by completed batches".into());
    assert_eq!(
        notifier
            .submit_with(&healthy, 120, |_| async { Err(SendFailure::Retryable) })
            .await
            .unwrap(),
        Outcome::RetryPending
    );
    assert_eq!(
        notifier
            .submit_with(&healthy, 130, |mail| async move {
                assert!(String::from_utf8_lossy(&mail.formatted())
                    .contains("Affected reviews: 1 confirmed by completed batches"));
                Ok(())
            })
            .await
            .unwrap(),
        Outcome::Sent
    );
    let saved: Outbox = StateDir::lock(&path).unwrap().read().unwrap().unwrap();
    assert!(!saved.incidents.contains_key(&event.map_key()));
    assert!(saved.incidents.contains_key(&other.map_key()));
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn progress_keeps_failure_incident_open_until_idle_recovery() {
    let config = config();
    let path = directory();
    let notifier = Notifier::new(&config, &path).unwrap();
    let failed = failure("judge", "all-projects", "judge_failure");
    let completed = progress("judge", "all-projects");
    let idle = recovery("judge", "all-projects");

    assert_eq!(
        notifier
            .submit_with(&completed, 100, |_| async {
                panic!("progress alone must not send")
            })
            .await
            .unwrap(),
        Outcome::NotNeeded
    );
    assert_eq!(
        notifier
            .submit_with(&failed, 101, |_| async { Ok(()) })
            .await
            .unwrap(),
        Outcome::Sent
    );
    for time in 102..1102 {
        assert_eq!(
            notifier
                .submit_with(&completed, time, |_| async {
                    panic!("completed batch must not send recovery")
                })
                .await
                .unwrap(),
            Outcome::NotNeeded
        );
        assert_eq!(
            notifier
                .submit_with(&failed, time, |_| async {
                    panic!("same failure must not send again")
                })
                .await
                .unwrap(),
            Outcome::NotNeeded
        );
    }
    let saved: Outbox = StateDir::lock(&path).unwrap().read().unwrap().unwrap();
    assert_eq!(
        saved.incidents[&failed.map_key()].active_code.as_deref(),
        Some("judge_failure")
    );
    drop(saved);
    assert_eq!(
        notifier
            .submit_with(&idle, 1102, |_| async { Ok(()) })
            .await
            .unwrap(),
        Outcome::Sent
    );
    let saved: Outbox = StateDir::lock(&path).unwrap().read().unwrap().unwrap();
    assert!(!saved.incidents.contains_key(&failed.map_key()));
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn failures_remain_retryable_and_latest_status_replaces_the_pending_alert() {
    let config = config();
    let path = directory();
    let notifier = Notifier::new(&config, &path).unwrap();
    let blocked = failure("judge", "project-a", "blocked");
    for current in [100, 110] {
        notifier
            .submit_with(&blocked, current, |_| async { Err(SendFailure::Retryable) })
            .await
            .unwrap();
    }
    assert_eq!(
        notifier
            .submit_with(&blocked, 100, |_| async { Err(SendFailure::Retryable) })
            .await
            .unwrap(),
        Outcome::RetryPending
    );
    let previous: Outbox = StateDir::lock(&path).unwrap().read().unwrap().unwrap();
    let old_id = previous.incidents[&blocked.map_key()]
        .outbox
        .as_ref()
        .unwrap()
        .id
        .clone();
    let partial = failure("judge", "project-a", "partial");
    assert_eq!(
        notifier
            .submit_with(&partial, 201, |_| async { Err(SendFailure::Retryable) })
            .await
            .unwrap(),
        Outcome::RetryPending
    );
    let updated: Outbox = StateDir::lock(&path).unwrap().read().unwrap().unwrap();
    assert_ne!(
        old_id,
        updated.incidents[&partial.map_key()]
            .outbox
            .as_ref()
            .unwrap()
            .id
    );
    assert_eq!(
        notifier
            .submit_with(&recovery("judge", "project-a"), 202, |_| async {
                panic!("unsent failure has no recovery alert")
            })
            .await
            .unwrap(),
        Outcome::NotNeeded
    );
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn loopback_starttls_and_implicit_tls_with_certificate_checks() {
    let (cert_dir, root, cert, key) = certificate();
    for mode in [EmailTls::Starttls, EmailTls::Tls] {
        let (port, server) = fixture(mode, ServerCase::Accept, cert.clone(), key.clone()).await;
        let mut config = config();
        config.tls = Some(mode);
        config.port = Some(port);
        if mode == EmailTls::Starttls {
            config.auth = Some(Auth::Password);
            config.username = Some("fixture-user".into());
            config.password = Some("fixture-password".into());
        }
        let event = failure("judge", "fixture", "blocked");
        let alert = Alert::new(AlertKind::Failure, &event, "blocked", "Fixture failed", 0);
        let result = smtp::send_with_root(
            &config,
            smtp::message(&config, &alert).unwrap(),
            Some(&root),
            None,
        )
        .await;
        let captured = server.await.unwrap();
        assert!(
            result.is_ok(),
            "SMTP fixture failed: {result:?}; {captured:?}"
        );
        assert!(captured.accepted);
        assert_eq!(captured.authenticated, mode == EmailTls::Starttls);
        assert!(captured.data.contains("Code: blocked"));
        assert!(captured
            .pre_tls
            .iter()
            .all(|line| !line.starts_with("AUTH")));
    }
    let (port, server) = fixture(
        EmailTls::Starttls,
        ServerCase::Accept,
        cert.clone(),
        key.clone(),
    )
    .await;
    let mut config = config();
    config.port = Some(port);
    let event = failure("judge", "fixture", "blocked");
    let alert = Alert::new(AlertKind::Failure, &event, "blocked", "Fixture failed", 0);
    assert!(
        smtp::send_with_root(&config, smtp::message(&config, &alert).unwrap(), None, None)
            .await
            .is_err()
    );
    let captured = server.await.unwrap();
    assert!(!captured.accepted);
    assert!(captured
        .pre_tls
        .iter()
        .all(|line| !line.starts_with("AUTH")));
    std::fs::remove_dir_all(cert_dir).unwrap();
}

#[tokio::test]
async fn digest_uses_host_and_real_loopback_smtp() {
    let (cert_dir, root, cert, key) = certificate();
    let (port, server) = fixture(EmailTls::Tls, ServerCase::Accept, cert, key).await;
    let mut config = config();
    config.tls = Some(EmailTls::Tls);
    config.port = Some(port);
    let digest = Digest {
        through_day: "2026-10-10".into(),
        body: "2026-10-10   2 reviews\nRunning total: 2\n".into(),
    };
    let message = smtp::digest_message(&config, &digest).unwrap();
    let result = smtp::send_with_root(&config, message, Some(&root), None).await;
    let captured = server.await.unwrap();
    assert!(result.is_ok(), "fixture delivery failed: {result:?}");
    assert!(captured.accepted);
    assert!(captured
        .data
        .contains(&format!("Mimir [{}] daily statistics", computer_name())));
    assert!(captured
        .data
        .contains(&format!("Computer: {}", computer_name())));
    assert!(captured.data.contains("Running total: 2"));
    std::fs::remove_dir_all(cert_dir).unwrap();
}

#[tokio::test]
async fn digest_cursor_suppresses_repeats_and_allows_immediate_failed_delivery_retry() {
    use std::os::unix::fs::PermissionsExt;
    let config = config();
    let path = directory();
    let notifier = Notifier::new(&config, &path).unwrap();
    let digest = Digest {
        through_day: "2026-10-10".into(),
        body: "Fixture statistics\n".into(),
    };
    assert_eq!(
        notifier
            .send_digest_at(
                &digest,
                100,
                Some(|_| async { Err(SendFailure::Retryable) })
            )
            .await
            .unwrap(),
        Outcome::RetryPending
    );
    let state = notifier.digest_state().unwrap();
    assert_eq!(state.next_due, 0);
    assert_eq!(state.through_day, None);
    assert!(state.last_attempt_failed);
    assert_eq!(
        std::fs::metadata(path.join("notification-digest.json"))
            .unwrap()
            .permissions()
            .mode()
            & 0o777,
        0o600
    );
    assert_eq!(
        notifier
            .send_digest_at(&digest, 100, Some(|_| async { Ok(()) }))
            .await
            .unwrap(),
        Outcome::Sent
    );
    assert_eq!(
        notifier.digest_state().unwrap().through_day.as_deref(),
        Some("2026-10-10")
    );
    assert!(!notifier.digest_state().unwrap().last_attempt_failed);
    assert_eq!(
        notifier
            .send_digest_at(&digest, 3701, Some(|_| async { panic!("duplicate") }))
            .await
            .unwrap(),
        Outcome::NotNeeded
    );
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn refused_recipient_acceptance_close_and_crash_retry() {
    let (cert_dir, root, cert, key) = certificate();
    let mut config = config();
    config.tls = Some(EmailTls::Tls);
    let event = failure("judge", "fixture", "blocked");
    let alert = Alert::new(AlertKind::Failure, &event, "blocked", "Fixture failed", 0);
    let (port, server) = fixture(
        EmailTls::Tls,
        ServerCase::RejectRecipient,
        cert.clone(),
        key.clone(),
    )
    .await;
    config.port = Some(port);
    assert!(smtp::send_with_root(
        &config,
        smtp::message(&config, &alert).unwrap(),
        Some(&root),
        None
    )
    .await
    .is_err());
    assert!(!server.await.unwrap().accepted);

    let path = directory();
    let (port, server) = fixture(
        EmailTls::Tls,
        ServerCase::FailQuit,
        cert.clone(),
        key.clone(),
    )
    .await;
    config.port = Some(port);
    let notifier = Notifier::new(&config, &path).unwrap();
    let trust = root.clone();
    let mail = &config;
    assert_eq!(
        notifier
            .submit_with(&event, 100, |message| async move {
                smtp::send_with_root(mail, message, Some(&trust), None)
                    .await
                    .map_err(|_| SendFailure::Retryable)
            })
            .await
            .unwrap(),
        Outcome::Sent
    );
    let first = server.await.unwrap();
    assert!(first.accepted);
    assert!(first.quit_seen);
    drop(notifier);

    let crash_event = failure("mcp", "fixture", "lost");
    let (port, server) =
        fixture(EmailTls::Tls, ServerCase::Accept, cert.clone(), key.clone()).await;
    config.port = Some(port);
    let notifier = Notifier::new(&config, &path).unwrap();
    let trust = root.clone();
    let mail = &config;
    assert_eq!(
        notifier
            .submit_with(&crash_event, 110, |message| async move {
                smtp::send_with_root(mail, message, Some(&trust), None)
                    .await
                    .map_err(|_| SendFailure::Retryable)?;
                Err(SendFailure::Retryable)
            })
            .await
            .unwrap(),
        Outcome::RetryPending
    );
    let second = server.await.unwrap();
    assert!(second.accepted);
    let first_id = second
        .data
        .lines()
        .find(|line| line.starts_with("Message-ID:"))
        .unwrap();
    drop(notifier);

    let (port, server) =
        fixture(EmailTls::Tls, ServerCase::Accept, cert.clone(), key.clone()).await;
    config.port = Some(port);
    let notifier = Notifier::new(&config, &path).unwrap();
    let trust = root.clone();
    let mail = &config;
    assert_eq!(
        notifier
            .submit_with(&crash_event, 120, |message| async move {
                smtp::send_with_root(mail, message, Some(&trust), None)
                    .await
                    .map_err(|_| SendFailure::Retryable)
            })
            .await
            .unwrap(),
        Outcome::Sent
    );
    let second = server.await.unwrap();
    assert!(second.accepted);
    let second_id = second
        .data
        .lines()
        .find(|line| line.starts_with("Message-ID:"))
        .unwrap();
    assert_eq!(first_id, second_id);
    std::fs::remove_dir_all(path).unwrap();
    std::fs::remove_dir_all(cert_dir).unwrap();
}

#[tokio::test]
async fn shared_outbox_lock_privacy_and_unbounded_retry() {
    use std::os::unix::fs::PermissionsExt;
    let (cert_dir, _root, cert, key) = certificate();
    let mut config = config();
    let path = directory();
    let locked = StateDir::lock(&path).unwrap();
    assert!(StateDir::lock(&path).is_err());
    assert_eq!(
        std::fs::metadata(&path).unwrap().permissions().mode() & 0o777,
        0o700
    );
    drop(locked);

    let event = failure("mcp", "transport", "unavailable");
    let notifier = Notifier::new(&config, &path).unwrap();
    assert_eq!(
        notifier
            .submit_with(&event, 1, |_| async { Err(SendFailure::Retryable) })
            .await
            .unwrap(),
        Outcome::RetryPending
    );
    let metadata = std::fs::metadata(path.join("notification-outbox.json")).unwrap();
    assert_eq!(metadata.permissions().mode() & 0o777, 0o600);
    drop(notifier);

    let (port, server) = fixture(
        EmailTls::Starttls,
        ServerCase::Accept,
        cert.clone(),
        key.clone(),
    )
    .await;
    config.port = Some(port);
    let notifier = Notifier::new(&config, &path).unwrap();
    let retried = notifier.retry_due().await.unwrap();
    assert_eq!(
        retried,
        vec![("mcp".into(), "transport".into(), Outcome::RetryPending)]
    );
    assert!(!server.await.unwrap().accepted); // untrusted local certificate
    let saved: Outbox = StateDir::lock(&path).unwrap().read().unwrap().unwrap();
    let incident = &saved.incidents[&event.map_key()];
    assert_eq!(incident.outbox.as_ref().unwrap().attempts, 2);
    std::fs::remove_dir_all(path).unwrap();
    std::fs::remove_dir_all(cert_dir).unwrap();
}

fn oauth_config(provider: OAuthProvider) -> EmailConfig {
    let mut config = config();
    config.auth = Some(Auth::Oauth2);
    config.username = Some("owner@example.test".into());
    config.oauth = Some(OAuthConfig {
        provider,
        client_id: "client-one".into(),
        client_secret: Some("client-secret".into()),
        refresh_token: "initial-refresh".into(),
        tenant: (provider == OAuthProvider::Microsoft).then(|| "common".into()),
        scope: (provider == OAuthProvider::Microsoft)
            .then(|| "https://outlook.office.com/SMTP.Send offline_access".into()),
    });
    config
}

fn oauth_directory() -> PathBuf {
    std::env::temp_dir().join(format!("mimir-oauth-state-{}", Uuid::new_v4()))
}

async fn token_fixture(
    status: &'static str,
    reply: impl Into<String>,
) -> (String, tokio::task::JoinHandle<(String, String)>) {
    let reply = reply.into();
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let url = format!("http://{}/token", listener.local_addr().unwrap());
    let task = tokio::spawn(async move {
        let (mut socket, _) = listener.accept().await.unwrap();
        let request = read_line(&mut socket).await.unwrap();
        let mut length = None;
        loop {
            let line = read_line(&mut socket).await.unwrap();
            if line == "\r\n" {
                break;
            }
            if let Some(value) = line.to_ascii_lowercase().strip_prefix("content-length:") {
                length = Some(value.trim().parse::<usize>().unwrap());
            }
        }
        let mut body = vec![0; length.expect("token request Content-Length")];
        socket.read_exact(&mut body).await.unwrap();
        let response = format!(
            "HTTP/1.1 {status}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{reply}",
            reply.len()
        );
        socket.write_all(response.as_bytes()).await.unwrap();
        (request, String::from_utf8(body).unwrap())
    });
    (url, task)
}

#[tokio::test]
async fn all_legacy_pending_alerts_retry_without_deadlines_or_attempt_ceilings() {
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let mut config = config();
    config.port = Some(listener.local_addr().unwrap().port());
    let path = directory();
    let notifier = Notifier::new(&config, &path).unwrap();
    for number in 0..27 {
        let event = failure("judge", &format!("project-{number}"), "pending");
        assert_eq!(notifier.accept(&event).unwrap(), Outcome::RetryPending);
    }
    let state = StateDir::lock(&path).unwrap();
    let mut saved: Outbox = state.read().unwrap().unwrap();
    let original_ids: Vec<_> = saved
        .incidents
        .values()
        .map(|incident| incident.outbox.as_ref().unwrap().id.clone())
        .collect();
    for incident in saved.incidents.values_mut() {
        let alert = incident.outbox.as_mut().unwrap();
        alert.delivery = Delivery::Exhausted;
        alert.next_due = u64::MAX;
        alert.attempts = 999;
    }
    state.write(&saved).unwrap();
    drop(state);
    let server = tokio::spawn(async move {
        for _ in 0..27 {
            let (socket, _) = listener.accept().await.unwrap();
            drop(socket);
        }
    });
    let outcomes = notifier.retry_due().await.unwrap();
    server.await.unwrap();
    assert_eq!(outcomes.len(), 27);
    assert!(outcomes
        .iter()
        .all(|(_, _, outcome)| *outcome == Outcome::RetryPending));
    let saved: Outbox = StateDir::lock(&path).unwrap().read().unwrap().unwrap();
    for (incident, original_id) in saved.incidents.values().zip(original_ids) {
        let alert = incident.outbox.as_ref().unwrap();
        assert_eq!(alert.id, original_id);
        assert_eq!(alert.attempts, 1000);
        assert_eq!(alert.next_due, 0);
        assert!(alert.delivery == Delivery::Pending);
    }
    std::fs::remove_dir_all(path).unwrap();
}

#[test]
fn admission_reconciles_unsent_recovery_before_opening_a_transport() {
    let config = config();
    let path = directory();
    let notifier = Notifier::new(&config, &path).unwrap();
    assert_eq!(
        notifier
            .accept(&failure("judge", "project", "blocked"))
            .unwrap(),
        Outcome::RetryPending
    );
    assert_eq!(
        notifier.accept(&recovery("judge", "project")).unwrap(),
        Outcome::NotNeeded
    );
    let saved: Outbox = StateDir::lock(&path).unwrap().read().unwrap().unwrap();
    assert!(saved.incidents.is_empty());
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn complete_oauth_response_and_credentials_remain_valid_until_provider_expiry() {
    let mut config = oauth_config(OAuthProvider::Google);
    let oauth = config.oauth.as_mut().unwrap();
    oauth.client_id = "client".repeat(1000);
    oauth.client_secret = Some("secret".repeat(2000));
    oauth.refresh_token = "refresh".repeat(2000);
    config.validate().unwrap();
    let path = oauth_directory();
    let state = StateDir::lock(&path).unwrap();
    let access = "access".repeat(5000);
    let rotated = "rotated".repeat(2000);
    let reply = serde_json::json!({"access_token":&access,"refresh_token":&rotated,"token_type":"Bearer","expires_in":1}).to_string();
    assert!(reply.len() > 16 * 1024);
    let (url, server) = token_fixture("200 OK", reply).await;
    let first = oauth::access_token(&config, &state, 100, false, Some(&url))
        .await
        .unwrap();
    server.await.unwrap();
    assert_eq!(first.value, access);
    assert!(!first.cached);
    let cached = oauth::access_token(&config, &state, 100, false, Some("http://127.0.0.1:1"))
        .await
        .unwrap();
    assert!(cached.cached);
    assert_eq!(cached.value, access);
    let saved: serde_json::Value = state.read_oauth().unwrap().unwrap();
    assert_eq!(saved["refresh_token"], rotated);
    drop(state);
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn cancelling_stalled_oauth_releases_the_transport_and_state_lock() {
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let endpoint = format!("http://{}/token", listener.local_addr().unwrap());
    let path = oauth_directory();
    let task_path = path.clone();
    let task = tokio::spawn(async move {
        let state = StateDir::lock(&task_path).unwrap();
        oauth::access_token(
            &oauth_config(OAuthProvider::Google),
            &state,
            100,
            false,
            Some(&endpoint),
        )
        .await
    });
    let (mut socket, _) = listener.accept().await.unwrap();
    assert!(read_line(&mut socket)
        .await
        .unwrap()
        .starts_with("POST /token"));
    assert!(!task.is_finished());
    task.abort();
    assert!(matches!(task.await, Err(error) if error.is_cancelled()));
    let mut bytes = Vec::new();
    if let Err(error) = socket.read_to_end(&mut bytes).await {
        assert!(matches!(
            error.kind(),
            std::io::ErrorKind::ConnectionReset | std::io::ErrorKind::BrokenPipe
        ));
    }
    assert!(StateDir::lock(&path).is_ok());
    assert!(!path.join("notification-oauth.json").exists());
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn oauth_google_rotation_cache_expiry_and_account_change() {
    use std::os::unix::fs::PermissionsExt;
    let config = oauth_config(OAuthProvider::Google);
    config.validate().unwrap();
    let path = oauth_directory();
    let state = StateDir::lock(&path).unwrap();
    let (url, server) = token_fixture(
        "200 OK",
        r#"{"access_token":"access-one","token_type":"Bearer","expires_in":3600,"refresh_token":"rotated-refresh"}"#,
    )
    .await;
    let first = oauth::access_token(&config, &state, 100, false, Some(&url))
        .await
        .unwrap();
    assert_eq!(first.value, "access-one");
    assert!(!first.cached);
    let (request, body) = server.await.unwrap();
    assert!(request.starts_with("POST /token HTTP/1.1"));
    assert!(body.contains("refresh_token=initial-refresh"));
    assert!(body.contains("client_id=client-one"));
    assert!(!body.contains("scope="));
    let metadata = std::fs::metadata(path.join("notification-oauth.json")).unwrap();
    assert_eq!(metadata.permissions().mode() & 0o777, 0o600);
    let cached = oauth::access_token(&config, &state, 101, false, Some("http://127.0.0.1:1"))
        .await
        .unwrap();
    assert_eq!(cached.value, "access-one");
    assert!(cached.cached);
    let (url, server) = token_fixture(
        "200 OK",
        r#"{"access_token":"access-two","token_type":"Bearer","expires_in":3600}"#,
    )
    .await;
    let renewed = oauth::access_token(&config, &state, 4000, false, Some(&url))
        .await
        .unwrap();
    assert_eq!(renewed.value, "access-two");
    assert!(!renewed.cached);
    let (_, body) = server.await.unwrap();
    assert!(body.contains("refresh_token=rotated-refresh"));
    let saved: serde_json::Value = state.read_oauth().unwrap().unwrap();
    assert_eq!(saved["refresh_token"], "rotated-refresh");
    let mut changed = oauth_config(OAuthProvider::Google);
    changed.oauth.as_mut().unwrap().client_id = "different-client".into();
    let refused = oauth::access_token(&changed, &state, 4001, false, None).await;
    assert_eq!(refused.err(), Some(oauth::AuthError::NeedsAttention));
    let still_saved: serde_json::Value = state.read_oauth().unwrap().unwrap();
    assert_eq!(saved, still_saved);
    drop(state);
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn oauth_microsoft_scope_and_rotation() {
    let config = oauth_config(OAuthProvider::Microsoft);
    config.validate().unwrap();
    let path = oauth_directory();
    let state = StateDir::lock(&path).unwrap();
    let (url, server) = token_fixture(
        "200 OK",
        r#"{"access_token":"ms-access","token_type":"Bearer","expires_in":900,"refresh_token":"ms-rotated"}"#,
    )
    .await;
    let token = oauth::access_token(&config, &state, 100, false, Some(&url))
        .await
        .unwrap();
    assert_eq!(token.value, "ms-access");
    let (_, body) = server.await.unwrap();
    assert!(body.contains("scope=https%3A%2F%2Foutlook.office.com%2FSMTP.Send+offline_access"));
    let saved: serde_json::Value = state.read_oauth().unwrap().unwrap();
    assert_eq!(saved["refresh_token"], "ms-rotated");
    let mut changed = oauth_config(OAuthProvider::Microsoft);
    changed.oauth.as_mut().unwrap().tenant = Some("organizations".into());
    let refused = oauth::access_token(&changed, &state, 101, false, None).await;
    assert_eq!(refused.err(), Some(oauth::AuthError::NeedsAttention));
    drop(state);
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn oauth_revocation_malformed_reply_and_redacted_errors() {
    let config = oauth_config(OAuthProvider::Google);
    let path = oauth_directory();
    let state = StateDir::lock(&path).unwrap();
    for (status, reply, expected) in [
        (
            "400 Bad Request",
            r#"{"error":"invalid_grant","error_description":"private-provider-detail"}"#,
            oauth::AuthError::NeedsAttention,
        ),
        (
            "200 OK",
            r#"{"access_token":"bad\nprivate-token","token_type":"Bearer","expires_in":3600}"#,
            oauth::AuthError::NeedsAttention,
        ),
        (
            "500 Server Error",
            r#"{"error":"server_error","detail":"private-server-detail"}"#,
            oauth::AuthError::Retryable,
        ),
        (
            "401 Unauthorized",
            r#"{"error":"interaction_required","detail":"private-consent-detail"}"#,
            oauth::AuthError::NeedsAttention,
        ),
    ] {
        let (url, server) = token_fixture(status, reply).await;
        let error = oauth::access_token(&config, &state, 100, false, Some(&url))
            .await
            .err()
            .unwrap();
        assert_eq!(error, expected);
        let displayed = format!("{error:?}");
        assert!(!displayed.contains("private"));
        server.await.unwrap();
        let saved: Option<serde_json::Value> = state.read_oauth().unwrap();
        assert!(saved.is_none());
    }
    drop(state);
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn oauth_interrupted_rotation_keeps_previous_token() {
    use std::os::unix::fs::PermissionsExt;
    let config = oauth_config(OAuthProvider::Google);
    let path = oauth_directory();
    let state = StateDir::lock(&path).unwrap();
    let (url, server) = token_fixture(
        "200 OK",
        r#"{"access_token":"first","token_type":"Bearer","expires_in":1,"refresh_token":"first-rotated"}"#,
    )
    .await;
    oauth::access_token(&config, &state, 100, false, Some(&url))
        .await
        .unwrap();
    server.await.unwrap();
    let before: serde_json::Value = state.read_oauth().unwrap().unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o500)).unwrap();
    let (url, server) = token_fixture(
        "200 OK",
        r#"{"access_token":"second","token_type":"Bearer","expires_in":3600,"refresh_token":"second-rotated"}"#,
    )
    .await;
    let result = oauth::access_token(&config, &state, 102, false, Some(&url)).await;
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
    server.await.unwrap();
    assert_eq!(result.err(), Some(oauth::AuthError::Storage));
    let after: serde_json::Value = state.read_oauth().unwrap().unwrap();
    assert_eq!(before, after);
    drop(state);
    std::fs::remove_dir_all(path).unwrap();
}

#[tokio::test]
async fn oauth_smtp_uses_xoauth2_and_rejection_invalidates_access_only() {
    let (cert_dir, root, cert, key) = certificate();
    let mut config = oauth_config(OAuthProvider::Google);
    config.host = Some("localhost".into());
    config.tls = Some(EmailTls::Tls);
    let event = failure("judge", "fixture", "blocked");
    let alert = Alert::new(AlertKind::Failure, &event, "blocked", "Fixture failed", 0);
    let (port, server) = fixture(
        EmailTls::Tls,
        ServerCase::OAuthAccept,
        cert.clone(),
        key.clone(),
    )
    .await;
    config.port = Some(port);
    smtp::send_with_root(
        &config,
        smtp::message(&config, &alert).unwrap(),
        Some(&root),
        Some("access-fixture"),
    )
    .await
    .unwrap();
    let captured = server.await.unwrap();
    assert!(captured.accepted);
    let auth_line = captured.auth_line.unwrap();
    let encoded = auth_line.split_whitespace().nth(2).unwrap();
    let decoded = base64::engine::general_purpose::STANDARD
        .decode(encoded)
        .unwrap();
    assert_eq!(
        decoded,
        b"user=owner@example.test\x01auth=Bearer access-fixture\x01\x01"
    );

    let path = oauth_directory();
    let (url, token_server) = token_fixture(
        "200 OK",
        r#"{"access_token":"rejected-access","token_type":"Bearer","expires_in":3600,"refresh_token":"rotated-refresh"}"#,
    )
    .await;
    let (port, mail_server) = fixture(EmailTls::Tls, ServerCase::AuthReject, cert, key).await;
    config.port = Some(port);
    let notifier = Notifier::new(&config, &path).unwrap();
    let state = StateDir::lock(&path).unwrap();
    let result = notifier
        .send_real_with(
            &state,
            smtp::message(&config, &alert).unwrap(),
            Some(&url),
            Some(&root),
        )
        .await;
    assert_eq!(result, Err(SendFailure::AuthRequired));
    token_server.await.unwrap();
    let rejected = mail_server.await.unwrap();
    assert!(!rejected.accepted);
    let saved: serde_json::Value = state.read_oauth().unwrap().unwrap();
    assert_eq!(saved["refresh_token"], "rotated-refresh");
    assert!(saved["access_token"].is_null());
    drop(state);
    std::fs::remove_dir_all(path).unwrap();
    std::fs::remove_dir_all(cert_dir).unwrap();
}

#[tokio::test]
async fn oauth_rejected_cached_access_refreshes_once_and_sends() {
    let (cert_dir, root, cert, key) = certificate();
    let mut config = oauth_config(OAuthProvider::Google);
    config.host = Some("localhost".into());
    config.tls = Some(EmailTls::Tls);
    let path = oauth_directory();
    let state = StateDir::lock(&path).unwrap();
    let (url, first_server) = token_fixture(
        "200 OK",
        r#"{"access_token":"stale-access","token_type":"Bearer","expires_in":3600,"refresh_token":"first-rotated"}"#,
    )
    .await;
    oauth::access_token(&config, &state, now(), false, Some(&url))
        .await
        .unwrap();
    first_server.await.unwrap();
    let (url, second_server) = token_fixture(
        "200 OK",
        r#"{"access_token":"fresh-access","token_type":"Bearer","expires_in":3600,"refresh_token":"second-rotated"}"#,
    )
    .await;
    let (port, smtp_server) = oauth_fixture_twice(cert, key).await;
    config.port = Some(port);
    let notifier = Notifier::new(&config, &path).unwrap();
    let event = failure("judge", "fixture", "blocked");
    let alert = Alert::new(AlertKind::Failure, &event, "blocked", "Fixture failed", 0);
    assert_eq!(
        notifier
            .send_real_with(
                &state,
                smtp::message(&config, &alert).unwrap(),
                Some(&url),
                Some(&root),
            )
            .await,
        Ok(())
    );
    let (_, body) = second_server.await.unwrap();
    assert!(body.contains("refresh_token=first-rotated"));
    let captures = smtp_server.await.unwrap();
    assert_eq!(captures.len(), 2);
    assert!(!captures[0].accepted);
    assert!(captures[1].accepted);
    for (capture, expected) in captures.iter().zip(["stale-access", "fresh-access"]) {
        let encoded = capture
            .auth_line
            .as_deref()
            .unwrap()
            .split_whitespace()
            .nth(2)
            .unwrap();
        let decoded = base64::engine::general_purpose::STANDARD
            .decode(encoded)
            .unwrap();
        assert!(String::from_utf8(decoded).unwrap().contains(expected));
    }
    let saved: serde_json::Value = state.read_oauth().unwrap().unwrap();
    assert_eq!(saved["refresh_token"], "second-rotated");
    assert_eq!(saved["access_token"], "fresh-access");
    drop(state);
    std::fs::remove_dir_all(path).unwrap();
    std::fs::remove_dir_all(cert_dir).unwrap();
}

#[tokio::test]
async fn oauth_attention_is_preserved_on_an_immediate_explicit_retry() {
    let config = oauth_config(OAuthProvider::Google);
    let path = oauth_directory();
    let notifier = Notifier::new(&config, &path).unwrap();
    let event = failure("judge", "project-a", "blocked");
    assert_eq!(
        notifier
            .submit_with(&event, 100, |_| async { Err(SendFailure::AuthRequired) })
            .await
            .unwrap(),
        Outcome::AuthRequired
    );
    assert_eq!(
        notifier
            .submit_with(&event, 100, |_| async { Err(SendFailure::AuthRequired) })
            .await
            .unwrap(),
        Outcome::AuthRequired
    );
    let saved: Outbox = StateDir::lock(&path).unwrap().read().unwrap().unwrap();
    let alert = saved.incidents[&event.map_key()].outbox.as_ref().unwrap();
    assert_eq!(alert.last_error, Some(AlertError::AuthRequired));
    assert_eq!(alert.attempts, 2);
    std::fs::remove_dir_all(path).unwrap();
}
