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
    let dir = PathBuf::from(format!("/var/tmp/mimir/step9/cert-{}", Uuid::new_v4()));
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
        assert!(bytes.len() < 65536, "oversized SMTP fixture line");
        if one[0] == b'\n' {
            break;
        }
    }
    Some(String::from_utf8(bytes).unwrap())
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
        timeout_seconds: 3,
        retry_seconds: 10,
        max_attempts: 2,
    }
}

fn directory() -> PathBuf {
    PathBuf::from(format!("/var/tmp/mimir/step9/state-{}", Uuid::new_v4()))
}

fn failure(source: &str, incident: &str, code: &str) -> Event {
    Event {
        source: source.into(),
        incident_key: incident.into(),
        status: EventStatus::Failure {
            code: code.into(),
            summary: "Fixture failed".into(),
        },
    }
}

fn recovery(source: &str, incident: &str) -> Event {
    Event {
        source: source.into(),
        incident_key: incident.into(),
        status: EventStatus::Recovery,
    }
}

#[tokio::test]
async fn independent_components_retry_restart_suppress_and_recover() {
    let config = config();
    let path = directory();
    let notifier = Notifier::new(&config, &path).unwrap();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let event = failure("judge", "project-a", "blocked");
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
            .submit_with(&event, 105, |_| async { panic!("retry is not due") })
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
            assert!(String::from_utf8_lossy(raw)
                .contains(&format!("Message-ID: <mimir-{first_id}@mimir.local>")));
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
    let healthy = recovery("judge", "project-a");
    assert_eq!(
        notifier
            .submit_with(&healthy, 120, |_| async { Err(SendFailure::Retryable) })
            .await
            .unwrap(),
        Outcome::RetryPending
    );
    assert_eq!(
        notifier
            .submit_with(&healthy, 130, |_| async { Ok(()) })
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
async fn exhaustion_and_latest_status_replacement_are_per_incident() {
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
            .submit_with(&blocked, 200, |_| async {
                panic!("exhausted alert must not retry")
            })
            .await
            .unwrap(),
        Outcome::Exhausted
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
async fn shared_outbox_lock_privacy_and_due_retry() {
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
    let retried = notifier.retry_due(1).await.unwrap();
    assert_eq!(
        retried,
        vec![("mcp".into(), "transport".into(), Outcome::Exhausted)]
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
    PathBuf::from(format!("/var/tmp/mimir/step10/state-{}", Uuid::new_v4()))
}

async fn token_fixture(
    status: &'static str,
    reply: &'static str,
) -> (String, tokio::task::JoinHandle<(String, String)>) {
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
async fn oauth_attention_status_persists_until_retry_is_due() {
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
            .submit_with(&event, 105, |_| async {
                panic!("auth failure must stay visible before retry")
            })
            .await
            .unwrap(),
        Outcome::AuthRequired
    );
    let saved: Outbox = StateDir::lock(&path).unwrap().read().unwrap().unwrap();
    let alert = saved.incidents[&event.map_key()].outbox.as_ref().unwrap();
    assert_eq!(alert.last_error, Some(AlertError::AuthRequired));
    assert_eq!(alert.attempts, 1);
    std::fs::remove_dir_all(path).unwrap();
}
