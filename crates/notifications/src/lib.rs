//! Reusable, incident-keyed SMTP notifications for Mimir components.
//! A component supplies a short safe summary; the notifier owns delivery state.
pub mod config;
mod oauth;
mod smtp;
mod state;
#[cfg(test)]
mod tests;

use anyhow::{anyhow, ensure, Result};
use config::{Auth, EmailConfig};
use serde::{Deserialize, Serialize};
use state::StateDir;
use std::{
    collections::BTreeMap,
    future::{Future, Ready},
    path::{Path, PathBuf},
};
use uuid::Uuid;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Event {
    pub source: String,
    pub incident_key: String,
    pub status: EventStatus,
    /// Component-supplied facts safe to include in email.
    pub details: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub enum EventStatus {
    Failure {
        code: String,
        summary: String,
    },
    /// A successful unit of work while the component may still have queued work.
    Progress,
    Recovery,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Disabled,
    NotNeeded,
    Sent,
    RetryPending,
    AuthRequired,
    Unavailable,
}

/// Persistent delivery cursor for the daily digest. Dates use ISO local calendar days.
#[derive(Default, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DigestState {
    pub through_day: Option<String>,
    pub next_due: u64,
    #[serde(default)]
    pub last_attempt_failed: bool,
}

pub struct Digest {
    pub through_day: String,
    pub body: String,
}

/// The host which actually sends the email, not the origin of every database row.
pub fn computer_name() -> String {
    let mut information = std::mem::MaybeUninit::<libc::utsname>::zeroed();
    // uname fills the platform's own complete hostname field. Its ABI capacity
    // is an OS constraint, rather than a Mimir-selected output buffer size.
    if unsafe { libc::uname(information.as_mut_ptr()) } != 0 {
        return "unknown-host".into();
    }
    // Successful uname initializes every field of this C structure.
    let information = unsafe { information.assume_init() };
    let bytes: Vec<u8> = information
        .nodename
        .iter()
        .map(|byte| *byte as u8)
        .collect();
    hostname_text(&bytes).unwrap_or("unknown-host").into()
}

fn hostname_text(bytes: &[u8]) -> Option<&str> {
    std::ffi::CStr::from_bytes_until_nul(bytes)
        .ok()?
        .to_str()
        .ok()
        .filter(|name| !name.is_empty())
}

impl Outcome {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Disabled => "disabled",
            Self::NotNeeded => "not_needed",
            Self::Sent => "sent",
            Self::RetryPending => "retry_pending",
            Self::AuthRequired => "auth_required",
            Self::Unavailable => "unavailable",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum AlertKind {
    Failure,
    Recovery,
}

#[derive(Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum Delivery {
    Pending,
    Exhausted,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum AlertError {
    AuthRequired,
    Unavailable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SendFailure {
    Retryable,
    AuthRequired,
    Unavailable,
}

type NoSender = fn(lettre::Message) -> Ready<std::result::Result<(), SendFailure>>;

#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Alert {
    id: String,
    kind: AlertKind,
    source: String,
    code: String,
    summary: String,
    #[serde(default)]
    details: Option<String>,
    attempts: usize,
    next_due: u64,
    delivery: Delivery,
    #[serde(default)]
    last_error: Option<AlertError>,
}

impl Alert {
    fn new(kind: AlertKind, event: &Event, code: &str, summary: &str, _now: u64) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            kind,
            source: event.source.clone(),
            code: code.into(),
            summary: summary.into(),
            details: event.details.clone(),
            attempts: 0,
            next_due: 0,
            delivery: Delivery::Pending,
            last_error: None,
        }
    }
}

#[derive(Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Incident {
    source: String,
    incident_key: String,
    active_code: Option<String>,
    delivered_code: Option<String>,
    outbox: Option<Alert>,
}

#[derive(PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Outbox {
    schema_version: u32,
    incidents: BTreeMap<String, Incident>,
}

impl Default for Outbox {
    fn default() -> Self {
        Self {
            schema_version: 1,
            incidents: BTreeMap::new(),
        }
    }
}

fn token(value: &str) -> bool {
    !value.is_empty()
        && value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.'))
}

impl Event {
    pub fn validate(&self) -> Result<()> {
        ensure!(token(&self.source), "invalid notification source");
        ensure!(
            !self.incident_key.is_empty() && !self.incident_key.chars().any(char::is_control),
            "invalid notification incident key"
        );
        if let EventStatus::Failure { code, summary } = &self.status {
            ensure!(token(code), "invalid notification code");
            ensure!(
                !summary.trim().is_empty() && !summary.chars().any(char::is_control),
                "invalid notification summary"
            );
        }
        if let Some(details) = &self.details {
            ensure!(
                !details.is_empty()
                    && details
                        .chars()
                        .all(|character| character == '\n' || !character.is_control()),
                "invalid notification details"
            );
        }
        Ok(())
    }

    fn map_key(&self) -> String {
        mimir_json::to_string(&(&self.source, &self.incident_key)).expect("string event key")
    }
}

fn reconcile(incident: &mut Incident, event: &Event, now: u64) {
    match &event.status {
        EventStatus::Failure { code, summary } => {
            if incident.active_code.as_deref() != Some(code) {
                incident.active_code = Some(code.clone());
                incident.outbox = Some(Alert::new(AlertKind::Failure, event, code, summary, now));
            }
        }
        EventStatus::Progress => {}
        EventStatus::Recovery => {
            if incident.active_code.take().is_some() {
                incident.outbox = incident
                    .delivered_code
                    .as_deref()
                    .map(|code| Alert::new(AlertKind::Recovery, event, code, "Recovered", now));
            }
        }
    }
}

fn outcome(incident: &Incident) -> Outcome {
    match incident.outbox.as_ref() {
        Some(alert) => match alert.last_error {
            Some(AlertError::AuthRequired) => Outcome::AuthRequired,
            Some(AlertError::Unavailable) => Outcome::Unavailable,
            None => Outcome::RetryPending,
        },
        None => Outcome::NotNeeded,
    }
}

fn now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |value| value.as_secs())
}

/// Durable admission is independent of SMTP, OAuth and the sender's state lock.
/// This handle owns no lock. Each append holds only a short file-update lock.
pub struct IncomingEvents {
    path: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PendingEvent {
    pub id: String,
    pub event: Event,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct IncomingState {
    schema_version: u32,
    events: std::collections::VecDeque<PendingEvent>,
}

impl IncomingState {
    fn read(state: &StateDir) -> Result<Self> {
        let incoming: Self = state.read_incoming()?.unwrap_or_else(|| Self {
            schema_version: 1,
            events: Default::default(),
        });
        ensure!(
            incoming.schema_version == 1,
            "unsupported incoming notification version"
        );
        for pending in &incoming.events {
            pending.event.validate()?;
        }
        Ok(incoming)
    }
}

impl IncomingEvents {
    pub fn new(path: impl AsRef<Path>) -> Result<Self> {
        // Perform the same private-path checks even before the first append.
        let path = path.as_ref().to_owned();
        drop(StateDir::incoming(&path)?);
        Ok(Self { path })
    }

    pub fn enqueue(&self, event: &Event) -> Result<String> {
        event.validate()?;
        let state = StateDir::incoming(&self.path)?;
        let mut incoming = IncomingState::read(&state)?;
        let id = Uuid::new_v4().to_string();
        incoming.events.push_back(PendingEvent {
            id: id.clone(),
            event: event.clone(),
        });
        state.write_incoming(&incoming)?;
        Ok(id)
    }

    /// The watcher holds this ownership until it stops. Producers never acquire it.
    pub fn claim(&self) -> Result<EventConsumer> {
        Ok(EventConsumer {
            owner: StateDir::consumer(&self.path)?,
        })
    }
}

/// One consumer owns reconciliation and delivery. Dropping it releases ownership;
/// an unacknowledged event remains available to the next watcher.
pub struct EventConsumer {
    owner: StateDir,
}

impl EventConsumer {
    pub fn front(&self) -> Result<Option<PendingEvent>> {
        let state = StateDir::incoming(self.owner.path())?;
        Ok(IncomingState::read(&state)?.events.pop_front())
    }

    /// Call only after the event was durably reconciled into the sender's outbox.
    /// A delivery failure can still be acknowledged there: the sender retains it.
    pub fn acknowledge(&self, id: &str) -> Result<()> {
        let state = StateDir::incoming(self.owner.path())?;
        let mut incoming = IncomingState::read(&state)?;
        ensure!(
            incoming.events.front().is_some_and(|event| event.id == id),
            "incoming notification changed; read the pending event before acknowledging"
        );
        incoming.events.pop_front();
        state.write_incoming(&incoming)
    }
}

/// Owns an independent outbox lock; clients do not depend on the judge.
pub struct Notifier<'a> {
    config: &'a EmailConfig,
    state_dir: PathBuf,
}

impl<'a> Notifier<'a> {
    pub fn new(config: &'a EmailConfig, state_dir: impl AsRef<Path>) -> Result<Self> {
        config.validate()?;
        let path = state_dir.as_ref();
        ensure!(
            path.is_absolute(),
            "notification state path must be absolute"
        );
        Ok(Self {
            config,
            state_dir: path.to_owned(),
        })
    }

    pub async fn submit(&self, event: &Event) -> Result<Outcome> {
        self.submit_internal(event, now(), None::<NoSender>).await
    }

    pub fn digest_state(&self) -> Result<DigestState> {
        let state = StateDir::lock(&self.state_dir)?;
        Ok(state.read_digest()?.unwrap_or_default())
    }

    /// Save pending delivery before SMTP; advance the cursor only on acceptance.
    pub async fn send_digest(&self, digest: &Digest) -> Result<Outcome> {
        self.send_digest_at(digest, now(), None::<NoSender>).await
    }

    async fn send_digest_at<F, Fut>(
        &self,
        digest: &Digest,
        _current: u64,
        send_override: Option<F>,
    ) -> Result<Outcome>
    where
        F: FnOnce(lettre::Message) -> Fut,
        Fut: Future<Output = std::result::Result<(), SendFailure>>,
    {
        if !self.config.enabled {
            return Ok(Outcome::Disabled);
        }
        ensure!(
            digest.through_day.len() == 10
                && digest.through_day.bytes().enumerate().all(|(index, byte)| {
                    if index == 4 || index == 7 {
                        byte == b'-'
                    } else {
                        byte.is_ascii_digit()
                    }
                }),
            "invalid digest day"
        );
        let state = StateDir::lock(&self.state_dir)?;
        let mut cursor: DigestState = state.read_digest()?.unwrap_or_default();
        if cursor.through_day.as_deref() >= Some(digest.through_day.as_str()) {
            return Ok(Outcome::NotNeeded);
        }
        let message = smtp::digest_message(self.config, digest)?;
        cursor.next_due = 0;
        cursor.last_attempt_failed = true;
        state.write_digest(&cursor)?;
        let sent = match send_override {
            Some(send) => send(message).await,
            None => self.send_real(&state, message).await,
        };
        if sent.is_ok() {
            cursor.through_day = Some(digest.through_day.clone());
            cursor.next_due = 0;
            cursor.last_attempt_failed = false;
            state.write_digest(&cursor)?;
            Ok(Outcome::Sent)
        } else {
            Ok(Outcome::RetryPending)
        }
    }

    pub async fn retry_due(&self) -> Result<Vec<(String, String, Outcome)>> {
        if !self.config.enabled {
            return Ok(Vec::new());
        }
        let state = StateDir::lock(&self.state_dir)?;
        let mut outbox: Outbox = state.read()?.unwrap_or_default();
        ensure!(
            outbox.schema_version == 1,
            "unsupported notification state version"
        );
        let current = now();
        let keys: Vec<_> = outbox
            .incidents
            .iter()
            .filter(|(_, incident)| incident.outbox.is_some())
            .map(|(key, _)| key.clone())
            .collect();
        let mut outcomes = Vec::new();
        for key in keys {
            let incident = outbox
                .incidents
                .get(&key)
                .expect("selected incident exists");
            let source = incident.source.clone();
            let incident_key = incident.incident_key.clone();
            let result = self
                .attempt_with(&state, &mut outbox, &key, current, None::<NoSender>)
                .await?;
            outcomes.push((source, incident_key, result));
        }
        Ok(outcomes)
    }

    #[cfg(test)]
    async fn submit_with<F, Fut>(&self, event: &Event, current: u64, send: F) -> Result<Outcome>
    where
        F: FnOnce(lettre::Message) -> Fut,
        Fut: Future<Output = std::result::Result<(), SendFailure>>,
    {
        self.submit_internal(event, current, Some(send)).await
    }

    async fn submit_internal<F, Fut>(
        &self,
        event: &Event,
        current: u64,
        send_override: Option<F>,
    ) -> Result<Outcome>
    where
        F: FnOnce(lettre::Message) -> Fut,
        Fut: Future<Output = std::result::Result<(), SendFailure>>,
    {
        event.validate()?;
        if !self.config.enabled {
            return Ok(Outcome::Disabled);
        }
        let Some((state, mut outbox, key)) = self.reconcile_event(event, current)? else {
            return Ok(Outcome::NotNeeded);
        };
        self.attempt_with(&state, &mut outbox, &key, current, send_override)
            .await
    }

    /// Save incident changes without opening a transport. The watcher can
    /// reconcile later recovery events before it attempts pending deliveries.
    pub fn accept(&self, event: &Event) -> Result<Outcome> {
        event.validate()?;
        if !self.config.enabled {
            return Ok(Outcome::Disabled);
        }
        let Some((state, mut outbox, key)) = self.reconcile_event(event, now())? else {
            return Ok(Outcome::NotNeeded);
        };
        let incident = &outbox.incidents[&key];
        if incident.active_code.is_none()
            && incident.delivered_code.is_none()
            && incident.outbox.is_none()
        {
            outbox.incidents.remove(&key);
            state.write(&outbox)?;
            return Ok(Outcome::NotNeeded);
        }
        Ok(outcome(&outbox.incidents[&key]))
    }

    fn reconcile_event(
        &self,
        event: &Event,
        current: u64,
    ) -> Result<Option<(StateDir, Outbox, String)>> {
        let state = StateDir::lock(&self.state_dir)?;
        let mut outbox: Outbox = state.read()?.unwrap_or_default();
        ensure!(
            outbox.schema_version == 1,
            "unsupported notification state version"
        );
        let key = event.map_key();
        if !matches!(&event.status, EventStatus::Failure { .. })
            && !outbox.incidents.contains_key(&key)
        {
            return Ok(None);
        }
        let incident = outbox
            .incidents
            .entry(key.clone())
            .or_insert_with(|| Incident {
                source: event.source.clone(),
                incident_key: event.incident_key.clone(),
                ..Incident::default()
            });
        let old = incident.clone();
        reconcile(incident, event, current);
        if *incident != old {
            state.write(&outbox)?;
        }
        Ok(Some((state, outbox, key)))
    }

    async fn attempt_with<F, Fut>(
        &self,
        state: &StateDir,
        outbox: &mut Outbox,
        key: &str,
        _current: u64,
        send_override: Option<F>,
    ) -> Result<Outcome>
    where
        F: FnOnce(lettre::Message) -> Fut,
        Fut: Future<Output = std::result::Result<(), SendFailure>>,
    {
        let Some(incident) = outbox.incidents.get_mut(key) else {
            return Err(anyhow!("missing notification incident"));
        };
        let Some(alert) = incident.outbox.as_mut() else {
            if incident.active_code.is_none() && incident.delivered_code.is_none() {
                outbox.incidents.remove(key);
                state.write(outbox)?;
            }
            return Ok(Outcome::NotNeeded);
        };
        let message = smtp::message(self.config, alert)?;
        // Persist pending delivery before SMTP. Historical deadlines and exhausted
        // flags do not prevent a caller from retrying. Keep the Message-ID.
        alert.attempts = alert.attempts.saturating_add(1);
        alert.next_due = 0;
        alert.delivery = Delivery::Pending;
        state.write(outbox)?;
        let sent = match send_override {
            Some(send) => send(message).await,
            None => self.send_real(state, message).await,
        };
        let incident = outbox.incidents.get_mut(key).expect("incident exists");
        let alert = incident.outbox.as_mut().expect("alert exists");
        let result = match sent {
            Ok(()) => {
                match alert.kind {
                    AlertKind::Failure => incident.delivered_code = Some(alert.code.clone()),
                    AlertKind::Recovery => incident.delivered_code = None,
                }
                incident.outbox = None;
                Outcome::Sent
            }
            Err(SendFailure::Retryable) => {
                alert.last_error = None;
                Outcome::RetryPending
            }
            Err(SendFailure::AuthRequired) => {
                alert.last_error = Some(AlertError::AuthRequired);
                Outcome::AuthRequired
            }
            Err(SendFailure::Unavailable) => {
                alert.last_error = Some(AlertError::Unavailable);
                Outcome::Unavailable
            }
        };
        if incident.active_code.is_none()
            && incident.delivered_code.is_none()
            && incident.outbox.is_none()
        {
            outbox.incidents.remove(key);
        }
        state.write(outbox)?;
        Ok(result)
    }

    async fn send_real(
        &self,
        state: &StateDir,
        message: lettre::Message,
    ) -> std::result::Result<(), SendFailure> {
        self.send_real_with(state, message, None, None).await
    }

    async fn send_real_with(
        &self,
        state: &StateDir,
        message: lettre::Message,
        endpoint_override: Option<&str>,
        trusted_root: Option<&[u8]>,
    ) -> std::result::Result<(), SendFailure> {
        if self.config.auth != Some(Auth::Oauth2) {
            return smtp::send_with_root(self.config, message, trusted_root, None)
                .await
                .map_err(|_| SendFailure::Retryable);
        }
        let first = oauth::access_token(self.config, state, now(), false, endpoint_override)
            .await
            .map_err(map_auth_error)?;
        match smtp::send_with_root(
            self.config,
            message.clone(),
            trusted_root,
            Some(&first.value),
        )
        .await
        {
            Ok(()) => Ok(()),
            Err(smtp::SmtpFailure::Retryable) => Err(SendFailure::Retryable),
            Err(smtp::SmtpFailure::AuthRejected) => {
                oauth::invalidate_access(self.config, state).map_err(map_auth_error)?;
                if !first.cached {
                    return Err(SendFailure::AuthRequired);
                }
                let second =
                    oauth::access_token(self.config, state, now(), true, endpoint_override)
                        .await
                        .map_err(map_auth_error)?;
                match smtp::send_with_root(self.config, message, trusted_root, Some(&second.value))
                    .await
                {
                    Ok(()) => Ok(()),
                    Err(smtp::SmtpFailure::AuthRejected) => {
                        oauth::invalidate_access(self.config, state).map_err(map_auth_error)?;
                        Err(SendFailure::AuthRequired)
                    }
                    Err(smtp::SmtpFailure::Retryable) => Err(SendFailure::Retryable),
                }
            }
        }
    }
}

fn map_auth_error(error: oauth::AuthError) -> SendFailure {
    match error {
        oauth::AuthError::Retryable => SendFailure::Retryable,
        oauth::AuthError::NeedsAttention => SendFailure::AuthRequired,
        oauth::AuthError::Storage => SendFailure::Unavailable,
    }
}
