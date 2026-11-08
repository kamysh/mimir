use super::*;
use std::os::unix::fs::symlink;
use uuid::Uuid;

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        let path =
            std::env::temp_dir().join(format!("mimir-notification-persistence-{}", Uuid::new_v4()));
        fs::create_dir(&path).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        Self(path)
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn queued_event(status: crate::EventStatus) -> crate::Event {
    crate::Event {
        source: "judge".into(),
        incident_key: "review batch".into(),
        status,
        details: Some("complete affected work and repair instructions".into()),
    }
}

#[test]
fn incoming_events_survive_restart_while_sender_lock_is_held() {
    let directory = Directory::new();
    let sender = StateDir::lock(&directory.0).unwrap();
    let event = queued_event(crate::EventStatus::Failure {
        code: "review_incomplete".into(),
        summary: "Review needs attention".into(),
    });
    let queue = crate::IncomingEvents::new(&directory.0).unwrap();
    let id = queue.enqueue(&event).unwrap();
    drop(queue);
    let reopened = crate::IncomingEvents::new(&directory.0).unwrap();
    let consumer = reopened.claim().unwrap();
    assert_eq!(
        consumer.front().unwrap(),
        Some(crate::PendingEvent { id, event })
    );
    assert_eq!(
        fs::metadata(directory.0.join(INCOMING_FILE))
            .unwrap()
            .permissions()
            .mode()
            & 0o777,
        0o600
    );
    drop(sender);
}

#[test]
fn incoming_acknowledgement_preserves_concurrent_appends_and_event_order() {
    let directory = Directory::new();
    let queue = crate::IncomingEvents::new(&directory.0).unwrap();
    let first = queued_event(crate::EventStatus::Progress);
    let first_id = queue.enqueue(&first).unwrap();
    let consumer = queue.claim().unwrap();
    assert_eq!(consumer.front().unwrap().unwrap().id, first_id);
    let later = queued_event(crate::EventStatus::Recovery);
    let later_id = queue.enqueue(&later).unwrap();
    let before = fs::read(directory.0.join(INCOMING_FILE)).unwrap();
    assert!(consumer.acknowledge(&later_id).is_err());
    assert_eq!(fs::read(directory.0.join(INCOMING_FILE)).unwrap(), before);
    consumer.acknowledge(&first_id).unwrap();
    assert_eq!(
        consumer.front().unwrap(),
        Some(crate::PendingEvent {
            id: later_id.clone(),
            event: later
        })
    );
    consumer.acknowledge(&later_id).unwrap();
    assert!(consumer.front().unwrap().is_none());
}

#[test]
fn incoming_consumer_ownership_releases_without_losing_unacknowledged_work() {
    let directory = Directory::new();
    let queue = crate::IncomingEvents::new(&directory.0).unwrap();
    let id = queue
        .enqueue(&queued_event(crate::EventStatus::Progress))
        .unwrap();
    let first = queue.claim().unwrap();
    assert!(queue.claim().is_err());
    drop(first);
    let second = queue.claim().unwrap();
    assert_eq!(second.front().unwrap().unwrap().id, id);
}

#[test]
fn incoming_invalid_event_and_unknown_version_preserve_existing_file() {
    let directory = Directory::new();
    let queue = crate::IncomingEvents::new(&directory.0).unwrap();
    queue
        .enqueue(&queued_event(crate::EventStatus::Progress))
        .unwrap();
    let mut invalid = queued_event(crate::EventStatus::Recovery);
    invalid.source = "invalid source".into();
    let file = directory.0.join(INCOMING_FILE);
    let before = fs::read(&file).unwrap();
    assert!(queue.enqueue(&invalid).is_err());
    assert_eq!(fs::read(&file).unwrap(), before);
    let mut stored: serde_json::Value = serde_json::from_slice(&before).unwrap();
    stored["schema_version"] = 2.into();
    let bytes = serde_json::to_vec(&stored).unwrap();
    fs::write(&file, &bytes).unwrap();
    assert!(queue
        .enqueue(&queued_event(crate::EventStatus::Progress))
        .is_err());
    assert_eq!(fs::read(&file).unwrap(), bytes);
}

#[test]
fn failed_exclusive_creation_preserves_existing_file_and_symlink() {
    let directory = Directory::new();
    let temp = directory.0.join("temporary");
    let target = directory.0.join("report");
    let unrelated = directory.0.join("unrelated");
    fs::write(&target, b"previous report").unwrap();
    fs::write(&temp, b"someone else's temporary file").unwrap();
    fs::write(&unrelated, b"unrelated content").unwrap();
    let error = replace_state_file(&temp, &target, &directory.0, b"replacement").unwrap_err();
    assert_eq!(
        error.downcast_ref::<std::io::Error>().unwrap().kind(),
        std::io::ErrorKind::AlreadyExists
    );
    assert_eq!(fs::read(&temp).unwrap(), b"someone else's temporary file");
    assert_eq!(fs::read(&target).unwrap(), b"previous report");
    assert_eq!(fs::read(&unrelated).unwrap(), b"unrelated content");

    fs::remove_file(&temp).unwrap();
    symlink(&unrelated, &temp).unwrap();
    assert!(replace_state_file(&temp, &target, &directory.0, b"replacement").is_err());
    assert_eq!(fs::read_link(&temp).unwrap(), unrelated);
    assert_eq!(fs::read(&unrelated).unwrap(), b"unrelated content");
    assert_eq!(fs::read(&target).unwrap(), b"previous report");
}

#[test]
fn failed_rename_removes_only_the_created_temporary_file() {
    let directory = Directory::new();
    let temp = directory.0.join("temporary");
    let target = directory.0.join("nonempty-directory");
    fs::create_dir(&target).unwrap();
    fs::write(target.join("existing"), b"retain").unwrap();
    let unrelated = directory.0.join("another-temporary");
    fs::write(&unrelated, b"retain too").unwrap();
    assert!(replace_state_file(&temp, &target, &directory.0, b"replacement").is_err());
    assert!(!temp.exists());
    assert_eq!(fs::read(target.join("existing")).unwrap(), b"retain");
    assert_eq!(fs::read(unrelated).unwrap(), b"retain too");
}

#[test]
fn directory_open_failure_after_rename_does_not_roll_back_publication() {
    let directory = Directory::new();
    let temp = directory.0.join("temporary");
    let target = directory.0.join("report");
    fs::write(&target, b"old").unwrap();
    let error = replace_state_file(
        &temp,
        &target,
        &directory.0.join("missing"),
        b"new complete bytes",
    )
    .unwrap_err();
    assert_eq!(
        error.downcast_ref::<std::io::Error>().unwrap().kind(),
        std::io::ErrorKind::NotFound
    );
    assert!(!temp.exists());
    assert_eq!(fs::read(&target).unwrap(), b"new complete bytes");
}

#[test]
fn successful_replacement_is_private_and_replaces_the_whole_file() {
    let directory = Directory::new();
    let temp = directory.0.join("temporary");
    let target = directory.0.join("report");
    fs::write(&target, b"a much longer old report").unwrap();
    replace_state_file(&temp, &target, &directory.0, b"new").unwrap();
    assert_eq!(fs::read(&target).unwrap(), b"new");
    assert_eq!(
        fs::metadata(&target).unwrap().permissions().mode() & 0o777,
        0o600
    );
    assert!(!temp.exists());
    assert_eq!(fs::read_dir(&directory.0).unwrap().count(), 1);
}

#[test]
fn encoding_rejection_preserves_all_named_files() {
    struct Fails;
    impl Serialize for Fails {
        fn serialize<S: serde::Serializer>(&self, _: S) -> std::result::Result<S::Ok, S::Error> {
            Err(serde::ser::Error::custom("fixture serialization failure"))
        }
    }
    let directory = Directory::new();
    let state = StateDir::lock(&directory.0).unwrap();
    for name in [STATE_FILE, OAUTH_FILE, DIGEST_FILE] {
        state.write_named(name, &"original").unwrap();
        let before = fs::read(directory.0.join(name)).unwrap();
        let count = fs::read_dir(&directory.0).unwrap().count();
        assert!(state.write_named(name, &Fails).is_err());
        assert_eq!(fs::read(directory.0.join(name)).unwrap(), before);
        assert_eq!(fs::read_dir(&directory.0).unwrap().count(), count);
    }
}

#[test]
fn complete_large_named_files_survive_replacement_and_reopening() {
    let directory = Directory::new();
    let complete = format!(
        "{}last-complete-state-field",
        "λ state field ".repeat(100_000)
    );
    assert!(complete.len() > 1024 * 1024);
    {
        let state = StateDir::lock(&directory.0).unwrap();
        for name in [STATE_FILE, OAUTH_FILE, DIGEST_FILE] {
            state.write_named(name, &complete).unwrap();
        }
    }
    let reopened = StateDir::lock(&directory.0).unwrap();
    for name in [STATE_FILE, OAUTH_FILE, DIGEST_FILE] {
        assert_eq!(
            reopened.read_named::<String>(name).unwrap().as_ref(),
            Some(&complete)
        );
        assert_eq!(
            fs::metadata(directory.0.join(name))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o600
        );
    }
}

#[test]
fn all_named_files_survive_restart_without_reading_orphan_temporary_files() {
    let directory = Directory::new();
    let state = StateDir::lock(&directory.0).unwrap();
    state.write(&"outbox").unwrap();
    state.write_oauth(&"oauth").unwrap();
    state.write_digest(&"digest").unwrap();
    assert!(StateDir::lock(&directory.0).is_err());
    let orphan = directory.0.join(".notification-orphan.tmp");
    fs::write(&orphan, b"unfinished JSON {").unwrap();
    drop(state);
    let reopened = StateDir::lock(&directory.0).unwrap();
    assert_eq!(
        reopened.read::<String>().unwrap().as_deref(),
        Some("outbox")
    );
    assert_eq!(
        reopened.read_oauth::<String>().unwrap().as_deref(),
        Some("oauth")
    );
    assert_eq!(
        reopened.read_digest::<String>().unwrap().as_deref(),
        Some("digest")
    );
    assert_eq!(fs::read(&orphan).unwrap(), b"unfinished JSON {");
    for name in [STATE_FILE, OAUTH_FILE, DIGEST_FILE] {
        assert_eq!(
            fs::metadata(directory.0.join(name))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o600
        );
    }
}
