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
fn encoding_and_size_rejection_preserve_all_named_files() {
    struct Fails;
    impl Serialize for Fails {
        fn serialize<S: serde::Serializer>(&self, _: S) -> std::result::Result<S::Ok, S::Error> {
            Err(serde::ser::Error::custom("fixture serialization failure"))
        }
    }
    let directory = Directory::new();
    let state = StateDir::lock(&directory.0).unwrap();
    let oversized = "x".repeat(MAX_STATE as usize);
    for name in [STATE_FILE, OAUTH_FILE, DIGEST_FILE] {
        state.write_named(name, &"original").unwrap();
        let before = fs::read(directory.0.join(name)).unwrap();
        let count = fs::read_dir(&directory.0).unwrap().count();
        assert!(state.write_named(name, &Fails).is_err());
        assert!(state.write_named(name, &oversized).is_err());
        assert_eq!(fs::read(directory.0.join(name)).unwrap(), before);
        assert_eq!(fs::read_dir(&directory.0).unwrap().count(), count);
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
