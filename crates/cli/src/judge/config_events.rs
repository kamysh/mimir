//! OS file events, not a polling clock. Re-arm on replacement or directory
//! creation, including when the configuration file does not exist yet.
use anyhow::{Context, Result};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::path::{Path, PathBuf};
use tokio::io::unix::AsyncFd;

pub struct ConfigEvents {
    descriptor: AsyncFd<OwnedFd>,
    path: PathBuf,
    source: Option<Vec<u8>>,
    #[cfg(target_os = "macos")]
    _directory: std::fs::File,
}

#[cfg(test)]
mod tests {
    use super::*;
    #[tokio::test]
    async fn creation_replacement_and_removal_wake_without_polling() {
        let root = std::env::temp_dir().join(format!("mimir-file-events-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir(&root).unwrap();
        let path = root.join("config.toml");
        let mut events = ConfigEvents::new(&path).unwrap();
        std::fs::write(&path, b"first").unwrap();
        events.changed().await.unwrap();
        assert_eq!(events.source.as_deref(), Some(b"first".as_slice()));
        let replacement = root.join("replacement");
        std::fs::write(&replacement, b"corrected").unwrap();
        std::fs::rename(replacement, &path).unwrap();
        events.changed().await.unwrap();
        assert_eq!(events.source.as_deref(), Some(b"corrected".as_slice()));
        std::fs::remove_file(path).unwrap();
        events.changed().await.unwrap();
        assert_eq!(events.source, None);
        std::fs::remove_dir(root).unwrap();
    }
}

impl ConfigEvents {
    pub fn new(path: &Path) -> Result<Self> {
        let mut parent = path
            .parent()
            .context("configuration has no parent directory")?;
        while !parent.exists() {
            parent = parent
                .parent()
                .context("configuration has no existing ancestor")?;
        }
        #[cfg(target_os = "linux")]
        let descriptor = {
            use std::os::unix::ffi::OsStrExt;
            let raw = unsafe { libc::inotify_init1(libc::IN_NONBLOCK | libc::IN_CLOEXEC) };
            if raw < 0 {
                return Err(std::io::Error::last_os_error().into());
            }
            let descriptor = unsafe { OwnedFd::from_raw_fd(raw) };
            let name = std::ffi::CString::new(parent.as_os_str().as_bytes())?;
            let watched = unsafe {
                libc::inotify_add_watch(
                    raw,
                    name.as_ptr(),
                    libc::IN_CLOSE_WRITE
                        | libc::IN_MOVED_TO
                        | libc::IN_CREATE
                        | libc::IN_DELETE
                        | libc::IN_MOVE_SELF
                        | libc::IN_DELETE_SELF,
                )
            };
            if watched < 0 {
                return Err(std::io::Error::last_os_error().into());
            }
            descriptor
        };
        #[cfg(target_os = "macos")]
        let directory = std::fs::File::open(parent)?;
        #[cfg(target_os = "macos")]
        let descriptor = {
            let raw = unsafe { libc::kqueue() };
            if raw < 0 {
                return Err(std::io::Error::last_os_error().into());
            }
            let descriptor = unsafe { OwnedFd::from_raw_fd(raw) };
            let event = libc::kevent {
                ident: directory.as_raw_fd() as _,
                filter: libc::EVFILT_VNODE,
                flags: libc::EV_ADD | libc::EV_CLEAR,
                fflags: libc::NOTE_WRITE | libc::NOTE_RENAME | libc::NOTE_DELETE,
                data: 0,
                udata: std::ptr::null_mut(),
            };
            if unsafe { libc::kevent(raw, &event, 1, std::ptr::null_mut(), 0, std::ptr::null()) }
                < 0
            {
                return Err(std::io::Error::last_os_error().into());
            }
            descriptor
        };
        Ok(Self {
            // OwnedFd remains owned by AsyncFd for its entire registration.
            descriptor: unsafe { AsyncFd::register(descriptor) }?,
            path: path.into(),
            source: std::fs::read(path).ok(),
            #[cfg(target_os = "macos")]
            _directory: directory,
        })
    }

    pub async fn changed(&mut self) -> Result<()> {
        loop {
            let mut ready = self.descriptor.readable().await?;
            let result = ready.try_io(|descriptor| {
                #[cfg(target_os = "linux")]
                let count = {
                    let mut bytes = [0u8; 16384];
                    unsafe {
                        libc::read(
                            descriptor.as_raw_fd(),
                            bytes.as_mut_ptr().cast(),
                            bytes.len(),
                        )
                    }
                };
                #[cfg(target_os = "macos")]
                let count = {
                    let mut event = std::mem::MaybeUninit::<libc::kevent>::uninit();
                    let immediate = libc::timespec {
                        tv_sec: 0,
                        tv_nsec: 0,
                    };
                    unsafe {
                        libc::kevent(
                            descriptor.as_raw_fd(),
                            std::ptr::null(),
                            0,
                            event.as_mut_ptr(),
                            1,
                            &immediate,
                        ) as isize
                    }
                };
                if count < 0 {
                    Err(std::io::Error::last_os_error())
                } else {
                    Ok(())
                }
            });
            drop(ready);
            match result {
                Err(_) => continue,
                Ok(result) => result?,
            }
            let rearmed = Self::new(&self.path)?;
            let changed = rearmed.source != self.source;
            *self = rearmed;
            if changed {
                return Ok(());
            }
        }
    }
}
