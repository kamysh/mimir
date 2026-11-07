//! Owned OS file notifications; no polling interval or background worker.
use std::{
    io,
    os::unix::ffi::OsStrExt,
    path::{Path, PathBuf},
};

pub struct ConfigEvents {
    path: PathBuf,
    native: native::Watch,
}

impl ConfigEvents {
    pub fn new(path: &Path) -> io::Result<Self> {
        Ok(Self {
            path: path.to_owned(),
            native: native::Watch::new(path)?,
        })
    }

    // Install the replacement first. A change during the following config
    // load remains queued; changes preceding installation are covered by load.
    pub fn rearm(&mut self) -> io::Result<()> {
        self.native = native::Watch::new(&self.path)?;
        Ok(())
    }

    pub async fn changed(&mut self) -> io::Result<()> {
        self.native.changed().await
    }
}

fn directory_and_child(path: &Path) -> io::Result<(PathBuf, PathBuf)> {
    let mut directory = path
        .parent()
        .ok_or_else(|| io::Error::other("configuration has no parent directory"))?;
    loop {
        match std::fs::metadata(directory) {
            Ok(metadata) if metadata.is_dir() => break,
            Ok(_) => return Err(io::Error::other("configuration parent is not a directory")),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                directory = directory.parent().ok_or(error)?;
            }
            Err(error) => return Err(error),
        }
    }
    let child = path
        .strip_prefix(directory)
        .map_err(io::Error::other)?
        .components()
        .next()
        .ok_or_else(|| io::Error::other("configuration path is empty"))?;
    Ok((directory.to_owned(), directory.join(child)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::judge::harness::RunDir;
    use std::future::{poll_fn, Future};

    #[tokio::test]
    async fn observes_edits_atomic_replacements_and_recreated_parents() {
        let work = RunDir::new_in(&std::env::temp_dir()).unwrap();
        let directory = work.path().join("settings");
        std::fs::create_dir(&directory).unwrap();
        let path = directory.join("config.toml");
        std::fs::write(&path, "original").unwrap();
        let mut events = ConfigEvents::new(&path).unwrap();
        {
            let changed = events.changed();
            tokio::pin!(changed);
            assert!(
                poll_fn(|cx| std::task::Poll::Ready(changed.as_mut().poll(cx).is_pending())).await
            );
            std::fs::write(&path, "edited").unwrap();
            changed.await.unwrap();
        }

        events.rearm().unwrap();
        let replacement = directory.join("replacement");
        std::fs::write(&replacement, "replacement").unwrap();
        std::fs::rename(&replacement, &path).unwrap();
        events.changed().await.unwrap();
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "replacement");

        events.rearm().unwrap();
        std::fs::rename(&directory, work.path().join("previous-settings")).unwrap();
        events.changed().await.unwrap();
        events.rearm().unwrap();
        std::fs::create_dir(&directory).unwrap();
        events.changed().await.unwrap();
        events.rearm().unwrap();
        std::fs::write(&path, "restored").unwrap();
        events.changed().await.unwrap();
    }
}

#[cfg(target_os = "linux")]
mod native {
    use super::*;
    use std::mem::size_of;
    use std::{
        ffi::CString,
        os::fd::{AsRawFd, FromRawFd, OwnedFd},
    };
    use tokio::io::unix::AsyncFd;

    pub struct Watch {
        descriptor: AsyncFd<OwnedFd>,
        child: Vec<u8>,
    }

    impl Watch {
        pub fn new(path: &Path) -> io::Result<Self> {
            let (directory, child) = directory_and_child(path)?;
            let directory = CString::new(directory.as_os_str().as_bytes())?;
            let raw = unsafe { libc::inotify_init1(libc::IN_NONBLOCK | libc::IN_CLOEXEC) };
            if raw < 0 {
                return Err(io::Error::last_os_error());
            }
            let descriptor = unsafe { OwnedFd::from_raw_fd(raw) };
            let result = unsafe {
                libc::inotify_add_watch(
                    descriptor.as_raw_fd(),
                    directory.as_ptr(),
                    libc::IN_MODIFY
                        | libc::IN_CLOSE_WRITE
                        | libc::IN_MOVED_TO
                        | libc::IN_CREATE
                        | libc::IN_DELETE
                        | libc::IN_ATTRIB
                        | libc::IN_DELETE_SELF
                        | libc::IN_MOVE_SELF,
                )
            };
            if result < 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(Self {
                // SAFETY: OwnedFd stays owned by this private AsyncFd; no
                // caller can replace or close its registered descriptor.
                descriptor: unsafe {
                    AsyncFd::register_with_interest(descriptor, tokio::io::Interest::READABLE)?
                },
                child: child
                    .file_name()
                    .ok_or_else(|| io::Error::other("configuration has no filename"))?
                    .as_bytes()
                    .to_vec(),
            })
        }

        pub async fn changed(&mut self) -> io::Result<()> {
            loop {
                let mut ready = self.descriptor.readable().await?;
                let result = ready.try_io(|descriptor| {
                    // Transfer buffer, not an event quota. Keep reading until
                    // a relevant hint or WouldBlock; overflow also means rescan.
                    // Size for one complete kernel event, including the OS
                    // filename bound and NUL. This does not bound the loop.
                    let mut buffer =
                        [0u8; size_of::<libc::inotify_event>() + libc::NAME_MAX as usize + 1];
                    let count = unsafe {
                        libc::read(
                            descriptor.as_raw_fd(),
                            buffer.as_mut_ptr().cast(),
                            buffer.len(),
                        )
                    };
                    if count < 0 {
                        return Err(io::Error::last_os_error());
                    }
                    if count == 0 {
                        return Err(io::Error::new(
                            io::ErrorKind::UnexpectedEof,
                            "configuration event source closed",
                        ));
                    }
                    let mut offset = 0;
                    while offset + size_of::<libc::inotify_event>() <= count as usize {
                        let event = unsafe {
                            std::ptr::read_unaligned(
                                buffer.as_ptr().add(offset).cast::<libc::inotify_event>(),
                            )
                        };
                        let start = offset + size_of::<libc::inotify_event>();
                        let end = start + event.len as usize;
                        if end > count as usize {
                            return Err(io::Error::other("incomplete configuration event"));
                        }
                        let name = &buffer[start..end];
                        let name = &name[..name
                            .iter()
                            .position(|byte| *byte == 0)
                            .unwrap_or(name.len())];
                        if name == self.child
                            || event.mask
                                & (libc::IN_Q_OVERFLOW
                                    | libc::IN_IGNORED
                                    | libc::IN_DELETE_SELF
                                    | libc::IN_MOVE_SELF)
                                != 0
                        {
                            return Ok(true);
                        }
                        offset = end;
                    }
                    Ok(false)
                });
                match result {
                    Ok(Ok(true)) => return Ok(()),
                    Ok(Err(error)) => return Err(error),
                    Ok(Ok(false)) | Err(_) => (),
                }
            }
        }
    }
}

#[cfg(target_os = "macos")]
mod native {
    use super::*;
    use std::os::unix::fs::MetadataExt;
    use std::{
        ffi::CString,
        os::fd::{AsRawFd, FromRawFd, OwnedFd},
    };
    use tokio::io::unix::AsyncFd;

    fn identity(path: &Path) -> io::Result<Option<(u64, u64)>> {
        match std::fs::metadata(path) {
            Ok(metadata) => Ok(Some((metadata.dev(), metadata.ino()))),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(error),
        }
    }

    fn open(path: &Path) -> io::Result<OwnedFd> {
        let path = CString::new(path.as_os_str().as_bytes())?;
        let raw = unsafe { libc::open(path.as_ptr(), libc::O_EVTONLY | libc::O_CLOEXEC) };
        if raw < 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(unsafe { OwnedFd::from_raw_fd(raw) })
    }

    pub struct Watch {
        descriptor: AsyncFd<OwnedFd>,
        _directory: OwnedFd,
        file: Option<OwnedFd>,
        directory: PathBuf,
        directory_identity: Option<(u64, u64)>,
        child: PathBuf,
        child_identity: Option<(u64, u64)>,
    }

    impl Watch {
        pub fn new(path: &Path) -> io::Result<Self> {
            let (directory, child) = directory_and_child(path)?;
            let parent = open(&directory)?;
            let file = match open(path) {
                Ok(file) => Some(file),
                Err(error) if error.kind() == io::ErrorKind::NotFound => None,
                Err(error) => return Err(error),
            };
            let raw = unsafe { libc::kqueue() };
            if raw < 0 {
                return Err(io::Error::last_os_error());
            }
            let descriptor = unsafe { OwnedFd::from_raw_fd(raw) };
            if unsafe { libc::fcntl(descriptor.as_raw_fd(), libc::F_SETFD, libc::FD_CLOEXEC) } < 0 {
                return Err(io::Error::last_os_error());
            }
            for fd in std::iter::once(&parent).chain(file.iter()) {
                let event = libc::kevent {
                    ident: fd.as_raw_fd() as usize,
                    filter: libc::EVFILT_VNODE,
                    flags: libc::EV_ADD | libc::EV_CLEAR,
                    fflags: libc::NOTE_WRITE
                        | libc::NOTE_EXTEND
                        | libc::NOTE_ATTRIB
                        | libc::NOTE_DELETE
                        | libc::NOTE_RENAME
                        | libc::NOTE_REVOKE,
                    data: 0,
                    udata: std::ptr::null_mut(),
                };
                if unsafe {
                    libc::kevent(
                        descriptor.as_raw_fd(),
                        &event,
                        1,
                        std::ptr::null_mut(),
                        0,
                        std::ptr::null(),
                    )
                } < 0
                {
                    return Err(io::Error::last_os_error());
                }
            }
            Ok(Self {
                // SAFETY: the private OwnedFd is never replaced or closed
                // while registered; the vnode descriptors are owned here too.
                descriptor: unsafe {
                    AsyncFd::register_with_interest(descriptor, tokio::io::Interest::READABLE)?
                },
                _directory: parent,
                file,
                directory_identity: identity(&directory)?,
                child_identity: identity(&child)?,
                directory,
                child,
            })
        }

        pub async fn changed(&mut self) -> io::Result<()> {
            loop {
                let mut ready = self.descriptor.readable().await?;
                let result = ready.try_io(|descriptor| {
                    let mut event: libc::kevent = unsafe { std::mem::zeroed() };
                    let no_wait = libc::timespec {
                        tv_sec: 0,
                        tv_nsec: 0,
                    };
                    // Nonblocking queue drain, not a retry timeout. AsyncFd
                    // supplies the readiness wait without any timer.
                    let count = unsafe {
                        libc::kevent(
                            descriptor.as_raw_fd(),
                            std::ptr::null(),
                            0,
                            &mut event,
                            1,
                            &no_wait,
                        )
                    };
                    if count < 0 {
                        return Err(io::Error::last_os_error());
                    }
                    if count == 0 {
                        return Err(io::ErrorKind::WouldBlock.into());
                    }
                    if event.flags & libc::EV_ERROR != 0 {
                        return Err(io::Error::from_raw_os_error(event.data as i32));
                    }
                    Ok(self
                        .file
                        .as_ref()
                        .is_some_and(|file| file.as_raw_fd() as usize == event.ident)
                        || identity(&self.directory)? != self.directory_identity
                        || identity(&self.child)? != self.child_identity)
                });
                match result {
                    Ok(Ok(true)) => return Ok(()),
                    Ok(Err(error)) => return Err(error),
                    Ok(Ok(false)) | Err(_) => (),
                }
            }
        }
    }
}
