//! Blocking evaluation children: complete output, no deadline, explicit cancellation.
use anyhow::{Context, Result};
use std::io::{Read, Write};
use std::os::unix::process::CommandExt;
use std::process::{Command, Output, Stdio};
use std::thread;

struct SignalMask(libc::sigset_t);
impl Drop for SignalMask {
    fn drop(&mut self) {
        unsafe { libc::pthread_sigmask(libc::SIG_SETMASK, &self.0, std::ptr::null_mut()) };
    }
}

#[derive(Debug)]
pub struct Cancelled {
    pub signal: i32,
    pub output: Output,
}
impl std::fmt::Display for Cancelled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "evaluation cancelled by signal {}; owned child reaped\nstdout:\n{}\nstderr:\n{}",
            self.signal,
            String::from_utf8_lossy(&self.output.stdout),
            String::from_utf8_lossy(&self.output.stderr)
        )
    }
}
impl std::error::Error for Cancelled {}

fn read_all(mut pipe: impl Read) -> std::io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    pipe.read_to_end(&mut bytes)?;
    Ok(bytes)
}

/// The evaluators call this synchronously, with no other active child runner.
/// Block cancellation signals before spawning reader/writer threads, receive
/// them in one waiter, and restore the caller's mask before returning.
pub fn run(command: &mut Command, input: Option<&[u8]>) -> Result<Output> {
    let mut signals = unsafe { std::mem::zeroed::<libc::sigset_t>() };
    let mut previous = unsafe { std::mem::zeroed::<libc::sigset_t>() };
    unsafe {
        libc::sigemptyset(&mut signals);
        for signal in [libc::SIGINT, libc::SIGTERM, libc::SIGUSR1] {
            libc::sigaddset(&mut signals, signal);
        }
    }
    let code = unsafe { libc::pthread_sigmask(libc::SIG_BLOCK, &signals, &mut previous) };
    if code != 0 {
        return Err(std::io::Error::from_raw_os_error(code).into());
    }
    let _mask = SignalMask(previous);
    command.process_group(0);
    unsafe {
        command.pre_exec(move || {
            if libc::sigprocmask(libc::SIG_SETMASK, &previous, std::ptr::null_mut()) == -1 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let mut child = command
        .stdin(if input.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .context("start evaluation child")?;
    let pid = child.id() as i32;
    let monitor = thread::spawn(move || {
        let mut signal = 0;
        let code = unsafe { libc::sigwait(&signals, &mut signal) };
        if code != 0 {
            return Err(std::io::Error::from_raw_os_error(code));
        }
        if signal == libc::SIGUSR1 {
            return Ok(None);
        }
        unsafe { libc::kill(-pid, libc::SIGKILL) };
        Ok(Some(signal))
    });
    use std::os::unix::thread::JoinHandleExt;
    let monitor_id = monitor.as_pthread_t();
    let stdout = child.stdout.take().expect("piped stdout");
    let stderr = child.stderr.take().expect("piped stderr");
    let stdin = child.stdin.take();
    let input = input.map(<[u8]>::to_vec);
    let out = thread::spawn(move || read_all(stdout));
    let err = thread::spawn(move || read_all(stderr));
    let writer = thread::spawn(move || -> std::io::Result<()> {
        if let (Some(mut stdin), Some(bytes)) = (stdin, input) {
            stdin.write_all(&bytes)?;
        }
        Ok(())
    });
    // WNOWAIT keeps the leader's PID reserved until the signal waiter has
    // stopped and descendants have been killed. Never signal a re-used PID.
    let wait = loop {
        let mut info = unsafe { std::mem::zeroed::<libc::siginfo_t>() };
        if unsafe {
            libc::waitid(
                libc::P_PID,
                pid as _,
                &mut info,
                libc::WEXITED | libc::WNOWAIT,
            )
        } == 0
        {
            break Ok(());
        }
        let error = std::io::Error::last_os_error();
        if error.kind() != std::io::ErrorKind::Interrupted {
            break Err(error);
        }
    };
    unsafe { libc::pthread_kill(monitor_id, libc::SIGUSR1) };
    let cancellation = monitor.join().expect("signal waiter panicked");
    unsafe { libc::kill(-pid, libc::SIGKILL) };
    let status = child.wait();
    let stdout = out.join().expect("stdout reader panicked");
    let stderr = err.join().expect("stderr reader panicked");
    let written = writer.join().expect("stdin writer panicked");
    wait.context("observe evaluation child exit")?;
    let output = Output {
        status: status.context("reap evaluation child")?,
        stdout: stdout?,
        stderr: stderr?,
    };
    if let Some(signal) = cancellation? {
        return Err(Cancelled { signal, output }.into());
    }
    // Early exit can close stdin normally; the exit status and both streams
    // describe that result. Other write failures remain visible.
    if let Err(error) = written {
        if error.kind() != std::io::ErrorKind::BrokenPipe {
            return Err(error).context(format!(
                "write evaluation input; stdout: {}; stderr: {}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
    }
    Ok(output)
}
