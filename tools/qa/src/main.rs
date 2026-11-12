mod fixture;
mod formal;

use anyhow::{bail, Result};
use std::{
    io::ErrorKind,
    net::TcpListener,
    process::Command,
    sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        Arc,
    },
    thread,
    time::Duration,
};

fn decoy_guard(binary: &str) -> Result<()> {
    let listener = TcpListener::bind("127.0.0.1:0")?;
    listener.set_nonblocking(true)?;
    let port = listener.local_addr()?.port();
    let stop = Arc::new(AtomicBool::new(false));
    let connections = Arc::new(AtomicUsize::new(0));
    let (worker_stop, worker_connections) = (Arc::clone(&stop), Arc::clone(&connections));
    let worker = thread::spawn(move || {
        while !worker_stop.load(Ordering::Relaxed) {
            match listener.accept() {
                Ok((stream, _)) => {
                    worker_connections.fetch_add(1, Ordering::Relaxed);
                    drop(stream);
                }
                Err(e) if e.kind() == ErrorKind::WouldBlock => {
                    thread::sleep(Duration::from_millis(10))
                }
                Err(_) => break,
            }
        }
    });
    let output = Command::new(binary)
        .args(["--exact", "test_insert_and_get_belief", "--nocapture"])
        .env("MIMIR_PORT", port.to_string())
        .env("MIMIR_DBNAME", "mimir")
        .output()?;
    // Allow the listener to consume any connection queued just before exit.
    thread::sleep(Duration::from_millis(100));
    stop.store(true, Ordering::Relaxed);
    worker
        .join()
        .map_err(|_| anyhow::anyhow!("decoy listener failed"))?;
    let untouched = connections.load(Ordering::Relaxed) == 0;
    let log = String::from_utf8_lossy(&output.stdout).to_string()
        + &String::from_utf8_lossy(&output.stderr);
    print!("{log}");
    if output.status.code() != Some(101)
        || !log.contains("MIMIR_PORT does not match this test fixture")
        || !untouched
    {
        bail!("Rust connection guard did not reject conflicting settings before networking");
    }
    Ok(())
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("formal") if args.len() == 1 => formal::check(),
        Some("fixture-check") if args.len() == 1 => fixture::check(),
        Some("decoy-guard") if args.len() == 2 => decoy_guard(&args[1]),
        _ => bail!("usage: mimir-qa formal|fixture-check|decoy-guard TEST-BINARY"),
    }
}
