//! Standalone Rust fixture compiled by tests/judge-adapters.sh.
//! It never contacts a model, database, or network service.
use std::fs;
use std::io::{Read, Write};
use std::net::TcpStream;
use std::process::{self, Command};
use std::thread;

fn ready() {
    if let Ok(path) = std::env::var("MIMIR_JUDGE_FIXTURE_READY_FILE") {
        fs::write(path, "ready").unwrap();
    }
    if let Ok(address) = std::env::var("MIMIR_JUDGE_FIXTURE_READY_ADDR") {
        TcpStream::connect(address)
            .unwrap()
            .write_all(b"ready\n")
            .unwrap();
    }
}

fn blocked() -> ! {
    loop {
        thread::park();
    }
}

fn main() {
    if std::env::args().nth(1).as_deref() == Some("--blocked-child") {
        blocked();
    }
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();
    match std::env::var("MIMIR_JUDGE_FIXTURE_MODE").as_deref() {
        Ok("crash") => process::exit(7),
        Ok("malformed") => println!("not-json"),
        Ok("oversized") => println!("{}", "x".repeat(8 * 1024 * 1024 + 1)),
        Ok("slow") => {
            ready();
            blocked();
        }
        Ok("fork") => {
            let child = Command::new(std::env::current_exe().unwrap())
                .arg("--blocked-child")
                .spawn()
                .unwrap();
            let path = std::env::var("MIMIR_JUDGE_FIXTURE_PID_FILE").unwrap();
            fs::write(path, child.id().to_string()).unwrap();
            ready();
            blocked();
        }
        _ => println!("{}", r#"{"calls":[]}"#),
    }
}
