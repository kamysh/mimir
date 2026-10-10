//! Standalone Rust fixture compiled by tests/judge-adapters.sh.
//! It never contacts a model, database, or network service.
use std::fs;
use std::io::Read;
use std::process::{self, Command};
use std::thread;
use std::time::Duration;

fn main() {
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();
    match std::env::var("MIMIR_JUDGE_FIXTURE_MODE").as_deref() {
        Ok("crash") => process::exit(7),
        Ok("malformed") => println!("not-json"),
        Ok("oversized") => println!("{}", "x".repeat(8 * 1024 * 1024 + 1)),
        Ok("slow") => thread::sleep(Duration::from_secs(30)),
        Ok("fork") => {
            let child = Command::new("sleep").arg("30").spawn().unwrap();
            let path = std::env::var("MIMIR_JUDGE_FIXTURE_PID_FILE").unwrap();
            fs::write(path, child.id().to_string()).unwrap();
            thread::sleep(Duration::from_secs(30));
        }
        _ => println!("{}", r#"{"calls":[]}"#),
    }
}
