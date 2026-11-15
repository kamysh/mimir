//! CLI callers receive the same actionable correction as MCP callers
//! (issue #469 item 101): the sweep refusal names the unset user policy and
//! the repair path on the CLI's error output, and configuring the policy
//! makes the same command succeed.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use std::process::Command;

fn run(args: &[&str], config: &std::path::Path) -> Result<std::process::Output> {
    Ok(Command::new(std::env::var("MIMIR_TEST_MIMIR")?)
        .args(args)
        .env("MIMIR_CONFIG", config)
        .output()?)
}

#[tokio::test]
async fn cli_sweep_refusal_carries_the_correction_guidance() -> Result<()> {
    let fixture = isolation::fixture();
    let config = fixture.root.join("config.toml");

    // The fixture configuration has no [retirement] policy: the CLI must
    // fail with the same guidance the MCP surface returns, not a bare exit.
    let refused = run(&["sweep-defeated", "--threshold", "0.3"], &config)?;
    ensure!(
        !refused.status.success(),
        "sweep without a retention policy must fail"
    );
    let stderr = String::from_utf8_lossy(&refused.stderr);
    ensure!(
        stderr.contains("[retirement].grace_hours is unset"),
        "CLI refusal must name the unset policy: {stderr}"
    );
    ensure!(
        stderr.contains("Ask the user to choose a retention period"),
        "CLI refusal must carry the repair path: {stderr}"
    );

    // Configuring the user's policy makes the same command succeed.
    let with_policy = fixture.root.join("correction-parity.toml");
    let base = std::fs::read_to_string(&config)?;
    std::fs::write(
        &with_policy,
        format!("{base}\n[retirement]\ngrace_hours = 0\n"),
    )?;
    let allowed = run(&["sweep-defeated", "--threshold", "0.3"], &with_policy)?;
    ensure!(
        allowed.status.success(),
        "sweep with a configured policy must succeed: {}",
        String::from_utf8_lossy(&allowed.stderr)
    );
    Ok(())
}
