use anyhow::Result;
use chrono::{DateTime, Duration, Utc};
use mimir_core::{
    graph::{Belief, MemoryType},
    inference::InferenceEngine,
};
use std::collections::HashMap;
use uuid::Uuid;

fn clock() -> DateTime<Utc> {
    DateTime::parse_from_rfc3339("2026-11-09T00:00:00Z")
        .unwrap()
        .with_timezone(&Utc)
}
fn fact(baseline: DateTime<Utc>, alpha: f64, beta: f64) -> Result<Belief> {
    Belief::from_stored(
        Uuid::from_u128(1),
        "time-accounted input".into(),
        alpha,
        beta,
        1.0,
        1.0,
        baseline,
        baseline,
        baseline,
        MemoryType::Fact,
        None,
    )
}

#[test]
fn fractional_second_is_charged_before_its_baseline_advances() -> Result<()> {
    let now = clock();
    let value = fact(now - Duration::milliseconds(500), 100.0, 10.0)?;
    let updates = InferenceEngine::new().decay_all(&[value], now, 0.5, &HashMap::new())?;
    assert_eq!(updates.len(), 1);
    assert!(updates[0].1 .0 < 100.0 && updates[0].1 .0 > 99.0);
    Ok(())
}

#[test]
fn a_changed_representable_count_is_not_hidden_by_an_epsilon_allowance() -> Result<()> {
    let now = clock();
    let value = fact(now - Duration::days(1), 100.0, 10.0)?;
    let factor = f64::from_bits(1.0f64.to_bits() - 1);
    let updates = InferenceEngine::new().decay_all(&[value], now, factor, &HashMap::new())?;
    assert_eq!(updates.len(), 1);
    assert_ne!(updates[0].1 .0.to_bits(), 100.0f64.to_bits());
    Ok(())
}

#[test]
fn accounted_counts_remain_exact_at_the_same_or_an_earlier_clock() -> Result<()> {
    let now = clock();
    let value = fact(now - Duration::days(1), 100.0, 10.0)?;
    let (alpha, beta) =
        InferenceEngine::new().decay_all(&[value.clone()], now, 0.5, &HashMap::new())?[0].1;
    assert_eq!((alpha, beta), (50.5, 5.5));
    let mut published = value;
    published.alpha = alpha;
    published.beta = beta;
    published.decay_accounted_at = now;
    for time in [now, now - Duration::nanoseconds(1)] {
        assert!(InferenceEngine::new()
            .decay_all(&[published.clone()], time, 0.5, &HashMap::new())?
            .is_empty());
    }
    Ok(())
}
