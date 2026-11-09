use super::*;
use chrono::{DateTime, Utc};

/// A target's durable first defeat, or the explicit result of migration021.
/// Missing metadata is an error, never evidence that a new target is old.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefeatClock {
    Recorded(DateTime<Utc>),
    LegacyExpired,
}

#[derive(Debug)]
pub struct RetirementMetadataIssue(crate::interaction::NeedsInput);
impl RetirementMetadataIssue {
    pub fn correction(&self) -> &crate::interaction::NeedsInput {
        &self.0
    }
}
impl std::fmt::Display for RetirementMetadataIssue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            serde_json::to_string(&self.0).map_err(|_| std::fmt::Error)?
        )
    }
}
impl std::error::Error for RetirementMetadataIssue {}
fn repair(message: &str) -> anyhow::Error {
    use crate::interaction::{CorrectionItem, Location, NeedsInput};
    use crate::validation::{Code, Fault, Segment};
    RetirementMetadataIssue(NeedsInput::new(CorrectionItem::new(Location::Configuration,
        Fault{path:vec![Segment::Key("database".into()),Segment::Key("retirement".into())],code:Code::MalformedInput,message:message.into()},
        "Each defeated target has its first actual PostgreSQL defeat date or the explicit legacy-expired marker installed by the migration.".into(),
        "Read the target's stored retirement metadata and the first-defeat-clock migration receipt, then open the user dialog. Do not invent a historical date, label new broken data as legacy, restart its grace period or delete the belief to bypass this problem.".into()).expect("stored clock repair explains the invariant"),vec![]).expect("stored clock repair contains one issue")).into()
}
impl DefeatClock {
    pub(crate) fn waiting_satisfied(self, now: DateTime<Utc>, grace: chrono::Duration) -> bool {
        match self {
            Self::Recorded(first) => now - first >= grace,
            Self::LegacyExpired => true,
        }
    }
}

fn metadata(
    target: Uuid,
    first: Option<&str>,
    legacy: Option<&str>,
) -> Result<Option<DefeatClock>> {
    let first = first.filter(|value| *value != "null");
    let legacy = legacy.filter(|value| *value != "null");
    let issue = |message: &str| repair(&format!("Defeated belief {target}: {message}"));
    let legacy = legacy
        .map(str::parse::<bool>)
        .transpose()
        .map_err(|_| issue("The legacy-expired property is not a boolean."))?;
    match (first, legacy) {
        (Some(_), Some(true)) => Err(issue("The target has both a defeat date and a legacy-expired marker; no expiry was inferred.")),
        (Some(first), _) => {
            Ok(Some(DefeatClock::Recorded(DateTime::parse_from_rfc3339(&serde_json::from_str::<String>(first).map_err(|_|issue("The first defeat date is not a string."))?).map_err(|_|issue("The stored first defeat date is invalid; no replacement date was guessed."))?.with_timezone(&Utc))))
        }
        (None, Some(true)) => Ok(Some(DefeatClock::LegacyExpired)),
        (None, _) => Ok(None),
    }
}

impl AgeStore {
    /// Called only under the existing writer lock and transaction. Clock read,
    /// target metadata, edge and saved answer commit at the same boundary.
    pub(super) async fn record_defeat_time_on(&self, client: &Client, target: Uuid) -> Result<()> {
        let graph = &self.graph_name;
        let row = client.query_one(&format!(
            "SELECT ag_catalog.agtype_out(first)::text AS first,ag_catalog.agtype_out(legacy)::text AS legacy,incoming::text FROM ag_catalog.cypher('{graph}', $$ MATCH (target:Belief {{id:'{target}'}}) OPTIONAL MATCH (:Belief)-[prior:DEFEATS]->(target) RETURN target.first_defeated_at,target.legacy_defeat_expired,count(prior) $$) AS (first ag_catalog.agtype,legacy ag_catalog.agtype,incoming ag_catalog.agtype)"
        ), &[]).await?;
        let first: Option<&str> = row.get("first");
        let legacy: Option<&str> = row.get("legacy");
        if metadata(target, first, legacy)?.is_some() {
            return Ok(());
        }
        let incoming: &str = row.get("incoming");
        if incoming.parse::<u64>()? != 0 {
            return Err(repair(&format!("Defeated belief {target} has no recorded defeat date or legacy-expired marker. No fresh date was assigned.")));
        }
        let received: DateTime<Utc> = client
            .query_one("SELECT clock_timestamp()", &[])
            .await?
            .get(0);
        let date = received.to_rfc3339();
        client.query(&format!("SELECT * FROM ag_catalog.cypher('{graph}', $$ MATCH (target:Belief {{id:'{target}'}}) SET target.first_defeated_at = '{date}' RETURN target.id $$) AS (id ag_catalog.agtype)"), &[]).await?;
        Ok(())
    }

    pub(super) async fn defeat_clocks(
        &self,
        project: Option<&str>,
    ) -> Result<Vec<(Uuid, Uuid, DefeatClock)>> {
        let client = self.client.lock().await;
        self.defeat_clocks_on(&client, project).await
    }

    pub(super) async fn defeat_clocks_on(
        &self,
        client: &Client,
        project: Option<&str>,
    ) -> Result<Vec<(Uuid, Uuid, DefeatClock)>> {
        let graph = &self.graph_name;
        let filter = if project.is_some() {
            " WHERE (a.project = $project OR a.project IS NULL) AND (b.project = $project OR b.project IS NULL)"
        } else {
            ""
        };
        let prepare = format!("PREPARE age_retirement_clocks(agtype) AS SELECT source::text,target::text,ag_catalog.agtype_out(first)::text AS first,ag_catalog.agtype_out(legacy)::text AS legacy FROM ag_catalog.cypher('{graph}', $$ MATCH (a:Belief)-[:DEFEATS]->(b:Belief){filter} RETURN a.id,b.id,b.first_defeated_at,b.legacy_defeat_expired $$, $1) AS (source ag_catalog.agtype,target ag_catalog.agtype,first ag_catalog.agtype,legacy ag_catalog.agtype)");
        let parameters = serde_json::json!({"project": project}).to_string();
        let rows = age_query_rows(client, "age_retirement_clocks", &prepare, &parameters).await?;
        rows.iter().map(|row| {
            let source = row.get("source").context("missing defeat source")?;
            let target = row.get("target").context("missing defeat target")?;
            let target=Uuid::parse_str(target)?;
            let clock = metadata(target,row.get("first"),row.get("legacy"))?.ok_or_else(||repair(&format!("Defeated belief {target} is missing its first defeat date and legacy-expired marker. No belief was deleted and no date was guessed.")))?;
            Ok((Uuid::parse_str(source)?,target,clock))
        }).collect()
    }
}
