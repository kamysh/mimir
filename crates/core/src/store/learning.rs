use super::*;
use crate::learning::*;
use anyhow::ensure;
use std::collections::HashSet;
use tokio_postgres::Transaction;

fn state(row: &Row) -> Result<ExperienceState> {
    Ok(ExperienceState {
        experience: serde_json::from_str(row.get::<_, &str>("payload"))?,
        revision: row.get("revision"),
        review_revision: row.get("review_revision"),
        reviewed_revision: row.get("reviewed_revision"),
    })
}
const CURRENT: &str = "SELECT e.revision,e.review_revision,e.reviewed_revision,v.payload::text AS payload FROM mimir_experiences e JOIN mimir_experience_versions v ON v.experience_id=e.id AND v.revision=e.revision";
const ACTIVE_REVIEWS: &str = "SELECT r.payload::text FROM mimir_experiences e JOIN mimir_review_versions r ON r.experience_id=e.id AND r.revision=e.review_revision AND r.experience_revision=e.revision";

impl AgeStore {
    pub async fn get_experience(&self, id: Uuid) -> Result<Option<ExperienceState>> {
        let client = self.client.lock().await;
        client
            .query_opt(&format!("{CURRENT} WHERE e.id=$1"), &[&id])
            .await?
            .as_ref()
            .map(state)
            .transpose()
    }
    pub async fn list_experiences(
        &self,
        project: Option<&str>,
        pending: bool,
        limit: usize,
    ) -> Result<Vec<ExperienceState>> {
        ensure!((1..=100).contains(&limit), "limit must be in 1..=100");
        let client = self.client.lock().await;
        client.query(&format!("{CURRENT} WHERE ($1::text IS NULL OR e.project=$1) AND (NOT $2 OR e.reviewed_revision<e.revision) ORDER BY e.updated_at,e.id LIMIT $3"), &[&project, &pending, &(limit as i64)]).await?.iter().map(state).collect()
    }
    pub async fn experience_history(&self, id: Uuid) -> Result<serde_json::Value> {
        let client = self.client.lock().await;
        let mut result = serde_json::json!({"experiences": [], "reviews": []});
        for (table, key) in [
            ("mimir_experience_versions", "experiences"),
            ("mimir_review_versions", "reviews"),
        ] {
            let rows = client.query(&format!("SELECT revision,payload::text,created_at FROM {table} WHERE experience_id=$1 ORDER BY revision"), &[&id]).await?;
            result[key] = serde_json::Value::Array(rows.iter().map(|row| {
                Ok(serde_json::json!({"revision":row.get::<_,i64>(0), "payload":serde_json::from_str::<serde_json::Value>(row.get::<_,&str>(1))?, "created_at":row.get::<_,chrono::DateTime<chrono::Utc>>(2)}))
            }).collect::<Result<_>>()?);
        }
        Ok(result)
    }
    async fn learning_beliefs(&self, tx: &Transaction<'_>) -> Result<Vec<Belief>> {
        let g = &self.graph_name;
        let sql = format!("SELECT id::text,content::text,probability::text,confidence::text,alpha::text,beta::text,alpha0::text,beta0::text,created_at::text,last_activated_at::text,memory_type::text,project::text FROM ag_catalog.cypher('{g}', $$ MATCH (n:Belief) RETURN n.id,n.content,n.probability,n.confidence,n.alpha,n.beta,n.alpha0,n.beta0,n.created_at,n.last_activated_at,n.memory_type,n.project $$) {BELIEF_RETURN_COLUMNS}");
        tx.query(&sql, &[])
            .await?
            .iter()
            .map(belief_from_row)
            .collect()
    }
    async fn active_reviews(tx: &Transaction<'_>) -> Result<Vec<Review>> {
        tx.query(ACTIVE_REVIEWS, &[])
            .await?
            .iter()
            .map(|r| Ok(serde_json::from_str(r.get::<_, &str>(0))?))
            .collect()
    }
    async fn active_review(tx: &Transaction<'_>, id: Uuid) -> Result<Option<Review>> {
        tx.query_opt(&format!("{ACTIVE_REVIEWS} WHERE e.id=$1"), &[&id])
            .await?
            .map(|row| Ok(serde_json::from_str(row.get::<_, &str>(0))?))
            .transpose()
    }
    pub async fn learning_overlay(&self) -> Result<(HashMap<Uuid, (f64, f64)>, HashSet<Uuid>)> {
        let mut client = self.client.lock().await;
        let tx = client.transaction().await?;
        let reviews = Self::active_reviews(&tx).await?;
        Ok(overlay(&reviews))
    }
    /// All learning changes are serialized across MCP processes. Graph writes and
    /// the queue acknowledgement commit together; failures leave work pending.
    pub async fn record_experience(
        &self,
        experience: &Experience,
        expected: i64,
    ) -> Result<ExperienceState> {
        experience.validate()?;
        ensure!(
            (0..i64::MAX).contains(&expected),
            "expected_revision must be nonnegative"
        );
        let payload = serde_json::to_string(experience)?;
        let mut client = self.client.lock().await;
        let tx = client.transaction().await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let prior = tx
            .query_opt(&format!("{CURRENT} WHERE e.id=$1"), &[&experience.id])
            .await?
            .as_ref()
            .map(state)
            .transpose()?;
        if let Some(ref p) = prior {
            ensure!(
                p.experience.project == experience.project,
                "experience project is immutable"
            );
            if p.experience == *experience && (expected == p.revision || expected == p.revision - 1)
            {
                return Ok(p.clone());
            }
            ensure!(
                expected == p.revision,
                "stale experience revision: current is {}",
                p.revision
            );
        } else {
            ensure!(expected == 0, "new experience requires expected_revision=0");
        }
        let beliefs = self.learning_beliefs(&tx).await?;
        validate_targets(
            &beliefs,
            &experience.project,
            experience.belief_ids.iter().copied(),
        )?;
        if let Some(id) = experience.pattern_id {
            let g = &self.graph_name;
            let rows = tx.query(&format!("SELECT project::text FROM ag_catalog.cypher('{g}', $$ MATCH (p:Pattern {{id:'{id}'}}) RETURN p.project $$) AS (project ag_catalog.agtype)"), &[]).await?;
            ensure!(!rows.is_empty(), "pattern not found");
            let project: Option<&str> = rows[0].get(0);
            ensure!(
                project.is_none()
                    || project == Some("null")
                    || project == Some(experience.project.as_str()),
                "pattern belongs to another project"
            );
        }
        let old_review = Self::active_review(&tx, experience.id).await?;
        let affected = review_targets(old_review.iter());
        let revision = expected + 1;
        tx.execute("INSERT INTO mimir_experiences(id,project,revision) VALUES($1,$2,$3) ON CONFLICT(id) DO UPDATE SET revision=$3,updated_at=now()", &[&experience.id,&experience.project,&revision]).await?;
        tx.execute("INSERT INTO mimir_experience_versions(experience_id,revision,payload) VALUES($1,$2,$3::text::jsonb)", &[&experience.id,&revision,&payload]).await?;
        self.replace_review_edges(&tx, experience.id, &[]).await?;
        self.recompute_learning(&tx, &beliefs, affected).await?;
        let result = state(
            &tx.query_one(&format!("{CURRENT} WHERE e.id=$1"), &[&experience.id])
                .await?,
        )?;
        tx.commit().await?;
        Ok(result)
    }
    pub async fn review_experience(
        &self,
        review: &Review,
        expected: i64,
    ) -> Result<ExperienceState> {
        review.validate()?;
        ensure!(
            (0..i64::MAX).contains(&expected),
            "expected_review_revision must be nonnegative"
        );
        let mut client = self.client.lock().await;
        let tx = client.transaction().await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let current = state(
            &tx.query_opt(
                &format!("{CURRENT} WHERE e.id=$1"),
                &[&review.experience_id],
            )
            .await?
            .ok_or_else(|| anyhow::anyhow!("experience not found"))?,
        )?;
        ensure!(
            review.experience_revision == current.revision,
            "stale review: experience has changed"
        );
        let old_review = Self::active_review(&tx, review.experience_id).await?;
        if let Some(old) = old_review.as_ref() {
            if old == review
                && (expected == current.review_revision || expected == current.review_revision - 1)
            {
                return Ok(current);
            }
        }
        ensure!(
            expected == current.review_revision,
            "stale review revision: current is {}",
            current.review_revision
        );
        let beliefs = self.learning_beliefs(&tx).await?;
        let ids = review
            .feedback
            .iter()
            .map(|f| f.belief_id)
            .chain(review.superseded_beliefs.iter().copied())
            .chain(review.links.iter().flat_map(|l| [l.from_id, l.to_id]));
        validate_targets(&beliefs, &current.experience.project, ids)?;
        ensure!(
            review.feedback.is_empty()
                && review.links.is_empty()
                && review.superseded_beliefs.is_empty()
                || current
                    .experience
                    .evidence
                    .iter()
                    .any(|e| !e.trim().is_empty()),
            "learning requires recorded evidence"
        );
        let mut affected = review_targets(old_review.iter());
        affected.extend(review_targets(std::iter::once(review)));
        let revision = expected + 1;
        let payload = serde_json::to_string(review)?;
        tx.execute("INSERT INTO mimir_review_versions(experience_id,revision,experience_revision,payload) VALUES($1,$2,$3,$4::text::jsonb)", &[&review.experience_id,&revision,&review.experience_revision,&payload]).await?;
        tx.execute("UPDATE mimir_experiences SET review_revision=$2,reviewed_revision=revision WHERE id=$1", &[&review.experience_id,&revision]).await?;
        self.replace_review_edges(&tx, review.experience_id, &review.links)
            .await?;
        self.recompute_learning(&tx, &beliefs, affected).await?;
        let result = state(
            &tx.query_one(
                &format!("{CURRENT} WHERE e.id=$1"),
                &[&review.experience_id],
            )
            .await?,
        )?;
        tx.commit().await?;
        Ok(result)
    }
    async fn replace_review_edges(
        &self,
        tx: &Transaction<'_>,
        id: Uuid,
        links: &[LearningLink],
    ) -> Result<()> {
        let g = &self.graph_name;
        tx.query(&format!("SELECT * FROM ag_catalog.cypher('{g}', $$ MATCH (:Belief)-[r]->(:Belief) WHERE r.experience_id='{id}' DELETE r $$) AS (v ag_catalog.agtype)"), &[]).await?;
        for link in links {
            let label = link.relation.as_str();
            let mut pairs = vec![(link.from_id, link.to_id)];
            if link.relation == EdgeType::Contradicts {
                pairs.push((link.to_id, link.from_id));
            }
            for (from, to) in pairs {
                tx.query(&format!("SELECT * FROM ag_catalog.cypher('{g}', $$ MATCH (a:Belief {{id:'{from}'}}),(b:Belief {{id:'{to}'}}) CREATE (a)-[r:{label} {{weight:{},experience_id:'{id}'}}]->(b) RETURN r $$) AS (r ag_catalog.agtype)",link.weight), &[]).await?;
            }
        }
        Ok(())
    }
    async fn recompute_learning(
        &self,
        tx: &Transaction<'_>,
        beliefs: &[Belief],
        mut affected: HashSet<Uuid>,
    ) -> Result<()> {
        if affected.is_empty() {
            return Ok(());
        }
        let g = &self.graph_name;
        let rows = tx.query(&format!("SELECT a::text,b::text,label::text,w::text FROM ag_catalog.cypher('{g}', $$ MATCH (a:Belief)-[r]->(b:Belief) RETURN a.id,b.id,type(r),r.weight $$) AS (a ag_catalog.agtype,b ag_catalog.agtype,label ag_catalog.agtype,w ag_catalog.agtype)"), &[]).await?;
        let edges: Vec<_> = rows
            .iter()
            .map(|r| -> Result<_> {
                Ok((
                    Uuid::parse_str(r.get(0))?,
                    Uuid::parse_str(r.get(1))?,
                    r.get::<_, &str>(2).parse::<EdgeType>()?,
                    Probability::new(r.get::<_, &str>(3).parse()?)?,
                ))
            })
            .collect::<Result<_>>()?;
        // Closure includes targets of removed links (supplied by caller).
        loop {
            let n = affected.len();
            for (from, to, kind, _) in &edges {
                if *kind != EdgeType::Contradicts && affected.contains(from) {
                    affected.insert(*to);
                }
            }
            if n == affected.len() {
                break;
            }
        }
        let (mut mass, _) = overlay(&Self::active_reviews(tx).await?);
        let ground = tx.query(&format!("SELECT id::text,w::text FROM ag_catalog.cypher('{g}', $$ MATCH (:DocumentChunk)-[r:GROUNDS]->(b:Belief) RETURN b.id,sum(r.weight) $$) AS (id ag_catalog.agtype,w ag_catalog.agtype)"), &[]).await?;
        for row in ground {
            let id = Uuid::parse_str(row.get(0))?;
            let weight: f64 = row.get::<_, &str>(1).parse()?;
            mass.entry(id).or_insert((0.0, 0.0)).0 += EVIDENCE_MASS_K * weight;
        }
        let mut downstream: Vec<_> = beliefs
            .iter()
            .filter(|b| affected.contains(&b.id))
            .cloned()
            .collect();
        for b in &mut downstream {
            if let Some((a, z)) = mass.get(&b.id) {
                b.alpha0 += a;
                b.beta0 += z;
            }
        }
        let external = beliefs
            .iter()
            .filter(|b| !affected.contains(&b.id))
            .map(|b| (b.id, b.probability.value()))
            .collect();
        let updates =
            crate::inference::InferenceEngine::new().recompute(&downstream, &edges, &external)?;
        for (id, (a, b)) in updates {
            tx.query(&self.update_belief_beta_sql(id, a, b)?, &[])
                .await?;
        }
        Ok(())
    }
}
fn validate_targets(
    beliefs: &[Belief],
    project: &str,
    ids: impl Iterator<Item = Uuid>,
) -> Result<()> {
    for id in ids {
        let b = beliefs
            .iter()
            .find(|b| b.id == id)
            .ok_or_else(|| anyhow::anyhow!("belief {id} not found"))?;
        // A project observation cannot change globally shared knowledge implicitly.
        ensure!(
            b.project.as_deref() == Some(project),
            "belief {id} must belong to the experience project"
        );
        ensure!(
            b.memory_type != MemoryType::Working,
            "working memory is not a learning target"
        );
    }
    Ok(())
}
fn review_targets<'a>(reviews: impl Iterator<Item = &'a Review>) -> HashSet<Uuid> {
    reviews
        .flat_map(|r| {
            r.feedback.iter().map(|f| f.belief_id).chain(
                r.links
                    .iter()
                    .filter(|l| l.relation != EdgeType::Contradicts)
                    .map(|l| l.to_id),
            )
        })
        .collect()
}
fn overlay(reviews: &[Review]) -> (HashMap<Uuid, (f64, f64)>, HashSet<Uuid>) {
    let mut mass = HashMap::new();
    let mut superseded = HashSet::new();
    for r in reviews {
        superseded.extend(r.superseded_beliefs.iter().copied());
        for f in &r.feedback {
            let entry = mass.entry(f.belief_id).or_insert((0.0, 0.0));
            let delta = f.weight * crate::graph::EVIDENCE_UNIT;
            match f.verdict {
                Verdict::Support => entry.0 += delta,
                Verdict::Defeat => entry.1 += delta,
            }
        }
    }
    (mass, superseded)
}

impl AgeStore {
    pub async fn pattern_outcomes(&self, pattern: Pattern, project: &str) -> Result<PatternResult> {
        let client = self.client.lock().await;
        let rows = client.query("SELECT v.payload->>'outcome' AS outcome, v.payload->>'source' AS source, count(*)::bigint AS n FROM mimir_experiences e JOIN mimir_experience_versions v ON v.experience_id=e.id AND v.revision=e.revision WHERE e.project=$1 AND v.payload->>'pattern_id'=$2 GROUP BY outcome,source", &[&project,&pattern.id.to_string()]).await?;
        let (mut successes, mut failures, mut unknown) = (0, 0, 0);
        for r in rows {
            let n = r.get::<_, i64>("n") as usize;
            match (r.get::<_, &str>("source"), r.get::<_, &str>("outcome")) {
                ("agent_report", _) | (_, "unknown") => unknown += n,
                (_, "success") => successes += n,
                (_, "failure") => failures += n,
                _ => anyhow::bail!("invalid stored outcome"),
            }
        }
        Ok(PatternResult {
            pattern,
            successes,
            failures,
            unknown,
            observed_success_probability: (1.0 + successes as f64)
                / (2.0 + successes as f64 + failures as f64),
        })
    }
    pub async fn delete_learning_project(&self, project: &str) -> Result<()> {
        let mut client = self.client.lock().await;
        let tx = client.transaction().await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        tx.execute(
            "DELETE FROM mimir_experiences WHERE project=$1",
            &[&project],
        )
        .await?;
        tx.commit().await?;
        Ok(())
    }
}

impl AgeStore {
    pub async fn reviews_for_belief(
        &self,
        id: Uuid,
        offset: usize,
        limit: usize,
    ) -> Result<serde_json::Value> {
        ensure!((1..=20).contains(&limit), "limit must be in 1..=20");
        let mut client = self.client.lock().await;
        let tx = client.transaction().await?;
        let mut reviews: Vec<_> = Self::active_reviews(&tx)
            .await?
            .into_iter()
            .filter(|r| {
                r.feedback.iter().any(|f| f.belief_id == id)
                    || r.superseded_beliefs.contains(&id)
                    || r.links.iter().any(|l| l.from_id == id || l.to_id == id)
            })
            .collect();
        reviews.sort_by_key(|r| r.experience_id);
        let total = reviews.len();
        let page: Vec<_> = reviews.into_iter().skip(offset).take(limit).collect();
        let next = offset.saturating_add(page.len());
        Ok(
            serde_json::json!({"reviews":page,"total":total,"next_offset":if next<total {Some(next)} else {None}}),
        )
    }
}
