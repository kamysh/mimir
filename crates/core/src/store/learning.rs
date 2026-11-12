use super::*;
use crate::learning::*;
use anyhow::ensure;
use std::collections::HashSet;
use tokio_postgres::Transaction;

fn state(row: &Row) -> Result<ExperienceState> {
    let experience: Experience = serde_json::from_str(row.get::<_, &str>("payload"))?;
    let item_ids = local_item_ids(&experience.learning_items);
    Ok(ExperienceState {
        experience,
        revision: row.get("revision"),
        review_revision: row.get("review_revision"),
        reviewed_revision: row.get("reviewed_revision"),
        candidate_ids: HashMap::new(),
        item_ids,
    })
}

fn local_item_ids(items: &[crate::assessment::LearningItem]) -> HashMap<String, Uuid> {
    items
        .iter()
        .filter_map(|item| Some((item.key.clone()?, item.id?)))
        .collect()
}
const CURRENT: &str = "SELECT e.revision,e.review_revision,e.reviewed_revision,v.payload::text AS payload FROM mimir_experiences e JOIN mimir_experience_versions v ON v.experience_id=e.id AND v.revision=e.revision";
const ACTIVE_REVIEWS: &str = "SELECT r.payload::text FROM mimir_experiences e JOIN mimir_review_versions r ON r.experience_id=e.id AND r.revision=e.review_revision AND r.experience_revision=e.revision";

fn uuid_list(ids: &HashSet<Uuid>) -> String {
    let mut sorted: Vec<_> = ids.iter().copied().collect();
    sorted.sort_unstable();
    sorted
        .into_iter()
        .map(|id| format!("'{id}'"))
        .collect::<Vec<_>>()
        .join(",")
}

impl AgeStore {
    /// Only INSERT's PostgreSQL default may allocate a persistent item UUID.
    /// The enclosing learning transaction owns both allocation and publication.
    async fn resolve_item_ids(
        tx: &Transaction<'_>,
        experience_id: Uuid,
        items: &mut [crate::assessment::LearningItem],
    ) -> Result<()> {
        for item in items {
            let row = if let Some(key) = &item.key {
                match tx.query_opt(
                    "SELECT item_id,source_ref,actor FROM mimir_learning_item_owners WHERE experience_id=$1 AND item_key=$2",
                    &[&experience_id, key],
                ).await? {
                    Some(row) => row,
                    None => {
                        ensure!(item.id.is_none(), "new learning items must omit id; PostgreSQL allocates their UUIDs");
                        tx.query_one(
                            "INSERT INTO mimir_learning_item_owners(experience_id,item_key,source_ref,actor) VALUES($1,$2,$3,$4) RETURNING item_id,source_ref,actor",
                            &[&experience_id, key, &item.source_ref, &item.actor],
                        ).await?
                    }
                }
            } else {
                let id = item.id.ok_or_else(|| {
                    anyhow::anyhow!("learning item requires a local key or existing ID")
                })?;
                tx.query_opt(
                    "SELECT item_id,source_ref,actor FROM mimir_learning_item_owners WHERE experience_id=$1 AND item_id=$2",
                    &[&experience_id, &id],
                ).await?.ok_or_else(|| anyhow::anyhow!("unreserved learning item UUID; new items require a local key and PostgreSQL allocates their UUIDs"))?
            };
            let assigned: Uuid = row.get("item_id");
            ensure!(
                item.id.is_none_or(|id| id == assigned),
                "learning item key and UUID disagree"
            );
            ensure!(
                row.get::<_, &str>("source_ref") == item.source_ref
                    && row.get::<_, &str>("actor") == item.actor,
                "learning item identity or provenance conflict"
            );
            item.id = Some(assigned);
        }
        Ok(())
    }

    async fn resolve_item_references(tx: &Transaction<'_>, review: &mut Review) -> Result<()> {
        for assessment in &mut review.assessments {
            for key in &assessment.item_keys {
                let row = tx.query_opt(
                    "SELECT item_id FROM mimir_learning_item_owners WHERE experience_id=$1 AND item_key=$2",
                    &[&review.experience_id, key],
                ).await?.ok_or_else(|| anyhow::anyhow!("unknown learning item key: {key}"))?;
                assessment.item_ids.push(row.get(0));
            }
            assessment.item_keys.clear();
        }
        Ok(())
    }

    pub async fn assessments_for_beliefs(
        &self,
        project: &str,
        ids: &[Uuid],
    ) -> Result<(Vec<serde_json::Value>, bool)> {
        let client = self.client.lock().await;
        let rows = client.query("SELECT a.belief_id,a.scope,a.rubric,sum(a.positive),sum(a.negative),sum(a.benefit),sum(a.benefit_weight),count(*),count(*) FILTER (WHERE a.positive+a.negative=0),count(*) FILTER (WHERE a.benefit_weight=0) FROM mimir_assessment_contributions a JOIN mimir_experiences e ON e.id=a.experience_id JOIN mimir_review_versions r ON r.experience_id=e.id AND r.revision=a.review_revision WHERE e.project=$1 AND a.belief_id=ANY($2) AND e.review_revision=r.revision AND e.revision=r.experience_revision GROUP BY a.belief_id,a.scope,a.rubric ORDER BY a.belief_id,a.scope,a.rubric", &[&project,&ids]).await?;
        let values=rows.iter().map(|r| {
            let scores=crate::assessment::Scores::from_totals(r.get(3),r.get(4),r.get(5),r.get(6),r.get(7),r.get(8),r.get(9))?;
            Ok(serde_json::json!({"belief_id":r.get::<_,Uuid>(0),"scope":r.get::<_,&str>(1),"rubric":r.get::<_,&str>(2),"scores":scores}))
        }).collect::<Result<Vec<_>>>()?;
        Ok((values, false))
    }
    pub async fn lesson_assessment(
        &self,
        project: &str,
        belief_id: Uuid,
        scope: &str,
        rubric: &str,
    ) -> Result<serde_json::Value> {
        ensure!(
            !project.trim().is_empty() && !scope.trim().is_empty() && !rubric.trim().is_empty(),
            "assessment scope must be explicit"
        );
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        let beliefs = self
            .learning_beliefs_for_ids(&tx, &HashSet::from([belief_id]))
            .await?;
        validate_targets(&beliefs, project, [belief_id].into_iter())?;
        let row = tx.query_one("SELECT COALESCE(sum(a.positive),0), COALESCE(sum(a.negative),0), COALESCE(sum(a.benefit),0), COALESCE(sum(a.benefit_weight),0), count(*), count(*) FILTER (WHERE a.positive+a.negative=0), count(*) FILTER (WHERE a.benefit_weight=0) FROM mimir_assessment_contributions a JOIN mimir_experiences e ON e.id=a.experience_id JOIN mimir_review_versions r ON r.experience_id=e.id AND r.revision=a.review_revision WHERE e.project=$1 AND a.belief_id=$2 AND a.scope=$3 AND a.rubric=$4 AND e.review_revision=r.revision AND e.revision=r.experience_revision", &[&project,&belief_id,&scope,&rubric]).await?;
        let scores = crate::assessment::Scores::from_totals(
            row.get(0),
            row.get(1),
            row.get(2),
            row.get(3),
            row.get(4),
            row.get(5),
            row.get(6),
        )?;
        Ok(
            serde_json::json!({"project":project,"belief_id":belief_id,"scope":scope,"rubric":rubric,"scores":scores}),
        )
    }
    pub async fn lesson_assessment_history(
        &self,
        project: &str,
        belief_id: Uuid,
        scope: &str,
        rubric: &str,
        offset: usize,
        limit: usize,
    ) -> Result<serde_json::Value> {
        ensure!(
            limit > 0 && offset <= i64::MAX as usize,
            "invalid history page"
        );
        ensure!(!project.trim().is_empty(), "project must be explicit");
        let client = self.client.lock().await;
        let rows = client.query("SELECT a.experience_id,a.review_revision,r.experience_revision,a.payload::text,r.created_at,(e.review_revision=r.revision AND e.revision=r.experience_revision) AS active FROM mimir_assessment_contributions a JOIN mimir_experiences e ON e.id=a.experience_id JOIN mimir_review_versions r ON r.experience_id=e.id AND r.revision=a.review_revision WHERE e.project=$1 AND a.belief_id=$2 AND a.scope=$3 AND a.rubric=$4 ORDER BY r.created_at,a.experience_id,a.review_revision LIMIT $5 OFFSET $6", &[&project,&belief_id,&scope,&rubric,&(i64::try_from(limit)?.checked_add(1).ok_or_else(|| anyhow::anyhow!("page size exceeds PostgreSQL integer range"))?),&(offset as i64)]).await?;
        let entries = rows.iter().take(limit).map(|r| Ok(serde_json::json!({"experience_id":r.get::<_,Uuid>(0),"review_revision":r.get::<_,i64>(1),"experience_revision":r.get::<_,i64>(2),"assessment":serde_json::from_str::<serde_json::Value>(r.get::<_,&str>(3))?,"created_at":r.get::<_,chrono::DateTime<chrono::Utc>>(4),"active":r.get::<_,bool>(5)}))).collect::<Result<Vec<_>>>()?;
        Ok(
            serde_json::json!({"entries":entries,"next_offset":if rows.len()>limit {Some(offset.checked_add(limit).ok_or_else(|| anyhow::anyhow!("page offset exceeds platform range"))?)}else{None}}),
        )
    }
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
        self.list_experiences_excluding(project, pending, limit, &[])
            .await
    }
    pub async fn list_experiences_excluding(
        &self,
        project: Option<&str>,
        pending: bool,
        limit: usize,
        excluded: &[Uuid],
    ) -> Result<Vec<ExperienceState>> {
        self.select_experiences(project, pending, Some(limit), excluded)
            .await
    }

    pub async fn select_experiences(
        &self,
        project: Option<&str>,
        pending: bool,
        count: Option<usize>,
        excluded: &[Uuid],
    ) -> Result<Vec<ExperienceState>> {
        ensure!(
            count.is_none_or(|count| count > 0),
            "An explicit selection count must be positive; omit it to select all pending work"
        );
        let count = count.map(i64::try_from).transpose()?;
        let client = self.client.lock().await;
        client.query(&format!("{CURRENT} WHERE ($1::text IS NULL OR e.project=$1) AND (NOT $2 OR e.reviewed_revision<e.revision) AND NOT (e.id = ANY($4::uuid[])) ORDER BY e.updated_at,v.created_at LIMIT $3"), &[&project, &pending, &count, &excluded]).await?.iter().map(state).collect()
    }
    /// One snapshot: stale review data is never presented as current coverage.
    pub async fn learning_review(&self, id: Uuid) -> Result<serde_json::Value> {
        let client = self.client.lock().await;
        let row=client.query_opt("SELECT e.revision,e.review_revision,e.reviewed_revision,r.payload::text FROM mimir_experiences e LEFT JOIN mimir_review_versions r ON r.experience_id=e.id AND r.revision=e.review_revision AND r.experience_revision=e.revision WHERE e.id=$1", &[&id]).await?;
        row.map(|r| Ok(serde_json::json!({"experience_id":id,"revision":r.get::<_,i64>(0),"review_revision":r.get::<_,i64>(1),"reviewed_revision":r.get::<_,i64>(2),"review":r.get::<_,Option<&str>>(3).map(serde_json::from_str::<serde_json::Value>).transpose()?}))).transpose().map(|v|v.unwrap_or(serde_json::Value::Null))
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
    async fn learning_beliefs_for_ids(
        &self,
        tx: &Transaction<'_>,
        ids: &HashSet<Uuid>,
    ) -> Result<Vec<Belief>> {
        if ids.is_empty() {
            return Ok(Vec::new());
        }
        let g = &self.graph_name;
        let ids = uuid_list(ids);
        let sql = format!("SELECT id::text,content::text,probability::text,confidence::text,alpha::text,beta::text,alpha0::text,beta0::text,created_at::text,last_activated_at::text,memory_type::text,project::text FROM ag_catalog.cypher('{g}', $$ MATCH (n:Belief) WHERE n.id IN [{ids}] RETURN n.id,n.content,n.probability,n.confidence,n.alpha,n.beta,n.alpha0,n.beta0,n.created_at,n.last_activated_at,n.memory_type,n.project $$) {BELIEF_RETURN_COLUMNS}");
        tx.query(&sql, &[])
            .await?
            .iter()
            .map(belief_from_row)
            .collect()
    }
    pub(super) async fn active_reviews(tx: &Transaction<'_>) -> Result<Vec<Review>> {
        tx.query(ACTIVE_REVIEWS, &[])
            .await?
            .iter()
            .map(|r| Ok(serde_json::from_str(r.get::<_, &str>(0))?))
            .collect()
    }
    async fn active_reviews_for_targets(
        tx: &Transaction<'_>,
        project: Option<&str>,
        targets: &HashSet<Uuid>,
    ) -> Result<Vec<Review>> {
        if targets.is_empty() {
            return Ok(Vec::new());
        }
        let ids: Vec<Uuid> = targets.iter().copied().collect();
        let sql = format!("{ACTIVE_REVIEWS} WHERE ($1::text IS NULL OR e.project=$1) AND EXISTS (SELECT 1 FROM jsonb_array_elements(COALESCE(r.payload->'feedback','[]'::jsonb)) AS f WHERE (f->>'belief_id')::uuid=ANY($2))");
        tx.query(&sql, &[&project, &ids])
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
    async fn active_request(tx: &Transaction<'_>, id: Uuid) -> Result<Option<Review>> {
        tx.query_opt("SELECT COALESCE(r.request,r.payload)::text FROM mimir_experiences e JOIN mimir_review_versions r ON r.experience_id=e.id AND r.revision=e.review_revision AND r.experience_revision=e.revision WHERE e.id=$1", &[&id])
            .await?
            .map(|row| Ok(serde_json::from_str(row.get::<_, &str>(0))?))
            .transpose()
    }
    async fn candidate_ids(
        tx: &Transaction<'_>,
        experience_id: Uuid,
        candidates: &[Candidate],
    ) -> Result<HashMap<String, Uuid>> {
        let mut ids = HashMap::new();
        for candidate in candidates {
            let row = tx.query_opt("SELECT kind,node_id,declaration::text,retired FROM mimir_review_candidates WHERE experience_id=$1 AND candidate_key=$2", &[&experience_id, &candidate.key()]).await?;
            let Some(row) = row else {
                anyhow::bail!("candidate key is not reserved");
            };
            let kind: &str = row.get(0);
            let declaration: serde_json::Value = serde_json::from_str(row.get(2))?;
            let retired: bool = row.get(3);
            if kind != candidate.kind() || declaration != serde_json::to_value(candidate)? {
                return Err(crate::validation::Refusal::candidate_conflict().into());
            }
            ensure!(!retired, "candidate identity was deleted");
            ids.insert(candidate.key().to_owned(), row.get(1));
        }
        Ok(ids)
    }
    async fn reserve_candidates(
        &self,
        tx: &Transaction<'_>,
        experience_id: Uuid,
        project: &str,
        candidates: &[Candidate],
    ) -> Result<HashMap<String, Uuid>> {
        let mut ids = HashMap::new();
        for candidate in candidates {
            if let Some(row) = tx.query_opt("SELECT kind,node_id,declaration::text,retired FROM mimir_review_candidates WHERE experience_id=$1 AND candidate_key=$2", &[&experience_id, &candidate.key()]).await? {
                let kind: &str = row.get(0);
                let declaration: serde_json::Value = serde_json::from_str(row.get(2))?;
                let retired: bool = row.get(3);
                if kind != candidate.kind() || declaration != serde_json::to_value(candidate)? {
                    return Err(crate::validation::Refusal::candidate_conflict().into());
                }
                ensure!(!retired, "candidate identity was deleted");
                ids.insert(candidate.key().to_owned(), row.get(1));
                continue;
            }
            let id = tx.query_one("SELECT gen_random_uuid()", &[]).await?.get(0);
            self.ensure_candidate_identity_free(tx, id).await?;
            self.create_candidate_node(tx, candidate, id, project)
                .await?;
            let declaration = serde_json::to_string(candidate)?;
            tx.execute("INSERT INTO mimir_review_candidates(experience_id,candidate_key,kind,node_id,declaration) VALUES($1,$2,$3,$4,$5::text::jsonb)", &[&experience_id,&candidate.key(),&candidate.kind(),&id,&declaration]).await?;
            ids.insert(candidate.key().to_owned(), id);
        }
        Ok(ids)
    }
    async fn create_candidate_node(
        &self,
        tx: &Transaction<'_>,
        candidate: &Candidate,
        id: Uuid,
        project: &str,
    ) -> Result<()> {
        let g = &self.graph_name;
        let project_json = json_esc(project);
        match candidate {
            Candidate::Belief {
                content,
                memory_type,
                ..
            } => {
                let mut belief =
                    Belief::new_in_project(content.clone(), 0.5, 0.0, project.to_owned())?
                        .with_memory_type(*memory_type);
                belief.id = id;
                let args = format!(
                    r#"{{"id":"{id}","content":"{}","project":"{project_json}","created_at":"{}","last_activated_at":"{}","memory_type":"{}"}}"#,
                    json_esc(&belief.content),
                    belief.created_at.to_rfc3339(),
                    belief.last_activated_at.to_rfc3339(),
                    belief.memory_type.as_str()
                );
                let stmt = format!("candidate_b_{}", id.simple());
                let sql = format!("PREPARE {stmt}(agtype) AS SELECT * FROM ag_catalog.cypher('{g}', $$ CREATE (n:Belief {{id:$id,content:$content,project:$project,created_at:$created_at,last_activated_at:$last_activated_at,memory_type:$memory_type,probability:0.5,confidence:0.0,alpha:1.0,beta:1.0,alpha0:1.0,beta0:1.0}}) RETURN n.id $$,$1) AS (id ag_catalog.agtype)");
                age_execute(tx.client(), &stmt, &sql, &args).await?;
            }
            Candidate::Pattern {
                situation,
                approach,
                ..
            } => {
                let args = format!(
                    r#"{{"id":"{id}","situation":"{}","approach":"{}","project":"{project_json}","created_at":"{}"}}"#,
                    json_esc(situation),
                    json_esc(approach),
                    chrono::Utc::now().to_rfc3339()
                );
                let stmt = format!("candidate_p_{}", id.simple());
                let sql = format!("PREPARE {stmt}(agtype) AS SELECT * FROM ag_catalog.cypher('{g}', $$ CREATE (p:Pattern {{id:$id,situation:$situation,approach:$approach,project:$project,created_at:$created_at,activation_count:0,success_rate:0.5}}) RETURN p.id $$,$1) AS (id ag_catalog.agtype)");
                age_execute(tx.client(), &stmt, &sql, &args).await?;
            }
        }
        Ok(())
    }
    pub async fn learning_overlay(&self) -> Result<(HashMap<Uuid, (f64, f64)>, HashSet<Uuid>)> {
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
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
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let prior = tx
            .query_opt(&format!("{CURRENT} WHERE e.id=$1"), &[&experience.id])
            .await?
            .as_ref()
            .map(state)
            .transpose()?;
        if prior.is_none() {
            ensure!(expected == 0, "new experience requires expected_revision=0");
            // The ownership FK needs its experience row. All validation and
            // allocation below still roll back together on any refusal.
            tx.execute(
                "INSERT INTO mimir_experiences(id,project,revision) VALUES($1,$2,1)",
                &[&experience.id, &experience.project],
            )
            .await?;
        }
        let mut allocated = experience.clone();
        Self::resolve_item_ids(&tx, experience.id, &mut allocated.learning_items).await?;
        let experience = &allocated;
        let payload = serde_json::to_string(experience)?;
        if let Some(ref p) = prior {
            ensure!(
                p.experience.project == experience.project,
                "experience project is immutable"
            );
            for source in &p.experience.source_records {
                ensure!(
                    experience.source_records.contains(source),
                    "source corrections must retain original records; append a correction source"
                );
            }
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
        let target_ids: HashSet<_> = experience.belief_ids.iter().copied().collect();
        let beliefs = self.learning_beliefs_for_ids(&tx, &target_ids).await?;
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
        self.recompute_learning(&tx, Some(&experience.project), affected)
            .await?;
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
        self.review_experience_inner(review, expected, None).await
    }

    pub(crate) async fn existing_belief_candidates(
        &self,
        experience_id: Uuid,
    ) -> Result<HashSet<String>> {
        let client = self.client.lock().await;
        Ok(client.query("SELECT candidate_key FROM mimir_review_candidates WHERE experience_id=$1 AND kind='belief' AND NOT retired", &[&experience_id]).await?
            .into_iter().map(|row| row.get(0)).collect())
    }

    pub(crate) async fn review_supported_experience(
        &self,
        review: &Review,
        expected: i64,
        materials: &HashMap<String, (Uuid, Vec<f32>)>,
    ) -> Result<ExperienceState> {
        self.review_experience_inner(review, expected, Some(materials))
            .await
    }

    async fn review_experience_inner(
        &self,
        review: &Review,
        expected: i64,
        materials: Option<&HashMap<String, (Uuid, Vec<f32>)>>,
    ) -> Result<ExperienceState> {
        review
            .validate()
            .map_err(crate::validation::Refusal::validation)?;
        ensure!(
            (0..i64::MAX).contains(&expected),
            "expected_review_revision must be nonnegative"
        );
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
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
        let old_request = Self::active_request(&tx, review.experience_id).await?;
        if let Some(old) = old_request.as_ref() {
            if old == review
                && (expected == current.review_revision || expected == current.review_revision - 1)
            {
                let mut result = current;
                result.candidate_ids =
                    Self::candidate_ids(&tx, review.experience_id, &review.candidates).await?;
                if let Some(applied) = Self::active_review(&tx, review.experience_id).await? {
                    result
                        .item_ids
                        .extend(local_item_ids(&applied.extracted_items));
                }
                return Ok(result);
            }
        }
        ensure!(
            expected == current.review_revision,
            "stale review revision: current is {}",
            current.review_revision
        );
        let request = serde_json::to_string(review)?;
        let mut allocated = review.clone();
        Self::resolve_item_ids(&tx, review.experience_id, &mut allocated.extracted_items).await?;
        Self::resolve_item_references(&tx, &mut allocated).await?;
        let review = &allocated;
        crate::learning_sources::validate_review(review, &current.experience)
            .map_err(crate::validation::Refusal::validation)?;
        if let Some(prior)=tx.query_opt("SELECT payload::text FROM mimir_review_versions WHERE experience_id=$1 AND revision=$2", &[&review.experience_id,&current.review_revision]).await? {
            let prior:Review=serde_json::from_str(prior.get(0))?;
            for item in prior.extracted_items {
                ensure!(review.extracted_items.iter().any(|i|i.id==item.id && i.source_ref==item.source_ref && i.actor==item.actor && i.statement==item.statement && i.kind==item.kind),"review corrections must retain extracted identities and original quotations");
            }
        }

        let old_review = Self::active_review(&tx, review.experience_id).await?;
        let existing: HashSet<String> = tx
            .query(
                "SELECT candidate_key FROM mimir_review_candidates WHERE experience_id=$1",
                &[&review.experience_id],
            )
            .await?
            .into_iter()
            .map(|row| row.get(0))
            .collect();
        let candidate_ids = self
            .reserve_candidates(
                &tx,
                review.experience_id,
                &current.experience.project,
                &review.candidates,
            )
            .await?;
        if let Some(materials) = materials {
            for candidate in &review.candidates {
                if let Candidate::Belief {
                    key,
                    supporting_passage_id,
                    ..
                } = candidate
                {
                    if existing.contains(key) {
                        continue;
                    }
                    let (passage, embedding) = materials.get(key).ok_or_else(|| anyhow::anyhow!(
                        "New belief '{key}' has no prepared embedding and supporting passage. No review changes were saved; select an indexed supporting passage and resubmit."))?;
                    ensure!(Some(*passage) == *supporting_passage_id, "The prepared source does not match the selected passage; no review changes were saved.");
                    self.publish_belief_material_on(
                        tx.client(),
                        candidate_ids[key],
                        Some(&current.experience.project),
                        embedding,
                        *passage,
                    )
                    .await?;
                }
            }
        }
        let applied = materialize_review(review, &candidate_ids)?;
        applied.validate()?;
        let ids: HashSet<_> = applied
            .feedback
            .iter()
            .map(|f| f.belief_id)
            .chain(applied.superseded_beliefs.iter().copied())
            .chain(applied.links.iter().flat_map(|l| [l.from_id, l.to_id]))
            .chain(applied.assessments.iter().filter_map(|a| match a.target {
                BeliefTarget::Existing { belief_id } => Some(belief_id),
                _ => None,
            }))
            .collect();
        let beliefs = self.learning_beliefs_for_ids(&tx, &ids).await?;
        validate_targets(&beliefs, &current.experience.project, ids.iter().copied())?;
        let mut assessed = current.experience.clone();
        assessed
            .learning_items
            .extend(applied.extracted_items.clone());
        for assessment in &applied.assessments {
            assessment.validate_source(&assessed)?;
        }
        ensure!(
            applied.feedback.is_empty()
                && applied.links.is_empty()
                && applied.superseded_beliefs.is_empty()
                && applied.candidates.is_empty()
                || current
                    .experience
                    .evidence
                    .iter()
                    .any(|e| !e.trim().is_empty()),
            "learning requires recorded evidence"
        );
        let mut affected = review_targets(old_review.iter());
        affected.extend(review_targets(std::iter::once(&applied)));
        let revision = expected + 1;
        let payload = serde_json::to_string(&applied)?;
        tx.execute("INSERT INTO mimir_review_versions(experience_id,revision,experience_revision,payload,request) VALUES($1,$2,$3,$4::text::jsonb,$5::text::jsonb)", &[&review.experience_id,&revision,&review.experience_revision,&payload,&request]).await?;
        tx.execute("UPDATE mimir_experiences SET review_revision=$2,reviewed_revision=revision WHERE id=$1", &[&review.experience_id,&revision]).await?;
        for a in &applied.assessments {
            let BeliefTarget::Existing { belief_id } = a.target else {
                anyhow::bail!("unresolved assessment target")
            };
            let positive = a.correctness.weight * a.correctness.value.unwrap_or(0.);
            let negative = a.correctness.weight * (1. - a.correctness.value.unwrap_or(0.));
            let benefit = a.usefulness.weight * a.usefulness.value.unwrap_or(0.);
            let payload = serde_json::to_string(a)?;
            tx.execute("INSERT INTO mimir_assessment_contributions(experience_id,review_revision,belief_id,scope,rubric,positive,negative,benefit,benefit_weight,payload) VALUES($1,$2,$3,$4,$5,$6,$7,$8,$9,$10::text::jsonb)",
                &[&review.experience_id,&revision,&belief_id,&a.scope,&a.rubric,&positive,&negative,&benefit,&a.usefulness.weight,&payload]).await?;
        }
        self.replace_review_edges(&tx, review.experience_id, &applied.links)
            .await?;
        self.recompute_learning(&tx, Some(&current.experience.project), affected)
            .await?;
        let mut result = state(
            &tx.query_one(
                &format!("{CURRENT} WHERE e.id=$1"),
                &[&review.experience_id],
            )
            .await?,
        )?;
        result.candidate_ids = candidate_ids;
        result
            .item_ids
            .extend(local_item_ids(&applied.extracted_items));
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
    pub(super) async fn recompute_learning(
        &self,
        tx: &Transaction<'_>,
        project: Option<&str>,
        mut affected: HashSet<Uuid>,
    ) -> Result<()> {
        if affected.is_empty() {
            return Ok(());
        }
        let g = &self.graph_name;
        // Expand only within the experience project. Outside parents are read
        // later as fixed inputs, never added to the write set.
        let mut frontier = affected.clone();
        while !frontier.is_empty() {
            let source_ids = uuid_list(&frontier);
            let rows = tx.query(&format!("SELECT target::text,label::text,project::text FROM ag_catalog.cypher('{g}', $$ MATCH (a:Belief)-[r]->(b:Belief) WHERE a.id IN [{source_ids}] RETURN b.id,type(r),b.project $$) AS (target ag_catalog.agtype,label ag_catalog.agtype,project ag_catalog.agtype)"), &[]).await?;
            let mut next = HashSet::new();
            for row in rows {
                let label: &str = row.get(1);
                let owner: Option<&str> = row.get(2);
                if label == "CONTRADICTS" || project.is_some_and(|p| owner != Some(p)) {
                    continue;
                }
                let target = Uuid::parse_str(row.get(0))?;
                if affected.insert(target) {
                    next.insert(target);
                }
            }
            frontier = next;
        }
        let beliefs = self.learning_beliefs_for_ids(tx, &affected).await?;
        // Explicit deletion can retire a former review target. The deleted
        // identity remains in history, but there is no posterior to update.
        affected = beliefs.iter().map(|b| b.id).collect();
        if affected.is_empty() {
            return Ok(());
        }
        ensure!(
            beliefs
                .iter()
                .all(|b| project.is_none_or(|p| b.project.as_deref() == Some(p))),
            "review recomputation must stay in the experience project"
        );
        let ids = uuid_list(&affected);
        let rows = tx.query(&format!("SELECT a::text,b::text,label::text,w::text,p::text FROM ag_catalog.cypher('{g}', $$ MATCH (a:Belief)-[r]->(b:Belief) WHERE b.id IN [{ids}] RETURN a.id,b.id,type(r),r.weight,a.probability $$) AS (a ag_catalog.agtype,b ag_catalog.agtype,label ag_catalog.agtype,w ag_catalog.agtype,p ag_catalog.agtype)"), &[]).await?;
        let mut external = HashMap::new();
        let edges: Vec<_> = rows
            .iter()
            .map(|r| -> Result<_> {
                let source = Uuid::parse_str(r.get(0))?;
                if !affected.contains(&source) {
                    external.insert(source, r.get::<_, &str>(4).parse()?);
                }
                Ok((
                    source,
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
        let (mut mass, _) =
            overlay(&Self::active_reviews_for_targets(tx, project, &affected).await?);
        let ground = tx.query(&format!("SELECT id::text,w::text FROM ag_catalog.cypher('{g}', $$ MATCH (:DocumentChunk)-[r:GROUNDS]->(b:Belief) WHERE b.id IN [{ids}] RETURN b.id,sum(r.weight) $$) AS (id ag_catalog.agtype,w ag_catalog.agtype)"), &[]).await?;
        for row in ground {
            let id = Uuid::parse_str(row.get(0))?;
            let weight: f64 = row.get::<_, &str>(1).parse()?;
            mass.entry(id).or_insert((0.0, 0.0)).0 += EVIDENCE_MASS_K * weight;
        }
        let mut downstream = beliefs;
        for b in &mut downstream {
            if let Some((a, z)) = mass.get(&b.id) {
                b.alpha0 += a;
                b.beta0 += z;
            }
        }
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

fn resolve_belief_target(
    target: &BeliefTarget,
    candidates: &[Candidate],
    ids: &HashMap<String, Uuid>,
) -> Result<Uuid> {
    match target {
        BeliefTarget::Existing { belief_id } => Ok(*belief_id),
        BeliefTarget::Candidate { candidate_key } => {
            ensure!(
                candidates
                    .iter()
                    .any(|c| matches!(c, Candidate::Belief { key, .. } if key == candidate_key)),
                "candidate belief reference must be declared in this review"
            );
            ids.get(candidate_key)
                .copied()
                .ok_or_else(|| anyhow::anyhow!("candidate belief key is unresolved"))
        }
    }
}

fn materialize_review(requested: &Review, ids: &HashMap<String, Uuid>) -> Result<Review> {
    let mut applied = requested.clone();
    for a in &mut applied.assessments {
        a.target = BeliefTarget::Existing {
            belief_id: resolve_belief_target(&a.target, &requested.candidates, ids)?,
        };
    }
    for f in &requested.candidate_feedback {
        applied.feedback.push(Feedback {
            belief_id: resolve_belief_target(&f.target, &requested.candidates, ids)?,
            verdict: f.verdict,
            weight: f.weight,
        });
    }
    for link in &requested.candidate_links {
        applied.links.push(LearningLink {
            from_id: resolve_belief_target(&link.from, &requested.candidates, ids)?,
            to_id: resolve_belief_target(&link.to, &requested.candidates, ids)?,
            relation: link.relation,
            weight: link.weight,
        });
    }
    applied.candidate_feedback.clear();
    applied.candidate_links.clear();
    Ok(applied)
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
pub(super) fn overlay(reviews: &[Review]) -> (HashMap<Uuid, (f64, f64)>, HashSet<Uuid>) {
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
    pub async fn independent_provenance(&self, id: Uuid) -> Result<Option<IndependentProvenance>> {
        let client = self.client.lock().await;
        let g = &self.graph_name;
        let rows = client.query(&format!("SELECT basis::text,reference::text FROM ag_catalog.cypher('{g}', $$ MATCH (n:Belief {{id:'{id}'}}) RETURN n.origin_basis,n.origin_reference $$) AS (basis ag_catalog.agtype,reference ag_catalog.agtype)"), &[]).await?;
        let Some(row) = rows.first() else {
            return Ok(None);
        };
        let basis: Option<&str> = row.get(0);
        let reference: Option<&str> = row.get(1);
        let source = match (basis, reference) {
            (Some("user_instruction"), Some(reference)) => Some(IndependentProvenance {
                basis: IndependentBasis::UserInstruction,
                reference: reference.into(),
            }),
            (Some("document"), Some(reference)) => Some(IndependentProvenance {
                basis: IndependentBasis::Document,
                reference: reference.into(),
            }),
            (None | Some("null"), None | Some("null")) => None,
            _ => anyhow::bail!("invalid stored direct provenance"),
        };
        Ok(source)
    }

    pub async fn candidate_provenance(&self, id: Uuid) -> Result<Option<CandidateProvenance>> {
        let client = self.client.lock().await;
        let row = client.query_opt("SELECT c.experience_id,c.candidate_key,c.kind,c.retired, (NOT c.retired AND EXISTS (SELECT 1 FROM jsonb_array_elements(COALESCE(r.payload->'candidates','[]'::jsonb)) AS item WHERE item->>'key'=c.candidate_key)) AS active FROM mimir_review_candidates c JOIN mimir_experiences e ON e.id=c.experience_id LEFT JOIN mimir_review_versions r ON r.experience_id=e.id AND r.revision=e.review_revision AND r.experience_revision=e.revision WHERE c.node_id=$1", &[&id]).await?;
        Ok(row.map(|r| CandidateProvenance {
            experience_id: r.get(0),
            candidate_key: r.get(1),
            kind: r.get(2),
            retired: r.get(3),
            active: r.get(4),
        }))
    }
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
        drop(client);
        let candidate_provenance = self.candidate_provenance(pattern.id).await?;
        Ok(PatternResult {
            pattern,
            successes,
            failures,
            unknown,
            observed_success_probability: (1.0 + successes as f64)
                / (2.0 + successes as f64 + failures as f64),
            candidate_provenance,
        })
    }
    pub async fn delete_learning_project(&self, project: &str) -> Result<()> {
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
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
        ensure!(limit > 0, "limit must be positive");
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        let id_text = id.to_string();
        let sql = format!("{ACTIVE_REVIEWS} WHERE EXISTS (SELECT 1 FROM jsonb_array_elements(COALESCE(r.payload->'feedback','[]'::jsonb)) f WHERE f->>'belief_id'=$1) OR EXISTS (SELECT 1 FROM jsonb_array_elements_text(COALESCE(r.payload->'superseded_beliefs','[]'::jsonb)) s WHERE s=$1) OR EXISTS (SELECT 1 FROM jsonb_array_elements(COALESCE(r.payload->'links','[]'::jsonb)) l WHERE l->>'from_id'=$1 OR l->>'to_id'=$1)");
        let mut reviews: Vec<Review> = tx
            .query(&sql, &[&id_text])
            .await?
            .iter()
            .map(|row| serde_json::from_str(row.get::<_, &str>(0)))
            .collect::<std::result::Result<_, _>>()?;
        reviews.sort_by_key(|r| r.experience_id);
        let total = reviews.len();
        let page: Vec<_> = reviews.into_iter().skip(offset).take(limit).collect();
        let next = offset.saturating_add(page.len());
        Ok(
            serde_json::json!({"reviews":page,"total":total,"next_offset":if next<total {Some(next)} else {None}}),
        )
    }
}
