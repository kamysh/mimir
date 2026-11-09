//! Transaction boundaries and closure required by the checked application contracts.
use super::*;
use anyhow::ensure;
use std::collections::{BTreeMap, HashSet};
use tokio_postgres::Transaction;

impl AgeStore {
    // GraphPaths.Returned: arbitrary mixtures of propagation relations, with
    // no depth bound and one result per identity. A nonempty cycle may reach
    // the seed; the inference engine separately clamps it.
    pub(crate) async fn downstream_on(
        &self,
        client: &Client,
        seed: Uuid,
        causal_only: bool,
    ) -> Result<Vec<Belief>> {
        let g = &self.graph_name;
        let mut reached = BTreeMap::new();
        let mut expanded = HashSet::new();
        let mut frontier = vec![seed];
        while !frontier.is_empty() {
            frontier.retain(|id| expanded.insert(*id));
            if frontier.is_empty() {
                break;
            }
            let ids = frontier
                .iter()
                .map(|id| format!("'{id}'"))
                .collect::<Vec<_>>()
                .join(",");
            let labels = if causal_only {
                &["CAUSES"][..]
            } else {
                &["SUPPORTS", "CAUSES", "DEFEATS"][..]
            };
            let arms = labels.iter().map(|label| format!(
                "MATCH (s:Belief)-[:{label}]->(n:Belief) WHERE s.id IN [{ids}] RETURN n.id,n.content,n.probability,n.confidence,n.alpha,n.beta,n.alpha0,n.beta0,n.created_at,n.last_activated_at,n.memory_type,n.project"
            )).collect::<Vec<_>>().join(" UNION ");
            let sql = format!("SELECT id::text,content::text,probability::text,confidence::text,alpha::text,beta::text,alpha0::text,beta0::text,created_at::text,last_activated_at::text,memory_type::text,project::text FROM ag_catalog.cypher('{g}', $$ {arms} $$) {BELIEF_RETURN_COLUMNS}");
            frontier.clear();
            for row in client.query(&sql, &[]).await? {
                let belief = belief_from_row(&row)?;
                if !expanded.contains(&belief.id) {
                    frontier.push(belief.id);
                }
                reached.insert(belief.id, belief);
            }
        }
        Ok(reached.into_values().collect())
    }

    pub(super) async fn propagate_in(
        &self,
        tx: &Transaction<'_>,
        seed_id: Uuid,
    ) -> Result<Vec<(Uuid, Probability)>> {
        let seed = self
            .get_belief_on(tx.client(), seed_id)
            .await?
            .ok_or_else(|| anyhow::anyhow!("belief {seed_id} not found"))?;
        let mut downstream = self.downstream_on(tx.client(), seed_id, false).await?;
        let (learning_mass, _) = learning::overlay(&Self::active_reviews(tx).await?);
        let grounding = self.get_grounding_mass_all_on(tx.client()).await?;
        for belief in &mut downstream {
            belief.alpha0 += grounding.get(&belief.id).copied().unwrap_or(0.0);
            if let Some((a, b)) = learning_mass.get(&belief.id) {
                belief.alpha0 += a;
                belief.beta0 += b;
            }
        }
        let mut ids: Vec<_> = downstream.iter().map(|b| b.id).collect();
        ids.push(seed_id);
        let incoming = self.get_incoming_edges_on(tx.client(), &ids).await?;
        let edges = crate::strip_source_means(&incoming);
        let external = crate::external_means_from(&incoming, &ids);
        let updates = crate::inference::InferenceEngine::new().propagate_defeat(
            &seed,
            &downstream,
            &edges,
            &external,
        )?;
        let writes: Vec<_> = updates.iter().map(|&(id, (a, b))| (id, a, b)).collect();
        self.update_beliefs_beta_on(tx.client(), &writes).await?;
        updates
            .into_iter()
            .map(|(id, (a, b))| Ok((id, Probability::new(crate::graph::beta_mean(a, b))?)))
            .collect()
    }

    pub(crate) async fn propagate_locked(&self, seed_id: Uuid) -> Result<Vec<(Uuid, Probability)>> {
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let result = self.propagate_in(&tx, seed_id).await?;
        tx.commit().await?;
        Ok(result)
    }

    pub(crate) async fn decay_locked(&self, factor: f64, project: Option<&str>) -> Result<usize> {
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let beliefs = match project {
            Some(project) => {
                self.list_beliefs_by_project_on(tx.client(), project)
                    .await?
            }
            None => self.list_beliefs_on(tx.client()).await?,
        };
        let grounding = self.get_grounding_mass_all_on(tx.client()).await?;
        let updates = crate::inference::InferenceEngine::new().decay_all(
            &beliefs,
            chrono::Utc::now(),
            factor,
            &grounding,
        )?;
        let writes: Vec<_> = updates.into_iter().map(|(id, (a, b))| (id, a, b)).collect();
        self.update_beliefs_beta_on(tx.client(), &writes).await?;
        tx.commit().await?;
        Ok(writes.len())
    }

    pub(super) async fn ensure_candidate_identity_free(
        &self,
        tx: &Transaction<'_>,
        id: Uuid,
    ) -> Result<()> {
        let g = &self.graph_name;
        let nodes = tx.query(&format!("SELECT id::text FROM ag_catalog.cypher('{g}', $$ MATCH (n) WHERE n.id = '{id}' RETURN n.id $$) AS (id ag_catalog.agtype)"), &[]).await?;
        let reservation = tx
            .query_opt(
                "SELECT node_id FROM mimir_review_candidates WHERE node_id=$1",
                &[&id],
            )
            .await?;
        ensure!(
            nodes.is_empty() && reservation.is_none(),
            "generated candidate identity is already occupied"
        );
        Ok(())
    }

    pub async fn replace_document(
        &self,
        path: &str,
        chunks: &[DocumentChunk],
        vectors: &[Vec<f32>],
    ) -> Result<()> {
        validate_document_batch(path, chunks, vectors)?;
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let old = self
            .get_chunk_ids_for_document_on(tx.client(), path)
            .await?;
        let proposed: HashSet<_> = chunks.iter().map(|c| c.id).collect();
        let g = &self.graph_name;
        // Validate against retained chunk identities before deleting anything.
        for row in tx.query(&format!("SELECT id::text FROM ag_catalog.cypher('{g}', $$ MATCH (c:DocumentChunk) RETURN c.id $$) AS (id ag_catalog.agtype)"), &[]).await? {
            let id = Uuid::parse_str(row.get(0))?;
            ensure!(!proposed.contains(&id) || old.contains(&id), "generated chunk identity is already occupied");
        }
        self.delete_document_chunks_in(&tx, &old).await?;
        self.delete_chunk_embeddings_on(tx.client(), &old).await?;
        for (chunk, vector) in chunks.iter().zip(vectors) {
            self.insert_document_chunk_on(tx.client(), chunk).await?;
            self.insert_chunk_embedding_on(tx.client(), chunk.id, vector)
                .await?;
        }
        tx.commit().await?;
        Ok(())
    }

    pub async fn clear_document(&self, path: &str) -> Result<usize> {
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let old = self
            .get_chunk_ids_for_document_on(tx.client(), path)
            .await?;
        self.delete_document_chunks_in(&tx, &old).await?;
        self.delete_chunk_embeddings_on(tx.client(), &old).await?;
        tx.commit().await?;
        Ok(old.len())
    }
}

fn validate_document_batch(
    path: &str,
    chunks: &[DocumentChunk],
    vectors: &[Vec<f32>],
) -> Result<()> {
    ensure!(
        chunks.len() == vectors.len(),
        "document embedding count does not match chunks"
    );
    let mut ids = HashSet::new();
    for chunk in chunks {
        ensure!(
            chunk.document_path == path,
            "replacement contains a different document"
        );
        ensure!(ids.insert(chunk.id), "duplicate generated chunk identity");
    }
    if let Some(first) = vectors.first() {
        ensure!(
            vectors.iter().all(|v| v.len() == first.len()),
            "inconsistent document embedding dimensions"
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Context;
    use std::future::poll_fn;
    use tokio_postgres::{AsyncMessage, NoTls};
    #[allow(dead_code)] // Test-only adapter for the shared integration guard.
    mod isolation {
        use crate as mimir_core;
        include!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/support/isolation.rs"
        ));
    }

    #[tokio::test]
    async fn propagation_waits_for_learning_lock_before_reading_seed() -> Result<()> {
        let cfg = isolation::fixture().database_config();
        crate::db::migrate(&cfg).await?;
        let mut owner = crate::db::connect(&cfg).await?;
        let identity: Uuid = owner
            .query_one("SELECT gen_random_uuid()", &[])
            .await?
            .get(0);
        let schema = format!("mimir_lock_{}", identity.simple());
        let notice = format!("mimir lock entry {identity}");
        let project = format!("lock-fixture-{identity}");
        let seed =
            isolation::seed_belief_in_project("seed", 0.1, 0.0, &project, MemoryType::Fact).await?;
        let target =
            isolation::seed_belief_in_project("target", 0.5, 0.0, &project, MemoryType::Fact)
                .await?;
        let store = AgeStore::new(crate::db::connect(&cfg).await?, cfg.dbname.clone())?;
        store
            .insert_edge(&Edge::new(seed.id, target.id, EdgeType::Supports, 1.0)?)
            .await?;

        // Only this test connection resolves the wrapper. The actual database
        // lock is still taken, and all application statements remain unchanged.
        owner.batch_execute(&format!("CREATE SCHEMA {schema}; CREATE FUNCTION {schema}.pg_advisory_xact_lock(lock_key bigint) RETURNS void LANGUAGE plpgsql AS $$ BEGIN RAISE NOTICE '{notice}'; PERFORM pg_catalog.pg_advisory_xact_lock(lock_key); END $$")).await?;
        let mut pg = tokio_postgres::Config::new();
        pg.keepalives(false);
        pg.host(&cfg.host)
            .port(cfg.port)
            .dbname(&cfg.dbname)
            .user(&cfg.user);
        pg.options(format!(
            "-c search_path={schema},pg_catalog,public,ag_catalog"
        ));
        if let Some(password) = crate::password::resolve(
            cfg.password.as_deref(),
            cfg.pgpassfile.as_deref(),
            &cfg.host,
            cfg.port,
            &cfg.dbname,
            &cfg.user,
        ) {
            pg.password(password);
        }
        let (client, mut connection) = pg.connect(NoTls).await?;
        let (entered, mut observed) =
            tokio::sync::oneshot::channel::<std::result::Result<(), String>>();
        let driver = tokio::spawn(async move {
            let mut entered = Some(entered);
            while let Some(message) = poll_fn(|cx| connection.poll_message(cx)).await {
                match message {
                    Ok(AsyncMessage::Notice(message)) if message.message() == notice => {
                        if let Some(entered) = entered.take() {
                            let _ = entered.send(Ok(()));
                        }
                    }
                    Err(error) => {
                        if let Some(entered) = entered.take() {
                            let _ = entered.send(Err(error.to_string()));
                        }
                        return Err(error);
                    }
                    _ => {}
                }
            }
            Ok::<_, tokio_postgres::Error>(())
        });
        let selected: String = client.query_one("SELECT n.nspname FROM pg_proc p JOIN pg_namespace n ON n.oid=p.pronamespace WHERE p.oid=to_regprocedure('pg_advisory_xact_lock(bigint)')", &[]).await?.get(0);
        ensure!(
            selected == schema,
            "test connection did not select its own lock observer"
        );
        let propagator = Arc::new(AgeStore::new(client, cfg.dbname.clone())?);
        let mut pending = None;
        let outcome: Result<()> = async {
            let tx = owner.transaction().await?;
            tx.query("SELECT pg_advisory_xact_lock(671942183)", &[]).await?;
            let worker = propagator.clone();
            let seed_id = seed.id;
            pending = Some(tokio::spawn(async move { worker.propagate_locked(seed_id).await }));
            let premature = tokio::select! {
                entry = &mut observed => {
                    entry.context("lock-entry observer ended")?.map_err(anyhow::Error::msg)?;
                    None
                }
                completion = pending.as_mut().unwrap() => Some(completion),
            };
            if let Some(completion) = premature {
                pending.take();
                anyhow::bail!("propagation completed before entering the learning lock: {completion:?}");
            }
            let graph = &cfg.dbname;
            tx.query(&format!("SELECT * FROM ag_catalog.cypher('{graph}', $$ MATCH (b:Belief {{id:'{seed_id}'}}) SET b.alpha=9.0,b.beta=1.0,b.probability=0.9 RETURN b.id $$) AS (id ag_catalog.agtype)"), &[]).await?;
            tx.commit().await?;
            let values = pending.take().unwrap().await??;
            let actual = values.iter().find(|(id, _)| *id == target.id).context("target posterior missing")?.1.value();
            let expected = (target.alpha0 + 0.9 * crate::graph::EVIDENCE_UNIT) /
                (target.alpha0 + target.beta0 + 0.9 * crate::graph::EVIDENCE_UNIT);
            ensure!((actual - expected).abs() < 1e-10, "actual={actual}, expected={expected}");
            Ok(())
        }.await;
        if let Some(pending) = pending {
            pending.abort();
            let _ = pending.await;
        }
        drop(propagator);
        let driven = driver.await;
        let schema_removed = owner
            .batch_execute(&format!("DROP SCHEMA {schema} CASCADE"))
            .await;
        let project_removed = store.delete_project(&project).await;
        outcome?;
        driven??;
        schema_removed?;
        project_removed?;
        Ok(())
    }

    #[test]
    fn document_admission_checks_count_shape_path_and_duplicate_id() {
        let chunk = DocumentChunk::new("document".into(), vec![], "text".into(), None, None);
        assert!(validate_document_batch(
            "document",
            std::slice::from_ref(&chunk),
            &[vec![1.0, 0.0]]
        )
        .is_ok());
        assert!(validate_document_batch("document", std::slice::from_ref(&chunk), &[]).is_err());
        assert!(
            validate_document_batch("other", std::slice::from_ref(&chunk), &[vec![1.0]]).is_err()
        );
        assert!(validate_document_batch(
            "document",
            &[chunk.clone(), chunk.clone()],
            &[vec![1.0], vec![1.0]]
        )
        .is_err());
        let mut second = chunk.clone();
        second.id = Uuid::new_v4();
        assert!(validate_document_batch(
            "document",
            &[chunk, second],
            &[vec![1.0], vec![1.0, 2.0]]
        )
        .is_err());
    }

    #[tokio::test]
    async fn candidate_allocation_rejects_live_and_retired_occupied_ids() {
        let cfg = isolation::fixture().database_config();
        let dbname = cfg.dbname.clone();
        crate::db::migrate(&cfg).await.unwrap();
        let store = AgeStore::new(crate::db::connect(&cfg).await.unwrap(), dbname).unwrap();
        let project = format!("identity-fixture-{}", Uuid::new_v4());
        let live = Belief::new_in_project(
            "identity collision fixture".into(),
            0.5,
            0.0,
            project.clone(),
        )
        .unwrap();
        store.insert_belief(&live).await.unwrap();
        let mut client = store.client.lock().await;
        client
            .batch_execute("SET default_transaction_isolation TO 'repeatable read'")
            .await
            .unwrap();
        let tx = learning_transaction(&mut client).await.unwrap();
        let isolation: String = tx
            .query_one("SHOW transaction_isolation", &[])
            .await
            .unwrap()
            .get(0);
        assert_eq!(isolation, "read committed");
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await
            .unwrap();
        assert!(store
            .ensure_candidate_identity_free(&tx, Uuid::new_v4())
            .await
            .is_ok());
        assert!(store
            .ensure_candidate_identity_free(&tx, live.id)
            .await
            .is_err());
        let experience = Uuid::new_v4();
        let retired = Uuid::new_v4();
        tx.execute(
            "INSERT INTO mimir_experiences(id,project,revision) VALUES($1,'fixture',1)",
            &[&experience],
        )
        .await
        .unwrap();
        tx.execute("INSERT INTO mimir_review_candidates(experience_id,candidate_key,kind,node_id,declaration,retired) VALUES($1,'retired','belief',$2,'{}'::jsonb,true)", &[&experience,&retired]).await.unwrap();
        assert!(store
            .ensure_candidate_identity_free(&tx, retired)
            .await
            .is_err());
        tx.rollback().await.unwrap();
        drop(client);
        store.delete_project(&project).await.unwrap();
    }
}
