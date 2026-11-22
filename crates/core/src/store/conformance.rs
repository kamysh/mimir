//! Transaction boundaries and closure required by the checked application contracts.
use super::*;
use anyhow::{ensure, Context};
use std::collections::{BTreeMap, HashSet};
use tokio_postgres::Transaction;

impl AgeStore {
    // GraphPaths.Returned: arbitrary mixtures of propagation relations, with
    // no depth bound and one result per identity. A nonempty cycle may reach
    // the seed; the inference engine separately clamps it.
    pub(super) async fn downstream_on(
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
    ) -> Result<Vec<DocumentChunk>> {
        validate_document_batch(path, chunks, vectors)?;
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let old = self
            .get_chunk_ids_for_document_on(tx.client(), path)
            .await?;
        let drafts: Vec<_> = chunks.iter().map(|chunk| chunk.id).collect();
        let assigned: HashMap<Uuid, Uuid> = tx
            .query(
                "SELECT draft, gen_random_uuid() FROM unnest($1::uuid[]) AS drafts(draft)",
                &[&drafts],
            )
            .await?
            .into_iter()
            .map(|row| (row.get(0), row.get(1)))
            .collect();
        let proposed: HashSet<_> = assigned.values().copied().collect();
        ensure!(
            proposed.len() == chunks.len(),
            "duplicate PostgreSQL chunk identity"
        );
        let g = &self.graph_name;
        // Validate against existing chunk identities before deleting anything.
        for row in tx.query(&format!("SELECT id::text FROM ag_catalog.cypher('{g}', $$ MATCH (c:DocumentChunk) RETURN c.id $$) AS (id ag_catalog.agtype)"), &[]).await? {
            let id = Uuid::parse_str(row.get(0))?;
            ensure!(!proposed.contains(&id), "generated chunk identity is already occupied");
        }
        let affected = self
            .detach_document_chunks_on(tx.client(), &old, true)
            .await?;
        self.delete_chunk_embeddings_on(tx.client(), &old).await?;
        let mut published = Vec::with_capacity(chunks.len());
        for (chunk, vector) in chunks.iter().zip(vectors) {
            let mut chunk = chunk.clone();
            chunk.id = assigned[&chunk.id];
            chunk.parent_id = chunk
                .parent_id
                .map(|parent| {
                    assigned
                        .get(&parent)
                        .copied()
                        .context("document parent must belong to the replacement")
                })
                .transpose()?;
            self.insert_document_chunk_on(tx.client(), &chunk).await?;
            self.insert_chunk_embedding_on(tx.client(), chunk.id, vector)
                .await?;
            published.push(chunk);
        }
        self.recompute_learning(&tx, None, affected).await?;
        tx.commit().await?;
        Ok(published)
    }

    pub async fn clear_document(&self, path: &str) -> Result<usize> {
        let mut client = self.client.lock().await;
        let tx = learning_transaction(&mut client).await?;
        tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
            .await?;
        let old = self
            .get_chunk_ids_for_document_on(tx.client(), path)
            .await?;
        let affected = self
            .detach_document_chunks_on(tx.client(), &old, true)
            .await?;
        self.delete_chunk_embeddings_on(tx.client(), &old).await?;
        self.recompute_learning(&tx, None, affected).await?;
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
        ensure!(!first.is_empty(), "document embeddings must be nonempty");
        ensure!(
            vectors.iter().all(|v| v.len() == first.len()),
            "inconsistent document embedding dimensions"
        );
        ensure!(
            vectors.iter().flatten().all(|value| value.is_finite()),
            "document embeddings must contain only finite numbers"
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(dead_code)] // Test-only adapter for the shared integration guard.
    mod isolation {
        use crate as mimir_core;
        include!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/support/isolation.rs"
        ));
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
        for vector in [vec![], vec![f32::INFINITY], vec![f32::NAN]] {
            assert!(
                validate_document_batch("document", std::slice::from_ref(&chunk), &[vector])
                    .is_err()
            );
        }
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

    #[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
    #[tokio::test]
    async fn document_search_ranks_visible_indexed_passages_before_limiting() {
        struct Provider(Vec<Vec<f32>>);
        impl crate::embed::EmbeddingProvider for Provider {
            fn embed<'a>(&'a self, _texts: &'a [String]) -> crate::embed::EmbedFuture<'a> {
                Box::pin(async move { Ok(self.0.clone()) })
            }
        }
        let fixture = isolation::fixture();
        let mut service = crate::MimirService::connect(&crate::config::Config {
            database: fixture.database_config(),
            embeddings: None,
            llm: None,
            judge: None,
            email: None,
            retirement: None,
        })
        .await
        .unwrap();
        service.embeddings = Some(Box::new(Provider(vec![vec![1.0, 0.0]])));
        let project = format!("document-search-{}", Uuid::new_v4());
        let path = format!("/fixture/{project}.md");
        let store = &service.store;
        let mut root = DocumentChunk::new(
            path.clone(),
            vec![],
            "parent passage".into(),
            None,
            Some(project.clone()),
        );
        let child = DocumentChunk::new(
            path.clone(),
            vec!["Child".into()],
            "closest scoped passage".into(),
            Some(root.id),
            Some(project.clone()),
        );
        let zero = DocumentChunk::new(
            path.clone(),
            vec![],
            "unrankable passage".into(),
            None,
            Some(project.clone()),
        );
        let published = store
            .replace_document(
                &path,
                &[root.clone(), child, zero],
                &[vec![0.0, 1.0], vec![1.0, 0.0], vec![0.0, 0.0]],
            )
            .await
            .unwrap();
        root.project = None;
        root.document_path = format!("{path}-global");
        let global = store
            .replace_document(
                &root.document_path,
                std::slice::from_ref(&root),
                &[vec![1.0, 0.0]],
            )
            .await
            .unwrap();
        let foreign = DocumentChunk::new(
            format!("{path}-foreign"),
            vec![],
            "foreign".into(),
            None,
            Some("foreign".into()),
        );
        let foreign = store
            .replace_document(
                &foreign.document_path,
                std::slice::from_ref(&foreign),
                &[vec![-1.0, 0.0]],
            )
            .await
            .unwrap();
        let orphan = {
            let client = store.client.lock().await;
            client
                .query_one("SELECT gen_random_uuid()", &[])
                .await
                .unwrap()
                .get::<_, Uuid>(0)
        };
        store
            .insert_chunk_embedding(orphan, &[1.0, 0.0])
            .await
            .unwrap();

        let scoped = service
            .query_document("retention", Some(&project), None)
            .await
            .unwrap();
        assert_eq!(
            scoped.iter().map(|hit| hit.id.as_str()).collect::<Vec<_>>(),
            [published[1].id.to_string(), published[0].id.to_string()]
        );
        assert_eq!(scoped[0].parent_content.as_deref(), Some("parent passage"));
        let limited = service
            .query_document("retention", Some(&project), Some(1))
            .await
            .unwrap();
        assert_eq!(limited.len(), 1);
        assert_eq!(limited[0].id, scoped[0].id);
        let unscoped = service
            .query_document("retention", None, None)
            .await
            .unwrap();
        for hidden in [orphan, published[2].id] {
            assert!(!unscoped.iter().any(|hit| hit.id == hidden.to_string()));
        }
        for visible in [global[0].id, foreign[0].id] {
            assert!(unscoped.iter().any(|hit| hit.id == visible.to_string()));
        }
        assert!(service
            .query_document("retention", Some("absent project"), None)
            .await
            .unwrap()
            .is_empty());

        for response in [
            vec![],
            vec![vec![0.0, 0.0]],
            vec![vec![f32::NAN]],
            vec![vec![1.0], vec![2.0]],
        ] {
            service.embeddings = Some(Box::new(Provider(response)));
            let error = service
                .query_document("retention", Some(&project), None)
                .await
                .unwrap_err();
            assert!(error
                .to_string()
                .contains("must return one finite, nonzero vector"));
        }
    }

    #[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
    #[tokio::test]
    async fn document_reload_rolls_back_late_failure_and_never_adds_evidence() {
        struct FixtureEmbedder;
        impl crate::embed::EmbeddingProvider for FixtureEmbedder {
            fn embed<'a>(&'a self, texts: &'a [String]) -> crate::embed::EmbedFuture<'a> {
                Box::pin(async move { Ok(vec![vec![1.0, 0.0]; texts.len()]) })
            }
        }

        let fixture = isolation::fixture();
        let mut service = crate::MimirService::connect(&crate::config::Config {
            database: fixture.database_config(),
            embeddings: None,
            llm: None,
            judge: None,
            email: None,
            retirement: None,
        })
        .await
        .unwrap();
        let project = format!("document-reload-{}", Uuid::new_v4());
        let path = fixture.root.join(format!("{project}.md"));
        let path = path.to_str().unwrap();
        std::fs::write(path, "# Retention\nKeep backups for 30 days.\n").unwrap();
        let belief = service
            .add_belief_in_project(
                "Keep backups for 30 days.",
                0.5,
                0.0,
                &project,
                MemoryType::Fact,
            )
            .await
            .unwrap();
        service
            .store
            .insert_belief_embedding(belief.id, &[1.0, 0.0])
            .await
            .unwrap();
        service.embeddings = Some(Box::new(FixtureEmbedder));
        assert_eq!(
            service.load_document(path, Some(&project)).await.unwrap(),
            1
        );

        let store = &service.store;
        let old = store.get_chunk_ids_for_document(path).await.unwrap()[0];
        let sources = || async { store.get_evidence_for_beliefs(&[belief.id]).await.unwrap() };
        let probability = || async {
            store
                .get_belief(belief.id)
                .await
                .unwrap()
                .unwrap()
                .probability
        };
        let has_vector = |id: Uuid| async move {
            let client = store.client.lock().await;
            client
                .query_one(
                    "SELECT EXISTS (SELECT 1 FROM chunk_embeddings WHERE chunk_id=$1)",
                    &[&id],
                )
                .await
                .unwrap()
                .get::<_, bool>(0)
        };
        assert!(
            sources().await.is_empty(),
            "identical vectors must not create evidence"
        );
        store
            .insert_evidence(old, belief.id, Probability::new(1.0).unwrap())
            .await
            .unwrap();
        let grounded = probability().await;
        assert!(grounded.value() > belief.probability.value());

        std::fs::write(path, "# Retention revised\nKeep backups for 60 days.\n").unwrap();
        {
            let client = store.client.lock().await;
            client.batch_execute("CREATE FUNCTION mimir_test_reject_chunk_vector() RETURNS trigger LANGUAGE plpgsql AS $$ BEGIN RAISE EXCEPTION 'fixture chunk vector rejected'; END $$; CREATE TRIGGER mimir_test_reject_chunk_vector BEFORE INSERT ON chunk_embeddings FOR EACH STATEMENT EXECUTE FUNCTION mimir_test_reject_chunk_vector()").await.unwrap();
        }
        let failed = service
            .load_document(path, Some(&project))
            .await
            .unwrap_err();
        {
            let client = store.client.lock().await;
            client.batch_execute("DROP TRIGGER mimir_test_reject_chunk_vector ON chunk_embeddings; DROP FUNCTION mimir_test_reject_chunk_vector()").await.unwrap();
        }
        assert!(failed.chain().any(|cause| cause
            .downcast_ref::<tokio_postgres::Error>()
            .and_then(tokio_postgres::Error::as_db_error)
            .is_some_and(|detail| detail.message() == "fixture chunk vector rejected")));
        assert_eq!(
            store.get_chunk_ids_for_document(path).await.unwrap(),
            vec![old]
        );
        assert!(has_vector(old).await);
        assert_eq!(sources().await, vec![(belief.id, old, 1.0)]);
        assert_eq!(probability().await, grounded);

        assert_eq!(
            service.load_document(path, Some(&project)).await.unwrap(),
            1
        );
        let replacement = store.get_chunk_ids_for_document(path).await.unwrap()[0];
        assert_ne!(replacement, old);
        assert!(has_vector(replacement).await);
        assert!(!has_vector(old).await);
        assert!(sources().await.is_empty());
        assert_eq!(probability().await, belief.probability);

        store
            .insert_evidence(replacement, belief.id, Probability::new(1.0).unwrap())
            .await
            .unwrap();
        assert_eq!(service.clear_document(path).await.unwrap(), 1);
        assert!(!has_vector(replacement).await);
        assert_eq!(probability().await, belief.probability);

        let drafts = crate::documents::parse_markdown(
            "# Policy\nParent text.\n\n## Detail\nChild text.\n",
            path,
            Some(&project),
        );
        assert_eq!(drafts.len(), 2);
        let published = store
            .replace_document(path, &drafts, &[vec![1.0, 0.0], vec![0.0, 1.0]])
            .await
            .unwrap();
        for (draft, stored) in drafts.iter().zip(&published) {
            assert_ne!(stored.id, draft.id);
            assert!(has_vector(stored.id).await);
            assert!(!has_vector(draft.id).await);
        }
        let child = store
            .get_chunk_by_id(published[1].id)
            .await
            .unwrap()
            .unwrap();
        assert_eq!(child.parent_id, Some(published[0].id));
        assert_eq!(service.clear_document(path).await.unwrap(), 2);
    }

    #[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
    #[tokio::test]
    async fn belief_preparation_and_publication_failures_leave_no_partial_belief() {
        struct Provider {
            fail: bool,
        }
        impl crate::embed::EmbeddingProvider for Provider {
            fn embed<'a>(&'a self, texts: &'a [String]) -> crate::embed::EmbedFuture<'a> {
                Box::pin(async move {
                    if self.fail {
                        anyhow::bail!("fixture embedding failed");
                    }
                    Ok(vec![vec![1.0, 0.0]; texts.len()])
                })
            }
        }
        let cfg = isolation::fixture().database_config();
        let mut service = crate::MimirService::connect(&crate::config::Config {
            database: cfg,
            embeddings: None,
            llm: None,
            judge: None,
            email: None,
            retirement: None,
        })
        .await
        .unwrap();
        let project = format!("prepared-belief-{}", Uuid::new_v4());
        let path = format!("/fixture/{project}.md");
        let source = DocumentChunk::new(
            path.clone(),
            vec![],
            "Backups are kept for 30 days.".into(),
            None,
            Some(project.clone()),
        );
        let source = service
            .store
            .replace_document(&path, std::slice::from_ref(&source), &[vec![1.0, 0.0]])
            .await
            .unwrap()
            .remove(0);
        let draft = || {
            Belief::new_in_project(
                "Backups are kept for 30 days.".into(),
                0.6,
                0.3,
                project.clone(),
            )
            .unwrap()
        };

        service.embeddings = Some(Box::new(Provider { fail: true }));
        assert!(service
            .publish_supported_belief(draft(), None, source.id)
            .await
            .is_err());
        assert!(!service
            .store
            .list_beliefs()
            .await
            .unwrap()
            .iter()
            .any(|belief| belief.project.as_deref() == Some(project.as_str())));

        service.embeddings = Some(Box::new(Provider { fail: false }));
        {
            let client = service.store.client.lock().await;
            client.batch_execute("CREATE FUNCTION mimir_test_reject_belief_vector() RETURNS trigger LANGUAGE plpgsql AS $$ BEGIN RAISE EXCEPTION 'fixture vector publication rejected'; END $$; CREATE TRIGGER mimir_test_reject_belief_vector BEFORE INSERT ON belief_embeddings FOR EACH STATEMENT EXECUTE FUNCTION mimir_test_reject_belief_vector()").await.unwrap();
        }
        let failed = service
            .publish_supported_belief(draft(), None, source.id)
            .await;
        {
            let client = service.store.client.lock().await;
            client.batch_execute("DROP TRIGGER mimir_test_reject_belief_vector ON belief_embeddings; DROP FUNCTION mimir_test_reject_belief_vector()").await.unwrap();
        }
        assert!(failed.is_err());
        assert!(!service
            .store
            .list_beliefs()
            .await
            .unwrap()
            .iter()
            .any(|belief| belief.project.as_deref() == Some(project.as_str())));

        let published = service
            .publish_supported_belief(draft(), None, source.id)
            .await
            .unwrap();
        let stored = service
            .store
            .get_belief(published.id)
            .await
            .unwrap()
            .unwrap();
        assert_eq!(stored.probability.value(), 0.6);
        assert_eq!(stored.confidence.value(), 0.3);
        assert_eq!(
            service
                .store
                .get_evidence_for_beliefs(&[published.id])
                .await
                .unwrap(),
            vec![(published.id, source.id, 0.0)]
        );
        let client = service.store.client.lock().await;
        let vectors: i64 = client
            .query_one(
                "SELECT count(*) FROM belief_embeddings WHERE belief_id=$1",
                &[&published.id],
            )
            .await
            .unwrap()
            .get(0);
        assert_eq!(vectors, 1);
        drop(client);
        // Review-created beliefs obey the same prepare-then-publish rule.
        let experience: crate::learning::Experience = serde_json::from_value(serde_json::json!({
            "id":Uuid::new_v4(), "project":project, "context":"backup retention",
            "action":"check retention documentation", "outcome":"success", "source":"tool_result",
            "evidence":["document read"], "pattern_id":null
        }))
        .unwrap();
        let experience = service
            .create_experience(&experience.clone().with_identity(()))
            .await
            .unwrap()
            .experience;
        let mut review: crate::learning::Review = serde_json::from_value(serde_json::json!({
            "experience_id":experience.id, "experience_revision":1, "reviewer":"fixture",
            "rationale":"document confirms retention", "candidates":[{
                "kind":"belief", "key":"retention", "content":"Backups are kept for 30 days.",
                "supporting_passage_id":source.id
            }]
        }))
        .unwrap();
        service.embeddings = Some(Box::new(Provider { fail: true }));
        let mut stale = review.clone();
        stale.experience_revision += 1;
        assert_eq!(
            service
                .review_supported_experience(&stale, 0)
                .await
                .unwrap_err()
                .to_string(),
            "stale review: experience has changed"
        );
        assert_eq!(
            service
                .review_supported_experience(&review, 1)
                .await
                .unwrap_err()
                .to_string(),
            "stale review revision: current is 0"
        );
        assert!(format!(
            "{:#}",
            service
                .review_supported_experience(&review, 0)
                .await
                .unwrap_err()
        )
        .contains("fixture embedding failed"));
        assert!(service
            .store
            .existing_belief_candidates(experience.id)
            .await
            .unwrap()
            .is_empty());
        assert_eq!(
            service
                .get_experience(experience.id)
                .await
                .unwrap()
                .unwrap()
                .review_revision,
            0
        );
        service.embeddings = Some(Box::new(Provider { fail: false }));
        if let crate::learning::Candidate::Belief {
            supporting_passage_id,
            ..
        } = &mut review.candidates[0]
        {
            *supporting_passage_id = None;
        }
        assert!(service
            .review_supported_experience(&review, 0)
            .await
            .is_err());
        if let crate::learning::Candidate::Belief {
            supporting_passage_id,
            ..
        } = &mut review.candidates[0]
        {
            *supporting_passage_id = Some(source.id);
        }
        let applied = service
            .review_supported_experience(&review, 0)
            .await
            .unwrap();
        let candidate_id = applied.candidate_ids["retention"];
        assert_eq!(
            service
                .store
                .get_evidence_for_beliefs(&[candidate_id])
                .await
                .unwrap(),
            vec![(candidate_id, source.id, 0.0)]
        );
        // A completed retry uses the existing belief without invoking a provider.
        service.embeddings = Some(Box::new(Provider { fail: true }));
        let retried = service
            .review_supported_experience(&review, 0)
            .await
            .unwrap();
        assert_eq!(retried.candidate_ids, applied.candidate_ids);
        service.delete_project(&project).await.unwrap();
    }

    #[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
    #[tokio::test]
    async fn grounding_edits_only_recalculate_changed_evidence_and_rollback_on_error() {
        let cfg = isolation::fixture().database_config();
        crate::db::migrate(&cfg).await.unwrap();
        let store =
            AgeStore::new(crate::db::connect(&cfg).await.unwrap(), cfg.dbname.clone()).unwrap();
        let project = format!("grounding-{}", Uuid::new_v4());
        let target =
            Belief::new_in_project("grounding target".into(), 0.5, 0.0, project.clone()).unwrap();
        let dependent =
            Belief::new_in_project("grounding dependent".into(), 0.5, 0.0, project.clone())
                .unwrap();
        let passage = DocumentChunk::new(
            format!("/fixture/{project}.md"),
            vec![],
            "An observed receipt.".into(),
            None,
            Some(project),
        );
        let target = store.insert_belief(&target).await.unwrap();
        let dependent = store.insert_belief(&dependent).await.unwrap();
        let passage = store.insert_document_chunk(&passage).await.unwrap();
        let links = || async { store.get_evidence_for_beliefs(&[target.id]).await.unwrap() };
        let target_value = || async {
            store
                .get_belief(target.id)
                .await
                .unwrap()
                .unwrap()
                .probability
        };
        let dependent_value = || async {
            store
                .get_belief(dependent.id)
                .await
                .unwrap()
                .unwrap()
                .probability
        };
        let add = |weight| {
            store.insert_evidence(passage.id, target.id, Probability::new(weight).unwrap())
        };
        let remove = || store.delete_evidence(passage.id, target.id);

        // A posterior different from the fixed prior makes needless recalculation visible.
        store.update_belief_beta(target.id, 9.0, 1.0).await.unwrap();
        let before = target_value().await;
        assert_ne!(before, target.probability);
        add(0.0).await.unwrap();
        assert_eq!(links().await, vec![(target.id, passage.id, 0.0)]);
        assert_eq!(target_value().await, before);
        remove().await.unwrap();
        remove().await.unwrap();
        assert!(links().await.is_empty());
        assert_eq!(target_value().await, before);

        store
            .update_belief_beta(target.id, target.alpha0, target.beta0)
            .await
            .unwrap();
        store
            .insert_edge_and_propagate(
                &Edge::new(target.id, dependent.id, EdgeType::Supports, 1.0).unwrap(),
            )
            .await
            .unwrap();
        let dependent_before = dependent_value().await;
        add(0.5).await.unwrap();
        add(0.5).await.unwrap();
        let weighted = links().await;
        assert_eq!(weighted, vec![(target.id, passage.id, 0.5); 2]);
        let with_evidence = target_value().await;
        let dependent_with_evidence = dependent_value().await;
        assert!(with_evidence.value() > target.probability.value());
        assert!(dependent_with_evidence.value() > dependent_before.value());

        // Inject an invalid stored weight so recalculation rejects the edit.
        let graph = &store.graph_name;
        let target_id = target.id;
        let dependent_id = dependent.id;
        let bad_link =
            format!("MATCH (a:Belief {{id:'{dependent_id}'}}), (b:Belief {{id:'{target_id}'}})");
        let edit_bad_link = |edit: &str| {
            let sql = format!("SELECT * FROM ag_catalog.cypher('{graph}', $$ {bad_link} {edit} RETURN 1 $$) AS (ok ag_catalog.agtype)");
            let store = &store;
            async move { store.client.lock().await.query(&sql, &[]).await.unwrap() }
        };
        edit_bad_link("CREATE (a)-[:SUPPORTS {weight:2.0}]->(b)").await;
        for error in [add(0.5).await.unwrap_err(), remove().await.unwrap_err()] {
            assert_eq!(error.to_string(), "probability 2 is outside [0, 1]");
            assert_eq!(links().await, weighted);
            assert_eq!(target_value().await, with_evidence);
            assert_eq!(dependent_value().await, dependent_with_evidence);
        }
        edit_bad_link("MATCH (a)-[r:SUPPORTS]->(b) DELETE r").await;
        remove().await.unwrap();
        assert!(links().await.is_empty());
        assert_eq!(target_value().await, target.probability);
        assert_eq!(dependent_value().await, dependent_before);
    }

    #[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
    #[tokio::test]
    async fn project_deletion_rolls_back_before_a_fresh_retry() {
        let cfg = isolation::fixture().database_config();
        crate::db::migrate(&cfg).await.unwrap();
        let store =
            AgeStore::new(crate::db::connect(&cfg).await.unwrap(), cfg.dbname.clone()).unwrap();
        let project = format!("deletion-rollback-{}", Uuid::new_v4());
        let belief = Belief::new_in_project(
            "deletion rollback fixture".into(),
            0.5,
            0.0,
            project.clone(),
        )
        .unwrap();
        let belief = store.insert_belief(&belief).await.unwrap();
        store
            .insert_belief_embedding(belief.id, &[1.0, 0.0])
            .await
            .unwrap();
        let survivor = Belief::new_in_project(
            "surviving belief grounded in the deleted project".into(),
            0.5,
            0.0,
            format!("{project}-survivor"),
        )
        .unwrap();
        let survivor = store.insert_belief(&survivor).await.unwrap();
        let linked = Belief::new_in_project(
            "surviving belief supported by a deleted belief".into(),
            0.5,
            0.0,
            format!("{project}-survivor"),
        )
        .unwrap();
        let linked = store.insert_belief(&linked).await.unwrap();
        let unrelated = Belief::new_in_project(
            "unrelated surviving belief".into(),
            0.8,
            0.0,
            format!("{project}-survivor"),
        )
        .unwrap();
        let unrelated = store.insert_belief(&unrelated).await.unwrap();
        let edge = Edge::new(belief.id, linked.id, EdgeType::Supports, 1.0).unwrap();
        store.insert_edge_and_propagate(&edge).await.unwrap();
        let with_support = store.get_belief(linked.id).await.unwrap().unwrap();
        assert!(with_support.probability.value() > linked.probability.value());
        let path = format!("/fixture/{project}.md");
        let passage = DocumentChunk::new(
            path.clone(),
            vec![],
            "This passage supports the surviving belief.".into(),
            None,
            Some(project.clone()),
        );
        let passage = store
            .replace_document(&path, std::slice::from_ref(&passage), &[vec![1.0, 0.0]])
            .await
            .unwrap()
            .remove(0);
        store
            .insert_evidence(passage.id, survivor.id, Probability::new(1.0).unwrap())
            .await
            .unwrap();
        let with_evidence = store.get_belief(survivor.id).await.unwrap().unwrap();
        assert!(with_evidence.probability.value() > survivor.probability.value());
        let experience = crate::learning::NewExperience {
            id: (),
            project: project.clone(),
            context: "deletion rollback".into(),
            action: "verify evidence".into(),
            outcome: crate::learning::Outcome::Unknown,
            source: crate::learning::ObservationSource::AgentReport,
            evidence: vec!["isolated fixture".into()],
            belief_ids: vec![],
            pattern_id: None,
            learning_items: vec![],
            source_records: vec![],
        };
        store.create_experience(&experience).await.unwrap();
        let vectors_exist = || async {
            let client = store.client.lock().await;
            let row = client
                .query_one(
                    "SELECT EXISTS (SELECT 1 FROM belief_embeddings WHERE belief_id = $1), \
                 EXISTS (SELECT 1 FROM chunk_embeddings WHERE chunk_id = $2)",
                    &[&belief.id, &passage.id],
                )
                .await
                .unwrap();
            (row.get::<_, bool>(0), row.get::<_, bool>(1))
        };
        // Reject the commit after both deletion and recalculation ran.
        {
            let client = store.client.lock().await;
            client.batch_execute("CREATE FUNCTION mimir_test_reject_delete() RETURNS trigger LANGUAGE plpgsql AS $$ BEGIN RAISE EXCEPTION 'fixture deletion rejected'; END $$; CREATE CONSTRAINT TRIGGER mimir_test_reject_delete AFTER DELETE ON mimir_experiences DEFERRABLE INITIALLY DEFERRED FOR EACH ROW EXECUTE FUNCTION mimir_test_reject_delete()").await.unwrap();
        }
        let failed = store.delete_project_complete(&project).await;
        {
            let client = store.client.lock().await;
            client.batch_execute("DROP TRIGGER mimir_test_reject_delete ON mimir_experiences; DROP FUNCTION mimir_test_reject_delete()").await.unwrap();
        }
        let error = failed.unwrap_err();
        assert!(error.chain().any(|cause| cause
            .downcast_ref::<tokio_postgres::Error>()
            .and_then(tokio_postgres::Error::as_db_error)
            .is_some_and(|detail| detail.message() == "fixture deletion rejected")));
        assert!(store.get_belief(belief.id).await.unwrap().is_some());
        assert!(store.get_chunk_by_id(passage.id).await.unwrap().is_some());
        assert_eq!(vectors_exist().await, (true, true));
        assert_eq!(
            store
                .get_belief(survivor.id)
                .await
                .unwrap()
                .unwrap()
                .probability,
            with_evidence.probability
        );
        assert_eq!(
            store
                .get_belief(linked.id)
                .await
                .unwrap()
                .unwrap()
                .probability,
            with_support.probability
        );
        assert_eq!(
            store.delete_project_complete(&project).await.unwrap(),
            (1, 1)
        );
        assert!(store.get_belief(belief.id).await.unwrap().is_none());
        assert!(store.get_chunk_by_id(passage.id).await.unwrap().is_none());
        assert_eq!(vectors_exist().await, (false, false));
        assert_eq!(
            store
                .get_belief(survivor.id)
                .await
                .unwrap()
                .unwrap()
                .probability,
            survivor.probability
        );
        assert_eq!(
            store
                .get_belief(linked.id)
                .await
                .unwrap()
                .unwrap()
                .probability,
            linked.probability
        );
        assert_eq!(
            store
                .get_belief(unrelated.id)
                .await
                .unwrap()
                .unwrap()
                .probability,
            unrelated.probability
        );
        assert_eq!(
            store.delete_project_complete(&project).await.unwrap(),
            (0, 0)
        );
    }

    #[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
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
        let live = store.insert_belief(&live).await.unwrap();
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
