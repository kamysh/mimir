//! A direct graph change and its original answer commit together.
use super::{AgeStore, OperationBindingRequest, RegisteredStep, StepDecision};
use crate::{
    graph::{Edge, EdgeType, Probability},
    interaction::RequestCorrection,
    operation_catalogue::CommitSite,
    validation::Code,
};
use anyhow::Result;
use serde::de::DeserializeOwned;
use uuid::Uuid;

fn decode<T: DeserializeOwned>(request: &OperationBindingRequest, schema: &str) -> Result<T> {
    if !request
        .settings()
        .as_object()
        .is_some_and(|settings| settings.is_empty())
    {
        return Err(RequestCorrection::bound_graph_request(
            "settings",
            Code::UnknownField,
            "Direct graph writes have no per-request settings; no graph change was made.".into(),
            "An empty settings object for the original direct graph request.",
        )
        .into());
    }
    serde_json::from_value(request.arguments().clone()).map_err(|error| {
        RequestCorrection::bound_graph_request(
            "",
            Code::MalformedInput,
            format!("Invalid original graph request: {error}. No graph change was made."),
            schema,
        )
        .into()
    })
}
fn probability(value: f64, field: &str) -> Result<Probability> {
    Probability::new(value).map_err(|error| {
        RequestCorrection::bound_graph_request(
            field,
            Code::InvalidNumber,
            format!("{error}. No graph change was made."),
            "A finite number between 0 and 1 inclusive; do not clamp or guess a replacement.",
        )
        .into()
    })
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct PatternArguments {
    situation: String,
    approach: String,
    success_rate: f64,
    #[serde(default, deserialize_with = "optional_project")]
    project: Option<String>,
}
// A missing project is allowed; explicit null has never been a string project.
fn optional_project<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> std::result::Result<Option<String>, D::Error> {
    <String as serde::Deserialize>::deserialize(deserializer).map(Some)
}
fn pattern(request: &OperationBindingRequest) -> Result<(PatternArguments, Probability)> {
    if request.operation() != "insert_pattern" {
        return Err(RequestCorrection::bound_graph_request(
            "operation_token",
            Code::WrongIdentity,
            "This token does not name an insert_pattern request; no pattern was changed.".into(),
            "The original token bound to the intended insert_pattern request.",
        )
        .into());
    }
    let args: PatternArguments = decode(request, "Exactly situation and approach strings, a success_rate in [0,1], and optionally a project string.")?;
    let success = probability(args.success_rate, "success_rate")?;
    Ok((args, success))
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct DirectedArguments {
    from_id: Uuid,
    to_id: Uuid,
    weight: f64,
}
#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct ContradictionArguments {
    id_a: Uuid,
    id_b: Uuid,
    #[serde(default = "one")]
    weight: f64,
}
fn one() -> f64 {
    1.0
}
fn edge(request: &OperationBindingRequest) -> Result<Edge> {
    let (from, to, kind, weight) = match request.operation() {
        "record_support" | "record_cause" => {
            let args: DirectedArguments = decode(request, "Exactly from_id and to_id stored UUIDs and a finite weight in [0,1].")?;
            (args.from_id, args.to_id, if request.operation() == "record_support" { EdgeType::Supports } else { EdgeType::Causes }, args.weight)
        }
        "record_contradiction" => {
            let args: ContradictionArguments = decode(request, "Exactly id_a and id_b stored UUIDs, and optionally a finite weight in [0,1].")?;
            (args.id_a, args.id_b, EdgeType::Contradicts, args.weight)
        }
        _ => return Err(RequestCorrection::bound_graph_request("operation_token", Code::WrongIdentity,
            "This token does not name a support, cause or contradiction request; no relationship was changed.".into(),
            "The original token bound to the intended direct relationship request.").into()),
    };
    let weight = probability(weight, "weight")?;
    Ok(Edge {
        from_id: from,
        to_id: to,
        edge_type: kind,
        weight,
    })
}

impl AgeStore {
    pub async fn create_pattern_operation(&self, step: &RegisteredStep) -> Result<StepDecision> {
        pattern(step.expected())?;
        if step.description().site != CommitSite::PatternPublication.name() {
            return Err(RequestCorrection::bound_graph_request(
                "plan",
                Code::WrongIdentity,
                "This step is not the registered pattern publication; no pattern was changed."
                    .into(),
                "The original insert_pattern plan's store.insert_pattern step.",
            )
            .into());
        }
        let owner = AgeStore {
            client: self.client.clone(),
            graph_name: self.graph_name.clone(),
        };
        self.commit_final_operation_step(step, move |tx, binding| {
            Box::pin(async move {
                let (args, success) = pattern(binding)?;
                tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
                    .await?;
                let created = owner
                    .create_pattern_on(
                        tx.client(),
                        &args.situation,
                        &args.approach,
                        success,
                        args.project.as_deref(),
                    )
                    .await?;
                let reply = serde_json::to_value(created)?;
                Ok((reply.clone(), reply))
            })
        })
        .await
    }

    pub async fn direct_relationship_operation(
        &self,
        step: &RegisteredStep,
    ) -> Result<StepDecision> {
        let original = edge(step.expected())?;
        let site = if original.edge_type == EdgeType::Contradicts {
            CommitSite::ContradictionPublication
        } else {
            CommitSite::EdgePublication
        };
        if step.description().site != site.name() {
            return Err(RequestCorrection::bound_graph_request("plan", Code::WrongIdentity,
                "This step is not the registered direct relationship publication; no relationship was changed.".into(),
                "The original request's registered store.insert_edge or store.insert_contradicts step.").into());
        }
        let owner = AgeStore {
            client: self.client.clone(),
            graph_name: self.graph_name.clone(),
        };
        self.commit_final_operation_step(step, move |tx, binding| {
            Box::pin(async move {
                let original = edge(binding)?;
                tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
                    .await?;
                if original.edge_type == EdgeType::Contradicts {
                    owner
                        .insert_contradicts_on(
                            tx.client(),
                            original.from_id,
                            original.to_id,
                            original.weight,
                        )
                        .await?;
                } else {
                    owner.insert_edge_on(tx.client(), &original).await?;
                }
                let reply = serde_json::json!({"ok":true});
                Ok((reply.clone(), reply))
            })
        })
        .await
    }
}
