//! Closed registrations for the existing public tools. Argument admission and
//! operation-journal binding follow separately; Input is the current raw JSON.
use anyhow::{anyhow, ensure, Result};
use mimir_core::MimirService;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

pub type Input = Value;

pub use mimir_core::operation_catalogue::{
    CommitBoundary, ControlOperation, GraphOperation, LearningOperation, Operation,
};

async fn call(operation: Operation, service: &MimirService, input: &Input) -> Result<Value> {
    if let Some(writer) = operation.registered_write() {
        let token = super::operation_protocol::token(input)?;
        let mut arguments = mimir_json::Document::new(mimir_json::clone_value(input));
        arguments
            .as_object_mut()
            .ok_or_else(|| anyhow!("Use the advertised argument object"))?
            .remove("operation_token");
        let result = service
            .execute_registered_write(writer, token, arguments)
            .await?;
        return super::operation_protocol::outcome(token, result);
    }
    match operation {
        Operation::Graph(operation) => super::handle_graph_call(service, operation, input).await,
        Operation::Learning(operation) => super::learning::call(service, operation, input).await,
        Operation::Control(operation) => {
            super::operation_protocol::call(operation, service, input).await
        }
    }
}

pub struct RegisteredOperation {
    handler: Operation,
    descriptor: Value,
}
impl RegisteredOperation {
    pub fn handler(&self) -> Operation {
        self.handler
    }
    pub fn input_schema(&self) -> &Value {
        &self.descriptor["inputSchema"]
    }
    pub fn committed_boundaries(&self) -> &'static [CommitBoundary] {
        self.handler.committed_boundaries()
    }
    pub async fn call(&self, service: &MimirService, input: &Input) -> Result<Value> {
        if let Some(correction) = super::admission::arguments(self.input_schema(), input) {
            return Ok(mimir_json::to_value(correction)?);
        }
        let result = call(self.handler, service, input).await;
        if let Err(error) = &result {
            if let Some(issue) = error.downcast_ref::<mimir_core::WriteAdmissionIssue>() {
                return Ok(mimir_json::to_value(issue.correction())?);
            }
        }
        if self.handler == Operation::Graph(GraphOperation::SweepExpiredDefeated) {
            if let Err(error) = &result {
                if let Some(issue) = error.downcast_ref::<mimir_core::config::RetirementIssue>() {
                    return Ok(mimir_json::to_value(issue.correction())?);
                }
            }
        }
        // Read-only handlers cannot have changed business data. Sweep also
        // acknowledges rollback before exposing a stored-value diagnostic;
        // an unacknowledged rollback deliberately strips that typed cause.
        // Do not apply this conversion to larger or partially committed work.
        if self.committed_boundaries().is_empty()
            || self.handler == Operation::Graph(GraphOperation::SweepExpiredDefeated)
        {
            if let Err(error) = &result {
                if let Some(issue) = error.downcast_ref::<mimir_core::graph::StoredBeliefIssue>() {
                    let correction =
                        mimir_core::interaction::NeedsInput::new(issue.issue().clone(), vec![])?;
                    return Ok(mimir_json::to_value(correction)?);
                }
            }
        }
        if self.handler == Operation::Graph(GraphOperation::RecordDefeat) {
            if let Err(error) = &result {
                if let Some(decision) =
                    error.downcast_ref::<mimir_core::inference::EdgeCommittedDecision>()
                {
                    return Ok(decision.response().clone());
                }
            }
        }
        if matches!(
            self.handler,
            Operation::Graph(
                GraphOperation::PropagateFrom
                    | GraphOperation::QueryIntervention
                    | GraphOperation::InsertBelief
                    | GraphOperation::LoadDocument
                    | GraphOperation::DeleteBelief
                    | GraphOperation::AddEvidence
                    | GraphOperation::SweepExpiredDefeated
            ) | Operation::Learning(
                LearningOperation::RecordExperience | LearningOperation::ReviewExperience
            )
        ) {
            if let Err(error) = &result {
                if let Some(decision) =
                    error.downcast_ref::<mimir_core::inference::NumericalDecision>()
                {
                    let correction =
                        mimir_core::interaction::NeedsInput::new(decision.issue().clone(), vec![])?;
                    return Ok(mimir_json::to_value(correction)?);
                }
            }
        }
        // A refusal from an inner step does not certify a larger operation
        // with earlier commits (for example document loading and grounding).
        if matches!(
            self.handler,
            Operation::Graph(GraphOperation::SweepExpiredDefeated | GraphOperation::RecordDefeat)
                | Operation::Learning(LearningOperation::ReviewExperience)
        ) {
            if let Err(error) = &result {
                if let Some(issue) =
                    error.downcast_ref::<mimir_core::store::RetirementMetadataIssue>()
                {
                    return Ok(serde_json::to_value(issue.correction())?);
                }
            }
        }
        if self.handler == Operation::Graph(GraphOperation::SweepExpiredDefeated) {
            if let Err(error) = &result {
                if let Some(issue) = error.downcast_ref::<mimir_core::store::SweepPolicyIssue>() {
                    return Ok(mimir_json::to_value(issue.correction())?);
                }
            }
        }
        if matches!(
            self.handler,
            Operation::Graph(
                GraphOperation::RecordSupport
                    | GraphOperation::RecordCause
                    | GraphOperation::RecordDefeat
                    | GraphOperation::RecordContradiction
                    | GraphOperation::AddEvidence
                    | GraphOperation::QueryIntervention
                    | GraphOperation::QueryDocument
                    | GraphOperation::PropagateFrom
                    | GraphOperation::SweepExpiredDefeated
            ) | Operation::Learning(
                LearningOperation::RecordExperience
                    | LearningOperation::ReviewExperience
                    | LearningOperation::GetLessonAssessment
                    | LearningOperation::QueryLearningContext
            )
        ) {
            if let Err(error) = &result {
                if let Some(refusal) =
                    error.downcast_ref::<mimir_core::interaction::RequestCorrection>()
                {
                    return Ok(mimir_json::to_value(refusal.correction())?);
                }
            }
        }
        if matches!(
            self.handler,
            Operation::Graph(GraphOperation::InsertBelief | GraphOperation::LoadDocument)
                | Operation::Learning(LearningOperation::ReviewExperience)
        ) {
            if let Err(error) = &result {
                if let Some(decision) =
                    error.downcast_ref::<mimir_core::preparation::PreparationRequired>()
                {
                    return Ok(mimir_json::to_value(decision.correction())?);
                }
            }
        }
        result
    }
}

pub struct Catalogue {
    entries: Vec<RegisteredOperation>,
}
impl Catalogue {
    pub fn new(descriptors: Value) -> Result<Self> {
        let descriptions = descriptors
            .as_array()
            .ok_or_else(|| anyhow!("compiled tool descriptions must be an array"))?;
        let available: BTreeMap<_, _> = Operation::ALL
            .iter()
            .map(|operation| (operation.name(), *operation))
            .collect();
        ensure!(
            available.len() == Operation::ALL.len(),
            "duplicate compiled operation name"
        );
        let mut seen = BTreeSet::new();
        let mut entries = Vec::new();
        for descriptor in descriptions {
            let name = descriptor["name"]
                .as_str()
                .ok_or_else(|| anyhow!("compiled tool description is missing its name"))?;
            ensure!(
                seen.insert(name),
                "duplicate compiled tool description: {name}"
            );
            let handler = available
                .get(name)
                .ok_or_else(|| anyhow!("unregistered compiled tool: {name}"))?;
            ensure!(
                descriptor["inputSchema"].is_object(),
                "compiled tool {name} has no input schema"
            );
            if handler.registered_write().is_some() {
                let schema = &descriptor["inputSchema"];
                ensure!(schema["properties"]["operation_token"]["type"]=="string"
                    && schema["properties"]["operation_token"]["format"]=="uuid"
                    && schema["required"].as_array().is_some_and(|fields|fields.iter().any(|field|field=="operation_token")),
                    "registered writer {name} must advertise its required PostgreSQL operation_token UUID");
            }
            let mut descriptor = descriptor.clone();
            super::admission::close_objects(&mut descriptor["inputSchema"]);
            entries.push(RegisteredOperation {
                handler: *handler,
                descriptor,
            });
        }
        for name in available.keys() {
            ensure!(
                seen.contains(name),
                "registered operation has no advertised input: {name}"
            );
        }
        Ok(Self { entries })
    }
    pub fn entries(&self) -> &[RegisteredOperation] {
        &self.entries
    }
    pub fn advertised(&self) -> Value {
        Value::Array(
            self.entries
                .iter()
                .map(|entry| entry.descriptor.clone())
                .collect(),
        )
    }
    pub fn get(&self, name: &str) -> Option<&RegisteredOperation> {
        self.entries
            .iter()
            .find(|entry| entry.handler.name() == name)
    }
    pub async fn call(&self, service: &MimirService, name: &str, input: &Input) -> Result<Value> {
        match self.get(name) {
            Some(operation) => operation.call(service, input).await,
            None => Ok(mimir_json::to_value(super::admission::unknown_tool(
                name,
                &self
                    .entries
                    .iter()
                    .map(|entry| entry.handler().name().to_owned())
                    .collect::<Vec<_>>(),
            ))?),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn actual_entries_preserve_all_advertised_schemas_and_order() {
        let descriptions = super::super::tools_list();
        let catalogue = Catalogue::new(descriptions.clone()).unwrap();
        assert_eq!(catalogue.advertised(), descriptions);
        assert_eq!(catalogue.entries().len(), Operation::ALL.len());
        for entry in catalogue.entries() {
            assert_eq!(
                entry.input_schema(),
                &descriptions
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|description| description["name"] == entry.handler().name())
                    .unwrap()["inputSchema"]
            );
            let mut sites = BTreeSet::new();
            for boundary in entry.committed_boundaries() {
                assert!(sites.insert(boundary.site.name()));
            }
        }
        assert!(catalogue.get("unregistered_tool").is_none());
    }

    #[test]
    fn missing_duplicate_and_unregistered_descriptions_are_rejected() {
        let original = super::super::tools_list();
        let mut missing = original.clone();
        missing.as_array_mut().unwrap().pop();
        assert!(Catalogue::new(missing).is_err());
        let mut duplicate = original.clone();
        duplicate.as_array_mut().unwrap().push(original[0].clone());
        assert!(Catalogue::new(duplicate).is_err());
        let mut unknown = original.clone();
        unknown
            .as_array_mut()
            .unwrap()
            .push(json!({"name":"unregistered_tool","inputSchema":{}}));
        assert!(Catalogue::new(unknown).is_err());
        let mut bypass = original.clone();
        bypass[0]["inputSchema"]["required"]
            .as_array_mut()
            .unwrap()
            .retain(|field| field != "operation_token");
        assert!(
            Catalogue::new(bypass).is_err(),
            "a registered writer cannot drop mandatory token admission"
        );
        let mut no_input = original;
        no_input[0].as_object_mut().unwrap().remove("inputSchema");
        assert!(Catalogue::new(no_input).is_err());
    }
}
