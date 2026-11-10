//! Pure CLI admission before configuration, connections or business writes.
use super::{Cli, Command, DeleteCmd, EvidenceCmd};
use clap::{
    error::{ContextKind, ContextValue, ErrorKind},
    CommandFactory,
};
use mimir_core::{
    interaction::{CorrectionItem, Location, NeedsInput},
    validation::{Code, Fault, Segment},
};

fn response(mut issues: Vec<CorrectionItem>) -> Option<NeedsInput> {
    if issues.is_empty() {
        return None;
    }
    let rest = issues.split_off(1);
    Some(NeedsInput::new(issues.pop().unwrap(), rest).expect("checked CLI issues"))
}

/// Use only at the boundary of one read-only or atomic request. An inner
/// refusal after earlier committed work cannot certify the whole command.
pub(super) fn reference<T>(result: anyhow::Result<T>) -> anyhow::Result<Option<T>> {
    match result {
        Ok(value) => Ok(Some(value)),
        Err(error) => {
            if let Some(refusal) =
                error.downcast_ref::<mimir_core::interaction::RequestCorrection>()
            {
                println!("{}", mimir_json::to_string(refusal.correction())?);
                Ok(None)
            } else if let Some(decision) =
                error.downcast_ref::<mimir_core::inference::NumericalDecision>()
            {
                let correction =
                    mimir_core::interaction::NeedsInput::new(decision.issue().clone(), vec![])?;
                println!("{}", mimir_json::to_string(&correction)?);
                Ok(None)
            } else {
                Err(error)
            }
        }
    }
}

/// The selected caller is read-only, or owns an acknowledged complete
/// rollback. A larger operation with an earlier commit must not use this.
pub(super) fn stored_evidence<T>(result: anyhow::Result<T>) -> anyhow::Result<Option<T>> {
    match result {
        Ok(value) => Ok(Some(value)),
        Err(error) => {
            if let Some(issue) = error.downcast_ref::<mimir_core::graph::StoredBeliefIssue>() {
                let correction = NeedsInput::new(issue.issue().clone(), vec![])?;
                println!("{}", mimir_json::to_string(&correction)?);
                Ok(None)
            } else {
                Err(error)
            }
        }
    }
}

fn uuid(value: &str, field: &str, issues: &mut Vec<CorrectionItem>) {
    if uuid::Uuid::parse_str(value).is_err() {
        issues.push(CorrectionItem::invalid_uuid(vec![Segment::Key(
            field.into(),
        )]));
    }
}

fn probability(value: f64, field: &str, issues: &mut Vec<CorrectionItem>) {
    if !value.is_finite() || !(0.0..=1.0).contains(&value) {
        issues.push(CorrectionItem::new(Location::Arguments,
            Fault { path: vec![Segment::Key(field.into())], code: Code::InvalidNumber,
                message: "The supplied value must be finite and between 0 and 1 inclusive.".into() },
            "A finite number between 0 and 1 inclusive.".into(),
            "Correct the value using the intended request. If it is unknown, ask the user; do not clamp it or invent a replacement.".into()).expect("numeric correction has complete guidance"));
    }
}

pub(super) fn command(command: &Command) -> Option<NeedsInput> {
    let mut issues = Vec::new();
    match command {
        Command::Delete(DeleteCmd::Belief { id } | DeleteCmd::Pattern { id }) => {
            uuid(id, "id", &mut issues)
        }
        Command::Intervene { id, value } => {
            uuid(id, "id", &mut issues);
            probability(*value, "value", &mut issues);
        }
        Command::Evidence(EvidenceCmd::Add {
            chunk_id,
            belief_id,
            weight,
        }) => {
            uuid(chunk_id, "chunk_id", &mut issues);
            uuid(belief_id, "belief_id", &mut issues);
            probability(*weight, "weight", &mut issues);
        }
        Command::Evidence(EvidenceCmd::List { belief_id }) => {
            uuid(belief_id, "belief_id", &mut issues)
        }
        Command::Decay { factor, .. } => probability(*factor, "factor", &mut issues),
        _ => (),
    }
    response(issues)
}

fn argument_name(command: &clap::Command, rendered: &str) -> Option<String> {
    command
        .get_arguments()
        .find(|arg| arg.to_string() == rendered)
        .map(|arg| arg.get_id().to_string())
        .or_else(|| {
            command
                .get_subcommands()
                .find_map(|subcommand| argument_name(subcommand, rendered))
        })
}

pub(super) fn parser(error: &clap::Error) -> NeedsInput {
    let mut catalogue = Cli::command();
    catalogue.build();
    let fields: Vec<String> = match error.get(ContextKind::InvalidArg) {
        Some(ContextValue::Strings(values)) => values.clone(),
        Some(ContextValue::StyledStrs(values)) => values.iter().map(ToString::to_string).collect(),
        Some(value) => vec![value.to_string()],
        None => vec![],
    };
    let field = fields
        .first()
        .and_then(|raw| argument_name(&catalogue, raw));
    let code = match error.kind() {
        ErrorKind::MissingRequiredArgument | ErrorKind::MissingSubcommand => Code::MissingField,
        ErrorKind::UnknownArgument | ErrorKind::InvalidSubcommand => Code::UnknownField,
        ErrorKind::ArgumentConflict => Code::UnsupportedCombination,
        ErrorKind::InvalidValue | ErrorKind::ValueValidation
            if matches!(
                field.as_deref(),
                Some("limit" | "threshold" | "factor" | "value" | "weight")
            ) =>
        {
            Code::InvalidNumber
        }
        _ => Code::MalformedInput,
    };
    let expected = match field.as_deref() {
        Some("limit") => "A positive integer result count. Omit --limit for all matching records; zero is invalid.".into(),
        Some("threshold" | "factor" | "value" | "weight") => "A finite number between 0 and 1 inclusive.".into(),
        _ => error.get(ContextKind::Usage).map(ToString::to_string).unwrap_or_else(|| "Use a documented Mimir command and its arguments; run mimir --help for the command list.".into()),
    };
    let paths: Vec<Vec<Segment>> = if fields.is_empty() {
        vec![vec![]]
    } else {
        fields
            .iter()
            .map(|raw| {
                argument_name(&catalogue, raw)
                    .map(|name| vec![Segment::Key(name)])
                    .unwrap_or_else(|| {
                        if error.kind() == ErrorKind::UnknownArgument {
                            vec![Segment::Key(raw.clone())]
                        } else {
                            vec![]
                        }
                    })
            })
            .collect()
    };
    response(paths.into_iter().map(|path| CorrectionItem::new(Location::Arguments,
        Fault { path, code, message: error.to_string() }, expected.clone(),
        "Correct the reported command or arguments and rerun it. If a required value is not known, ask the user instead of guessing. Do not substitute zero, an empty value or a placeholder to bypass a required field.".into())
        .expect("parser correction retains its complete diagnostic and guidance")).collect())
        .expect("a parser failure always identifies the request or an argument")
}
