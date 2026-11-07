//! Check advertised field shapes before any registered business handler.
use mimir_core::{
    interaction::{CorrectionItem, Location, NeedsInput},
    validation::{Code, Fault, Segment},
};
use serde_json::{json, Value};

fn issue(
    location: Location,
    path: &[Segment],
    code: Code,
    message: &str,
    expected: String,
) -> CorrectionItem {
    CorrectionItem::new(location, Fault {path: path.to_vec(), code, message: message.into()}, expected,
        "Correct this field using the tool schema and known task context. If the value or intended alternative is unknown, ask the user; do not guess or replace it with a default.".into())
        .expect("compiled admission diagnostics have explanations and corrections")
}
fn report(issues: Vec<CorrectionItem>) -> Option<NeedsInput> {
    let mut items = issues.into_iter();
    items.next().map(|first| {
        NeedsInput::new(first, items.collect()).expect("nonempty described correction")
    })
}
fn is_type(kind: &str, value: &Value) -> bool {
    match kind {
        "object" => value.is_object(),
        "array" => value.is_array(),
        "string" => value.is_string(),
        "number" => value.is_number(),
        "integer" => value.as_i64().is_some() || value.as_u64().is_some(),
        "boolean" => value.is_boolean(),
        "null" => value.is_null(),
        _ => false,
    }
}
fn walk(schema: &Value, value: &Value, path: &mut Vec<Segment>, issues: &mut Vec<CorrectionItem>) {
    if let Some(kind) = schema.get("type") {
        let accepted = kind
            .as_str()
            .map(|kind| is_type(kind, value))
            .unwrap_or_else(|| {
                kind.as_array().is_some_and(|kinds| {
                    kinds
                        .iter()
                        .any(|kind| kind.as_str().is_some_and(|kind| is_type(kind, value)))
                })
            });
        if !accepted {
            issues.push(issue(
                Location::Arguments,
                path,
                Code::WrongType,
                "The supplied value has the wrong JSON type.",
                format!("A value with JSON type {kind}."),
            ));
            return;
        }
    }
    if let Some(constant) = schema.get("const") {
        if constant != value {
            issues.push(issue(
                Location::Arguments,
                path,
                Code::MalformedInput,
                "This field does not identify the declared input alternative.",
                format!("The value {constant}."),
            ));
        }
    }
    if let Some(choices) = schema.get("enum").and_then(Value::as_array) {
        if !choices.contains(value) {
            issues.push(issue(
                Location::Arguments,
                path,
                Code::MalformedInput,
                "The supplied value is not one of the declared choices.",
                format!("One of {}.", json!(choices)),
            ));
        }
    }
    if let Some(fields) = value.as_object() {
        if let Some(required) = schema.get("required").and_then(Value::as_array) {
            for name in required.iter().filter_map(Value::as_str) {
                if !fields.contains_key(name) {
                    path.push(Segment::Key(name.into()));
                    issues.push(issue(
                        Location::Arguments,
                        path,
                        Code::MissingField,
                        "A required field is missing.",
                        schema
                            .get("properties")
                            .and_then(|fields| fields.get(name))
                            .map(|field| {
                                format!("A required field with this advertised schema: {field}.")
                            })
                            .unwrap_or_else(|| {
                                "Supply this required field as described by the tool schema.".into()
                            }),
                    ));
                    path.pop();
                }
            }
        }
        if let Some(properties) = schema.get("properties").and_then(Value::as_object) {
            for (name, child_schema) in properties {
                if let Some(child) = fields.get(name) {
                    path.push(Segment::Key(name.clone()));
                    walk(child_schema, child, path, issues);
                    path.pop();
                }
            }
        }
    }
    if let (Some(items), Some(values)) = (schema.get("items"), value.as_array()) {
        for (index, value) in values.iter().enumerate() {
            path.push(Segment::Index(index));
            walk(items, value, path, issues);
            path.pop();
        }
    }
    if let Some(branches) = schema.get("allOf").and_then(Value::as_array) {
        for branch in branches {
            walk(branch, value, path, issues);
        }
    }
    for (keyword, exclusive) in [("anyOf", false), ("oneOf", true)] {
        if let Some(branches) = schema.get(keyword).and_then(Value::as_array) {
            let results: Vec<_> = branches
                .iter()
                .map(|branch| {
                    let mut errors = Vec::new();
                    walk(branch, value, path, &mut errors);
                    errors
                })
                .collect();
            let accepted = results.iter().filter(|errors| errors.is_empty()).count();
            if accepted == 0 {
                for errors in results {
                    issues.extend(errors);
                }
            } else if exclusive && accepted != 1 {
                issues.push(issue(
                    Location::Arguments,
                    path,
                    Code::MalformedInput,
                    "The input combines mutually exclusive alternatives.",
                    "Choose exactly one of the alternatives in the tool schema.".into(),
                ));
            }
        }
    }
}

pub fn arguments(schema: &Value, value: &Value) -> Option<NeedsInput> {
    let mut issues = Vec::new();
    walk(schema, value, &mut Vec::new(), &mut issues);
    report(issues)
}

pub fn tool_parameters(params: &Value) -> Result<(&str, Value), NeedsInput> {
    let name = params.get("name");
    let mut issues = Vec::new();
    if !name.is_some_and(Value::is_string) {
        issues.push(issue(
            Location::Request,
            &[Segment::Key("params".into()), Segment::Key("name".into())],
            if name.is_none() {
                Code::MissingField
            } else {
                Code::WrongType
            },
            "tools/call requires a string tool name.",
            "The exact name of an advertised tool.".into(),
        ));
    }
    if params
        .get("arguments")
        .is_some_and(|value| !value.is_object())
    {
        issues.push(issue(
            Location::Request,
            &[
                Segment::Key("params".into()),
                Segment::Key("arguments".into()),
            ],
            Code::WrongType,
            "Tool arguments must be an object.",
            "An arguments object, or omission for a tool that needs no fields.".into(),
        ));
    }
    if let Some(correction) = report(issues) {
        return Err(correction);
    }
    Ok((
        name.and_then(Value::as_str).expect("tool name was checked"),
        params
            .get("arguments")
            .cloned()
            .unwrap_or_else(|| json!({})),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn required_and_nested_types_report_every_path_without_defaults() {
        let schema = json!({"type":"object", "required":["project", "review"], "properties":{
            "project":{"type":"string"}, "review":{"type":"object", "required":["items"], "properties":{"items":{"type":"array", "items":{"type":"object", "required":["weight"], "properties":{"weight":{"type":"number"}}}}}},
            "enabled":{"type":"boolean"}, "offset":{"type":"integer"}}});
        let correction = arguments(&schema, &json!({"project":null,"review":{"items":[{}, {"weight":"1"}]},"enabled":0,"offset":1.5})).unwrap();
        assert_eq!(correction.issues().len(), 5);
        let encoded = serde_json::to_value(correction).unwrap().to_string();
        assert!(
            encoded.contains("weight")
                && encoded.contains("missing_field")
                && encoded.contains("wrong_type")
        );
        assert!(arguments(
            &schema,
            &json!({"project":"p","review":{"items":[{"weight":1}]},"enabled":true,"offset":0})
        )
        .is_none());
    }

    #[test]
    fn alternatives_and_nullable_fields_keep_their_declared_meaning() {
        let schema = json!({"type":"object","properties":{"value":{"type":["number","null"]}}, "oneOf":[
            {"required":["key"],"properties":{"key":{"type":"string"}}},
            {"required":["id"],"properties":{"id":{"type":"string"}}}]});
        assert!(arguments(&schema, &json!({"key":"k","value":null})).is_none());
        assert!(arguments(&schema, &json!({"key":false})).is_some());
        assert!(arguments(&schema, &json!({"key":"k","id":"i"})).is_some());
        assert!(arguments(&schema, &json!({})).is_some());
    }

    #[test]
    fn tool_method_fields_are_checked_before_lookup() {
        assert!(tool_parameters(&json!({})).is_err());
        assert!(tool_parameters(&json!({"name":7,"arguments":null})).is_err());
        assert_eq!(
            tool_parameters(&json!({"name":"learning_capabilities"}))
                .unwrap()
                .1,
            json!({})
        );
    }
}
