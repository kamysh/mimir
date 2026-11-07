//! Pure MCP envelope admission, before any registered business handler.
use mimir_core::{
    interaction::{CorrectionItem, Location, NeedsInput},
    validation::{Code, Fault, Segment},
};
use serde_json::{json, Value};

pub struct Request {
    id: Value,
    method: String,
    params: Value,
}
impl Request {
    pub fn id(&self) -> &Value {
        &self.id
    }
    pub fn method(&self) -> &str {
        &self.method
    }
    pub fn params(&self) -> &Value {
        &self.params
    }
}
pub enum Incoming {
    Request(Request),
    Notification {
        method: String,
        diagnostic: Option<NeedsInput>,
    },
    Rejected(Value),
}

fn item(
    path: &[&str],
    code: Code,
    message: String,
    expected: &str,
    correction: &str,
) -> CorrectionItem {
    CorrectionItem::new(
        Location::Request,
        Fault {
            path: path.iter().map(|key| Segment::Key((*key).into())).collect(),
            code,
            message,
        },
        expected.into(),
        correction.into(),
    )
    .expect("fixed envelope diagnostics contain descriptions and a correction")
}
fn report(first: CorrectionItem, rest: Vec<CorrectionItem>) -> NeedsInput {
    NeedsInput::new(first, rest)
        .expect("an envelope diagnostic contains at least one described issue")
}
fn error(id: Value, code: i64, message: &str, data: NeedsInput) -> Value {
    json!({"jsonrpc":"2.0","id":id,"error":{"code":code,"message":message,"data":data}})
}
fn valid_id(value: &Value) -> bool {
    value.is_string() || value.is_number()
}

pub fn parse_error(message: &str) -> Value {
    error(Value::Null, -32700, "Parse error", report(item(&[], Code::MalformedInput,
        format!("The request could not be parsed: {message}"),
        "One complete UTF-8 JSON request object per line.",
        "Repair the JSON syntax or UTF-8 encoding and resend the complete request with its client-chosen ID."), vec![]))
}

pub fn decode(value: Value) -> Incoming {
    let Some(fields) = value.as_object() else {
        return Incoming::Rejected(error(
            Value::Null,
            -32600,
            "Invalid Request",
            report(
                item(
                    &[],
                    Code::WrongType,
                    "The message is not a request object.".into(),
                    "A JSON object containing jsonrpc, method and a client-chosen request ID.",
                    "Send one MCP request object per line; do not send a scalar or batch array.",
                ),
                vec![],
            ),
        ));
    };
    let mut issues = Vec::new();
    let version_ok = fields.get("jsonrpc").and_then(Value::as_str) == Some("2.0");
    if !version_ok {
        issues.push(item(
            &["jsonrpc"],
            if fields.contains_key("jsonrpc") {
                Code::MalformedInput
            } else {
                Code::MissingField
            },
            "The jsonrpc field must be the string \"2.0\".".into(),
            "The string \"2.0\".",
            "Supply jsonrpc as \"2.0\"; this is the JSON-RPC version, not the MCP protocolVersion.",
        ));
    }
    let method = fields.get("method").and_then(Value::as_str);
    if method.is_none() {
        issues.push(item(&["method"], if fields.contains_key("method") {Code::WrongType} else {Code::MissingField},
            "The request needs a string method name.".into(), "A method name such as tools/list or tools/call.",
            "Supply the method as a string. Keep the intended request; do not guess a different operation."));
    }
    let provided_id = fields.get("id");
    if provided_id.is_some_and(|id| !valid_id(id)) {
        issues.push(item(&["id"], Code::WrongType, "The MCP request ID is not a string or number.".into(),
            "A client-chosen string or JSON number; zero is a valid identifier.",
            "Use the calling client's request identifier. Do not use null, a boolean, an array or an object."));
    }
    let invalid_params = fields
        .get("params")
        .is_some_and(|params| !params.is_object());
    if invalid_params {
        issues.push(item(&["params"], Code::WrongType, "MCP named parameters must be an object.".into(),
            "An object, or an omitted params member when the method permits it.",
            "Supply named parameters as an object; do not replace an invalid supplied value with defaults."));
    }
    let notification = provided_id.is_none() && version_ok && method.is_some();
    let mut problems = issues.into_iter();
    if let Some(first) = problems.next() {
        let diagnostic = report(first, problems.collect());
        if notification {
            return Incoming::Notification {
                method: method.unwrap().into(),
                diagnostic: Some(diagnostic),
            };
        }
        let id = provided_id
            .filter(|id| valid_id(id))
            .cloned()
            .unwrap_or(Value::Null);
        let params_only =
            invalid_params && version_ok && method.is_some() && provided_id.is_none_or(valid_id);
        return Incoming::Rejected(error(
            id,
            if params_only { -32602 } else { -32600 },
            if params_only {
                "Invalid params"
            } else {
                "Invalid Request"
            },
            diagnostic,
        ));
    }
    let method = method
        .expect("method was checked before admission")
        .to_owned();
    if notification {
        let diagnostic = matches!(method.as_str(), "initialize" | "tools/list" | "tools/call")
            .then(|| {
                report(
                    item(
                        &["id"],
                        Code::MissingField,
                        "This MCP method requires a request ID; no tool was executed.".into(),
                        "A string or number chosen by the calling client.",
                        "Resend as a request with an ID if execution and a response were intended.",
                    ),
                    vec![],
                )
            });
        return Incoming::Notification { method, diagnostic };
    }
    Incoming::Request(Request {
        id: provided_id.expect("admitted requests have an ID").clone(),
        method,
        params: fields.get("params").cloned().unwrap_or_else(|| json!({})),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn malformed_envelopes_are_not_executable_and_keep_usable_ids() {
        for value in [
            json!(null),
            json!(7),
            json!([]),
            json!({"id":"version","method":"tools/call"}),
            json!({"jsonrpc":"1.0","id":0,"method":"tools/call"}),
            json!({"jsonrpc":"2.0","id":false,"method":"tools/call"}),
            json!({"jsonrpc":"2.0","id":"method","method":5}),
            json!({"jsonrpc":"2.0","id":"params","method":"tools/call","params":null}),
        ] {
            let expected_id = value
                .get("id")
                .filter(|id| valid_id(id))
                .cloned()
                .unwrap_or(Value::Null);
            let Incoming::Rejected(response) = decode(value) else {
                panic!("invalid envelope admitted")
            };
            assert_eq!(response["id"], expected_id);
            let diagnostic: NeedsInput =
                serde_json::from_value(response["error"]["data"].clone()).unwrap();
            assert!(!diagnostic.issues().is_empty());
        }
        for id in [json!(0), json!(-1), json!(0.5), json!("")] {
            let Incoming::Request(request) =
                decode(json!({"jsonrpc":"2.0","id":id,"method":"tools/list"}))
            else {
                panic!("valid ID rejected")
            };
            assert_eq!(request.id(), &id);
        }
    }

    #[test]
    fn notifications_never_become_tool_requests_even_when_their_params_are_wrong() {
        for params in [
            json!({"name":"delete_project","arguments":{"project":"kept"}}),
            json!(null),
        ] {
            assert!(matches!(
                decode(json!({"jsonrpc":"2.0","method":"tools/call","params":params})),
                Incoming::Notification {
                    diagnostic: Some(_),
                    ..
                }
            ));
        }
        assert!(matches!(
            decode(json!({"jsonrpc":"2.0","method":"notifications/initialized"})),
            Incoming::Notification {
                diagnostic: None,
                ..
            }
        ));
    }
}
