//! Pure MCP envelope admission, before any registered business handler.
use mimir_core::{
    interaction::{CorrectionItem, Location, NeedsInput},
    validation::{Code, Fault, Segment},
};
use mimir_json::Document;
use serde::de::{DeserializeSeed, Error, MapAccess, SeqAccess, Visitor};
use serde_json::{json, Value};
use std::fmt;

// Serde still owns JSON syntax and scalar decoding. This visitor records
// repeated member paths before an object insertion could hide them. Nothing
// is routed until the complete input has been read and this list is empty.
struct CheckedValue<'a> {
    path: &'a mut Vec<Segment>,
    repeated: &'a mut Vec<Vec<Segment>>,
}
impl<'de> DeserializeSeed<'de> for CheckedValue<'_> {
    type Value = Document;
    fn deserialize<D: serde::Deserializer<'de>>(self, decoder: D) -> Result<Document, D::Error> {
        decoder.deserialize_any(self)
    }
}
impl<'de> Visitor<'de> for CheckedValue<'_> {
    type Value = Document;
    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a JSON value")
    }
    fn visit_unit<E: Error>(self) -> Result<Document, E> {
        Ok(Document::new(Value::Null))
    }
    fn visit_bool<E: Error>(self, value: bool) -> Result<Document, E> {
        Ok(Document::new(Value::Bool(value)))
    }
    fn visit_i64<E: Error>(self, value: i64) -> Result<Document, E> {
        Ok(Document::new(value.into()))
    }
    fn visit_u64<E: Error>(self, value: u64) -> Result<Document, E> {
        Ok(Document::new(value.into()))
    }
    fn visit_f64<E: Error>(self, value: f64) -> Result<Document, E> {
        serde_json::Number::from_f64(value)
            .map(|v| Document::new(Value::Number(v)))
            .ok_or_else(|| E::custom("JSON number is not finite"))
    }
    fn visit_str<E: Error>(self, value: &str) -> Result<Document, E> {
        Ok(Document::new(Value::String(value.into())))
    }
    fn visit_string<E: Error>(self, value: String) -> Result<Document, E> {
        Ok(Document::new(Value::String(value)))
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut sequence: A) -> Result<Document, A::Error> {
        let mut values = Document::new(Value::Array(Vec::new()));
        loop {
            self.path
                .push(Segment::Index(values.as_array().unwrap().len()));
            let child = sequence.next_element_seed(CheckedValue {
                path: &mut *self.path,
                repeated: &mut *self.repeated,
            });
            self.path.pop();
            let Some(value) = child? else {
                break;
            };
            values.as_array_mut().unwrap().push(value.into_value());
        }
        Ok(values)
    }
    fn visit_map<A: MapAccess<'de>>(self, mut object: A) -> Result<Document, A::Error> {
        let mut values = Document::new(Value::Object(serde_json::Map::new()));
        while let Some(key) = object.next_key::<String>()? {
            self.path.push(Segment::Key(key.clone()));
            if values.as_object().unwrap().contains_key(&key) {
                self.repeated.push(self.path.clone());
            }
            let child = object.next_value_seed(CheckedValue {
                path: &mut *self.path,
                repeated: &mut *self.repeated,
            });
            self.path.pop();
            let value = child?;
            if let Some(replaced) = values
                .as_object_mut()
                .unwrap()
                .insert(key, value.into_value())
            {
                mimir_json::drop_value(replaced);
            }
        }
        Ok(values)
    }
}

pub fn parse(text: &str) -> Result<Incoming, serde_json::Error> {
    let mut decoder = serde_json::Deserializer::from_str(text);
    decoder.disable_recursion_limit();
    let mut repeated = Vec::new();
    let mut path = Vec::new();
    let value = CheckedValue {
        path: &mut path,
        repeated: &mut repeated,
    }
    .deserialize(serde_stacker::Deserializer::new(&mut decoder))?;
    decoder.end()?;
    if repeated.is_empty() {
        return Ok(decode(value.into_value()));
    }
    let repeated_id = repeated
        .iter()
        .any(|path| matches!(path.as_slice(), [Segment::Key(key)] if key == "id"));
    let mut issues = repeated.into_iter().map(|path| CorrectionItem::new(
        Location::Request,
        Fault {path,code:Code::Duplicate,message:"This field occurs more than once; no business operation was executed.".into()},
        "One intended value for each field.".into(),
        "Send this field exactly once. Decide which value was intended; do not rely on a first-value or last-value rule.".into(),
    ).expect("duplicate-field diagnostics contain paths and a repair"));
    let diagnostic = report(
        issues.next().expect("repeated fields were checked"),
        issues.collect(),
    );
    if value
        .as_object()
        .is_some_and(|fields| !fields.contains_key("id"))
    {
        return Ok(Incoming::Notification {
            method: "ambiguous message".into(),
            diagnostic: Some(diagnostic),
        });
    }
    let id = if repeated_id {
        Value::Null
    } else {
        value
            .get("id")
            .filter(|id| valid_id(id))
            .cloned()
            .unwrap_or(Value::Null)
    };
    Ok(Incoming::Rejected(error(
        id,
        -32600,
        "Invalid Request",
        diagnostic,
    )))
}

pub struct Request {
    id: Value,
    method: String,
    params: Document,
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

pub fn invalid_params(id: &Value, correction: NeedsInput) -> Value {
    error(id.clone(), -32602, "Invalid params", correction)
}

pub fn decode(value: Value) -> Incoming {
    let mut value = Document::new(value);
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
    let id = provided_id.expect("admitted requests have an ID").clone();
    let params = Document::new(
        value
            .as_object_mut()
            .expect("checked object")
            .remove("params")
            .unwrap_or_else(|| json!({})),
    );
    Incoming::Request(Request { id, method, params })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deep_requests_and_replaced_values_do_not_exhaust_the_stack_or_change_admission() {
        std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
            let depth=10000;
            let nested=format!("{}null{}", "[".repeat(depth), "]".repeat(depth));
            let clean=format!(r#"{{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{{"name":"list_beliefs","arguments":{{"extra":{nested}}}}}}}"#);
            let Incoming::Request(request)=parse(&clean).unwrap() else {panic!("valid envelope refused")};
            let (_,arguments)=super::super::admission::tool_parameters(request.params()).unwrap();
            assert!(arguments["extra"].is_array());
            let copy=arguments.clone();
            assert!(mimir_json::equal(&arguments,&copy));
            drop((request,arguments,copy));
            let duplicate=format!(r#"{{"jsonrpc":"2.0","id":2,"method":"tools/list","params":{{"extra":{nested},"extra":null}}}}"#);
            assert!(matches!(parse(&duplicate).unwrap(),Incoming::Rejected(_)));
            assert!(parse(&format!("[{nested},")).is_err());
            assert!(matches!(parse(r#"{"jsonrpc":"2.0","id":3,"method":"tools/list"}"#).unwrap(),Incoming::Request(_)));
        }).unwrap().join().unwrap();
    }

    #[test]
    fn duplicate_members_are_located_without_choosing_a_response_id() {
        let Incoming::Rejected(response) = parse(r#"{"jsonrpc":"2.0","id":1,"id":2,"method":"tools/list","method":"tools/call","params":{"arguments":{"project":"one","project":"two","sources":[{"actor":"one","actor":"two"}]}}}"#).unwrap() else {panic!("duplicates admitted")};
        assert_eq!(response["id"], Value::Null);
        let diagnostic: NeedsInput =
            mimir_json::from_value(response["error"]["data"].clone()).unwrap();
        let paths: Vec<_> = diagnostic
            .issues()
            .iter()
            .map(|item| item.fault().path.clone())
            .collect();
        assert_eq!(
            paths,
            vec![
                vec![Segment::Key("id".into())],
                vec![Segment::Key("method".into())],
                vec![
                    Segment::Key("params".into()),
                    Segment::Key("arguments".into()),
                    Segment::Key("project".into())
                ],
                vec![
                    Segment::Key("params".into()),
                    Segment::Key("arguments".into()),
                    Segment::Key("sources".into()),
                    Segment::Index(0),
                    Segment::Key("actor".into())
                ]
            ]
        );
    }

    #[test]
    fn repeated_notification_fields_never_acquire_a_response_or_handler() {
        let Incoming::Notification {diagnostic:Some(diagnostic),..}=parse(r#"{"jsonrpc":"2.0","method":"tools/call","params":{"arguments":{"project":"same","project":"same"}}}"#).unwrap() else {panic!("ambiguous notification was admitted")};
        assert_eq!(diagnostic.issues().len(), 1);
        assert_eq!(diagnostic.issues()[0].fault().code, Code::Duplicate);
    }

    #[test]
    fn clean_values_keep_standard_json_numbers_strings_and_complete_input_checks() {
        let text = r#"{"jsonrpc":"2.0","id":0,"method":"tools/list","params":{"values":[null,true,-1,18446744073709551615,1.0,1e20,"escaped\\text\n","\u0061"],"nested":{"whole":[]}}}"#;
        let expected: Value = mimir_json::from_str(text).unwrap();
        let Incoming::Request(request) = parse(text).unwrap() else {
            panic!("clean input refused")
        };
        assert_eq!(request.id(), &expected["id"]);
        assert_eq!(request.params(), &expected["params"]);
        for broken in [format!("{text} null"), "{\"a\":1,\"a\":2".into()] {
            assert!(parse(&broken).is_err());
        }
    }

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
                mimir_json::from_value(response["error"]["data"].clone()).unwrap();
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
