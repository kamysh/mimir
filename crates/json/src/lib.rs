//! serde_json owns syntax; this adapter grows the Serde stack and owns trees
//! so copying, formatting and cleanup do not recursively exhaust that stack.
use serde::{
    de::{DeserializeOwned, Error, MapAccess, SeqAccess, Visitor},
    Deserialize, Serialize,
};
pub use serde_json::{Error as JsonError, Value};
use std::{
    fmt,
    ops::{Deref, DerefMut},
};

pub struct Document(Value);
impl From<Value> for Document {
    fn from(value: Value) -> Self {
        Self(value)
    }
}
impl PartialEq<Value> for Document {
    fn eq(&self, other: &Value) -> bool {
        equal(&self.0, other)
    }
}
impl PartialEq<Document> for Value {
    fn eq(&self, other: &Document) -> bool {
        equal(self, &other.0)
    }
}
impl PartialEq for Document {
    fn eq(&self, other: &Self) -> bool {
        equal(&self.0, &other.0)
    }
}
impl Eq for Document {}
pub fn equal(first: &Value, second: &Value) -> bool {
    let mut pending = vec![(first, second)];
    while let Some((a, b)) = pending.pop() {
        match (a, b) {
            (Value::Array(a), Value::Array(b)) if a.len() == b.len() => {
                pending.extend(a.iter().zip(b))
            }
            (Value::Object(a), Value::Object(b)) if a.len() == b.len() => {
                for (key, value) in a {
                    let Some(other) = b.get(key) else {
                        return false;
                    };
                    pending.push((value, other));
                }
            }
            (Value::Array(_) | Value::Object(_), _) | (_, Value::Array(_) | Value::Object(_)) => {
                return false
            }
            _ if a != b => return false,
            _ => {}
        }
    }
    true
}
impl Document {
    pub fn new(value: Value) -> Self {
        Self(value)
    }
    pub fn into_value(mut self) -> Value {
        std::mem::take(&mut self.0)
    }
}
impl Deref for Document {
    type Target = Value;
    fn deref(&self) -> &Value {
        &self.0
    }
}
impl DerefMut for Document {
    fn deref_mut(&mut self) -> &mut Value {
        &mut self.0
    }
}
impl Drop for Document {
    fn drop(&mut self) {
        drop_value(std::mem::take(&mut self.0));
    }
}
impl Clone for Document {
    fn clone(&self) -> Self {
        Self(clone_value(&self.0))
    }
}
impl fmt::Display for Document {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&to_string(self).map_err(|_| fmt::Error)?)
    }
}
impl fmt::Debug for Document {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&to_string(self).map_err(|_| fmt::Error)?)
    }
}
impl Serialize for Document {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serde_stacker::Serializer::new(s))
    }
}
impl<'de> Deserialize<'de> for Document {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct Tree;
        impl<'de> Visitor<'de> for Tree {
            type Value = Document;
            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("a JSON value")
            }
            fn visit_unit<E: Error>(self) -> Result<Document, E> {
                Ok(Document(Value::Null))
            }
            fn visit_bool<E: Error>(self, v: bool) -> Result<Document, E> {
                Ok(Document(v.into()))
            }
            fn visit_i64<E: Error>(self, v: i64) -> Result<Document, E> {
                Ok(Document(v.into()))
            }
            fn visit_u64<E: Error>(self, v: u64) -> Result<Document, E> {
                Ok(Document(v.into()))
            }
            fn visit_f64<E: Error>(self, v: f64) -> Result<Document, E> {
                serde_json::Number::from_f64(v)
                    .map(|v| Document(Value::Number(v)))
                    .ok_or_else(|| E::custom("non-finite JSON number"))
            }
            fn visit_str<E: Error>(self, v: &str) -> Result<Document, E> {
                Ok(Document(Value::String(v.into())))
            }
            fn visit_string<E: Error>(self, v: String) -> Result<Document, E> {
                Ok(Document(Value::String(v)))
            }
            fn visit_seq<A: SeqAccess<'de>>(self, mut a: A) -> Result<Document, A::Error> {
                let mut result = Document(Value::Array(Vec::new()));
                while let Some(child) = a.next_element::<Document>()? {
                    result.as_array_mut().unwrap().push(child.into_value());
                }
                Ok(result)
            }
            fn visit_map<A: MapAccess<'de>>(self, mut a: A) -> Result<Document, A::Error> {
                let mut result = Document(Value::Object(serde_json::Map::new()));
                while let Some((key, child)) = a.next_entry::<String, Document>()? {
                    if let Some(old) = result
                        .as_object_mut()
                        .unwrap()
                        .insert(key, child.into_value())
                    {
                        drop_value(old);
                    }
                }
                Ok(result)
            }
        }
        d.deserialize_any(Tree)
    }
}

/// Detach children before dropping their containers, including object values.
pub fn drop_value(value: Value) {
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        match value {
            Value::Array(items) => pending.extend(items),
            Value::Object(fields) => pending.extend(fields.into_iter().map(|(_, v)| v)),
            _ => {}
        }
    }
}

pub fn replace(target: &mut Value, replacement: Value) {
    drop_value(std::mem::replace(target, replacement));
}

/// Copy a tree using heap work lists rather than recursive Value::clone.
pub fn clone_value(value: &Value) -> Value {
    enum Task<'a> {
        Visit(&'a Value),
        Array(usize),
        Object(Vec<String>),
    }
    let mut tasks = vec![Task::Visit(value)];
    let mut completed = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(Value::Array(items)) => {
                tasks.push(Task::Array(items.len()));
                tasks.extend(items.iter().rev().map(Task::Visit));
            }
            Task::Visit(Value::Object(fields)) => {
                tasks.push(Task::Object(fields.keys().cloned().collect()));
                tasks.extend(fields.values().rev().map(Task::Visit));
            }
            Task::Visit(scalar) => completed.push(scalar.clone()),
            Task::Array(count) => {
                let items = completed.split_off(completed.len() - count);
                completed.push(Value::Array(items));
            }
            Task::Object(keys) => {
                let values = completed.split_off(completed.len() - keys.len());
                completed.push(Value::Object(keys.into_iter().zip(values).collect()));
            }
        }
    }
    completed.pop().expect("one tree was copied")
}

pub fn parse(text: &str) -> Result<Document, JsonError> {
    let mut decoder = serde_json::Deserializer::from_str(text);
    decoder.disable_recursion_limit();
    let tree = Document::deserialize(serde_stacker::Deserializer::new(&mut decoder))?;
    decoder.end()?;
    Ok(tree)
}
pub fn from_str<T: DeserializeOwned>(text: &str) -> Result<T, JsonError> {
    let document = parse(text)?;
    decode_ref(&document)
}
pub fn from_slice<T: DeserializeOwned>(bytes: &[u8]) -> Result<T, JsonError> {
    let mut decoder = serde_json::Deserializer::from_slice(bytes);
    decoder.disable_recursion_limit();
    let tree = Document::deserialize(serde_stacker::Deserializer::new(&mut decoder))?;
    decoder.end()?;
    decode_ref(&tree)
}
pub fn from_value<T: DeserializeOwned>(value: impl Into<Document>) -> Result<T, JsonError> {
    let value = value.into();
    decode_ref(&value)
}
pub fn decode_ref<T: DeserializeOwned>(value: &Value) -> Result<T, JsonError> {
    T::deserialize(serde_stacker::Deserializer::new(value))
}
pub fn to_vec<T: Serialize + ?Sized>(value: &T) -> Result<Vec<u8>, JsonError> {
    let mut bytes = Vec::new();
    let mut encoder = serde_json::Serializer::new(&mut bytes);
    value.serialize(serde_stacker::Serializer::new(&mut encoder))?;
    Ok(bytes)
}
pub fn to_string<T: Serialize + ?Sized>(value: &T) -> Result<String, JsonError> {
    Ok(String::from_utf8(to_vec(value)?).expect("the JSON serializer emits UTF-8"))
}
pub fn to_string_pretty<T: Serialize + ?Sized>(value: &T) -> Result<String, JsonError> {
    let mut bytes = Vec::new();
    let mut encoder = serde_json::Serializer::pretty(&mut bytes);
    value.serialize(serde_stacker::Serializer::new(&mut encoder))?;
    Ok(String::from_utf8(bytes).expect("the JSON serializer emits UTF-8"))
}
pub fn to_value<T: Serialize>(value: T) -> Result<Value, JsonError> {
    value.serialize(serde_stacker::Serializer::new(
        serde_json::value::Serializer,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn deeply_nested(depth: usize) -> String {
        let mut text = "{\"child\":[".repeat(depth);
        text.push_str("\"complete payload\"");
        text.push_str(&"]}".repeat(depth));
        text
    }
    #[test]
    fn nested_arrays_and_objects_round_trip_copy_format_compare_and_drop() {
        // A small ordinary thread stack makes accidental recursive Clone/Drop
        // fail reliably. This is test input, never a product depth allowance.
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let text = deeply_nested(10000);
                let tree = parse(&text).unwrap();
                let copy = tree.clone();
                assert!(equal(&tree, &copy));
                assert_eq!(to_string(&tree).unwrap(), text);
                assert_eq!(format!("{tree}"), text);
                let pretty = format!("{tree:?}");
                let reparsed = parse(&pretty).unwrap();
                assert!(equal(&tree, &reparsed));
                drop((tree, copy, reparsed));
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn malformed_suffix_and_replaced_duplicate_values_release_complete_deep_subtrees() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let nested = deeply_nested(10000);
                for bad in [
                    format!("[{nested},"),
                    format!("{{\"stored\":{nested},\"unfinished\":"),
                    format!("{nested} false"),
                ] {
                    assert!(parse(&bad).is_err());
                }
                let doc = parse(&format!("{{\"same\":{nested},\"same\":1}}")).unwrap();
                assert_eq!(doc["same"], 1);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn replacing_a_nested_field_releases_the_previous_tree_without_recursion() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut document =
                    parse(&format!(r#"{{"replace":{}}}"#, deeply_nested(10000))).unwrap();
                replace(&mut document["replace"], Value::Bool(true));
                assert_eq!(document["replace"], true);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
