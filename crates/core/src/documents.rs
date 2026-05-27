use serde::{Deserialize, Serialize};
use uuid::Uuid;

// ---------------------------------------------------------------------------
// DocumentChunk — one heading-bounded markdown section.
// Stored as an AGE vertex (label "DocumentChunk").
// section_path = [] for root chunks; ["H1", "H2"] for nested chunks.
// parent_id mirrors the CONTAINS edge parent for easy lookup in queries.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocumentChunk {
    pub id: Uuid,
    pub document_path: String,
    pub section_path: Vec<String>,
    pub content: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent_id: Option<Uuid>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub project: Option<String>,
}

impl DocumentChunk {
    pub fn new(
        document_path: String,
        section_path: Vec<String>,
        content: String,
        parent_id: Option<Uuid>,
        project: Option<String>,
    ) -> Self {
        Self::with_id(
            Uuid::new_v4(),
            document_path,
            section_path,
            content,
            parent_id,
            project,
        )
    }

    pub fn with_id(
        id: Uuid,
        document_path: String,
        section_path: Vec<String>,
        content: String,
        parent_id: Option<Uuid>,
        project: Option<String>,
    ) -> Self {
        Self { id, document_path, section_path, content, parent_id, project }
    }
}

// ---------------------------------------------------------------------------
// QueryResult — one item in the query_document response.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueryResult {
    pub id: String,
    pub document_path: String,
    pub section_path: Vec<String>,
    pub content: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parent_content: Option<String>,
}

// ---------------------------------------------------------------------------
// Markdown parser — splits a document into heading-bounded chunks.
//
// Each ATX heading (# / ## / ###…) starts a new chunk.
// Text before the first heading becomes the root chunk (section_path=[]).
// The heading line is included as the first line of the chunk's content.
//
// Parent tracking uses pre-assigned UUIDs so children can reference the
// parent's ID before the parent chunk is flushed to the output vec.
// ---------------------------------------------------------------------------

pub fn parse_markdown(
    text: &str,
    document_path: &str,
    project: Option<&str>,
) -> Vec<DocumentChunk> {
    let mut chunks: Vec<DocumentChunk> = Vec::new();
    // stack: (depth, heading_text, pre_assigned_uuid)
    let mut stack: Vec<(usize, String, Uuid)> = Vec::new();
    let mut buf = String::new();
    let mut section_path: Vec<String> = Vec::new();
    let mut parent_id: Option<Uuid> = None;
    let mut current_id = Uuid::new_v4();
    let proj = project.map(str::to_string);

    macro_rules! flush {
        () => {{
            let trimmed = buf.trim().to_string();
            buf.clear();
            if !trimmed.is_empty() {
                chunks.push(DocumentChunk::with_id(
                    current_id,
                    document_path.to_string(),
                    section_path.clone(),
                    trimmed,
                    parent_id,
                    proj.clone(),
                ));
            }
        }};
    }

    for line in text.lines() {
        // Detect ATX heading: one or more '#' followed by ' ' or end of line.
        if let Some(rest) = line.strip_prefix('#') {
            let mut depth = 1usize;
            let mut r = rest;
            while let Some(s) = r.strip_prefix('#') {
                depth += 1;
                r = s;
            }
            if r.starts_with(' ') || r.is_empty() {
                let heading_text = r.trim().to_string();

                flush!();

                // Pop stack entries at depth >= this heading's depth.
                while stack.last().map_or(false, |f| f.0 >= depth) {
                    stack.pop();
                }

                let new_parent_id = stack.last().map(|f| f.2);
                section_path = stack.iter().map(|f| f.1.clone()).collect();
                section_path.push(heading_text.clone());

                let new_id = Uuid::new_v4();
                stack.push((depth, heading_text, new_id));
                current_id = new_id;
                parent_id = new_parent_id;

                buf.push_str(line);
                buf.push('\n');
                continue;
            }
        }
        buf.push_str(line);
        buf.push('\n');
    }
    flush!();
    chunks
}
