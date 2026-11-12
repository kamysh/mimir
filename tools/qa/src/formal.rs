use anyhow::{bail, ensure, Context, Result};
use regex::Regex;
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repository root")
}
fn read(root: &Path, path: &str) -> Result<String> {
    fs::read_to_string(root.join(path)).with_context(|| path.to_string())
}
fn captures(pattern: &str, text: &str) -> Result<Vec<String>> {
    Ok(Regex::new(pattern)?
        .captures_iter(text)
        .map(|c| c[1].to_string())
        .collect())
}
fn kebab(name: &str) -> String {
    let mut s = String::new();
    for (i, c) in name.chars().enumerate() {
        if i > 0 && c.is_ascii_uppercase() {
            s.push('-');
        }
        s.extend(c.to_lowercase());
    }
    s
}
fn variants(root: &Path, path: &str, name: &str) -> Result<Vec<String>> {
    let source = read(root, path)?;
    let re = Regex::new(&format!(
        r"(?s)(?:pub )?enum {} \{{(.*?)\n\}}",
        regex::escape(name)
    ))?;
    let body = re
        .captures(&source)
        .with_context(|| format!("missing enum {name} in {path}"))?;
    captures(r"(?m)^    ([A-Z][A-Za-z]+)\b", &body[1])
}
fn files(dir: &Path, ext: &str, result: &mut Vec<PathBuf>) -> Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if entry.file_type()?.is_dir() {
            files(&path, ext, result)?;
        } else if path.extension().is_some_and(|e| e == ext) {
            result.push(path);
        }
    }
    Ok(())
}

fn migration_body(source: &str) -> Result<String> {
    let mut lines = source.lines();
    ensure!(
        lines.next().map(str::trim) == Some("-- #!migration"),
        "expected migration header"
    );
    let metadata = Regex::new(r"^\s*--\s*(name|description|requires):\s*(.+)\s*([,;])\s*$")?;
    let mut fields = BTreeSet::new();
    while let Some(line) = lines.next() {
        let c = metadata
            .captures(line)
            .context("unsupported or unterminated migration header")?;
        let key = &c[1];
        let value: Value = serde_json::from_str(c[2].trim())?;
        ensure!(
            fields.insert(key.to_string()),
            "repeated migration metadata field"
        );
        ensure!(
            value.is_string()
                || (key == "requires"
                    && value
                        .as_array()
                        .is_some_and(|xs| xs.iter().all(Value::is_string))),
            "invalid migration metadata value"
        );
        if &c[3] == ";" {
            ensure!(
                fields.contains("name") && fields.contains("description"),
                "missing migration metadata"
            );
            let body = lines.collect::<Vec<_>>().join("\n");
            ensure!(
                !body.starts_with("-- #!") && !body.contains("\n-- #!"),
                "expected one migration per file"
            );
            return Ok(body.trim().to_string());
        }
    }
    bail!("unterminated migration header")
}

pub fn check() -> Result<()> {
    let root = root();
    let coverage: Value =
        serde_json::from_str(&read(&root, "docs/FORMAL-BEHAVIOR-COVERAGE.json")?)?;
    let inventory: Value = serde_json::from_str(&read(&root, "docs/FORMAL-INVENTORY.json")?)?;
    let formal = captures(
        r#"(?m)^wireName\s+\w+\s*=\s*"([a-z_]+)""#,
        &read(&root, "spec/Mimir/ToolCatalog.agda")?,
    )?;
    let mut advertised = Vec::new();
    for path in ["crates/mcp/src/main.rs", "crates/mcp/src/learning.rs"] {
        advertised.extend(captures(
            r#""name"\s*:\s*"([a-z_]+)"\s*,\s*"description"\s*:"#,
            &read(&root, path)?,
        )?);
    }
    let operations: Vec<String> = coverage["mcp"]
        .as_array()
        .context("mcp inventory")?
        .iter()
        .map(|x| x["name"].as_str().unwrap_or("").to_string())
        .collect();
    let set = |xs: &[String]| xs.iter().cloned().collect::<BTreeSet<_>>();
    ensure!(
        operations.len() == 34
            && set(&operations).len() == 34
            && set(&operations) == set(&formal)
            && set(&operations) == set(&advertised),
        "MCP inventory mismatch"
    );
    let main = "crates/cli/src/main.rs";
    let mut commands: Vec<String> = variants(&root, main, "Command")?
        .iter()
        .filter(|n| !["Config", "Judge", "Evidence", "Delete", "Doc", "Hook"].contains(&n.as_str()))
        .map(|n| kebab(n))
        .collect();
    for (prefix, name, source) in [
        ("config", "Command", "crates/cli/src/configuration.rs"),
        ("evidence", "EvidenceCmd", main),
        ("delete", "DeleteCmd", main),
        ("doc", "DocCmd", main),
        ("hook", "HookEvent", main),
        ("judge", "JudgeCommand", "crates/cli/src/judge/mod.rs"),
    ] {
        commands.extend(
            variants(&root, source, name)?
                .iter()
                .map(|n| format!("{prefix} {}", kebab(n))),
        );
    }
    let cli: Vec<String> = coverage["cli"]
        .as_array()
        .context("cli inventory")?
        .iter()
        .map(|x| x["name"].as_str().unwrap_or("").to_string())
        .collect();
    ensure!(
        commands.len() == set(&commands).len()
            && commands.len() == cli.len()
            && Some(cli.len() as u64) == coverage["counts"]["cli_leaves"].as_u64()
            && set(&commands) == set(&cli),
        "CLI inventory mismatch"
    );
    let mut agda = Vec::new();
    files(&root.join("spec"), "agda", &mut agda)?;
    let mut modules = BTreeMap::new();
    for path in &agda {
        let name = path
            .strip_prefix(root.join("spec"))?
            .with_extension("")
            .to_string_lossy()
            .replace('/', ".");
        modules.insert(name, path);
    }
    let imports = Regex::new(r"\bimport\s+(Mimir(?:\.[A-Za-z0-9_]+)*)")?;
    let mut reached = BTreeSet::new();
    let mut pending = vec!["Mimir".to_string()];
    while let Some(name) = pending.pop() {
        if !reached.insert(name.clone()) {
            continue;
        }
        let path = modules
            .get(&name)
            .with_context(|| format!("missing module {name}"))?;
        let source = fs::read_to_string(path)?;
        for c in imports.captures_iter(&source) {
            ensure!(modules.contains_key(&c[1]), "missing module {}", &c[1]);
            pending.push(c[1].to_string());
        }
    }
    ensure!(
        reached.len() == modules.len(),
        "not every formal module is reachable"
    );
    let safe = Regex::new(r"\{-#\s*OPTIONS\s+[^#]*--safe\b")?;
    let escape =
        Regex::new(r"\bpostulate\b|\bTERMINATING\b|\bNON_TERMINATING\b|allow-unsolved|\{!")?;
    for path in &agda {
        let source = fs::read_to_string(path)?;
        ensure!(safe.is_match(&source), "unsafe module {}", path.display());
        let code = source
            .lines()
            .map(|x| x.split("--").next().unwrap_or(""))
            .collect::<Vec<_>>()
            .join("\n");
        ensure!(
            !escape.is_match(&code),
            "unchecked construct in {}",
            path.display()
        );
    }
    let mut referenced = BTreeSet::new();
    for category in ["mcp", "cli", "lifecycles"] {
        for item in coverage[category]
            .as_array()
            .with_context(|| category.to_string())?
        {
            let paths = item["completion_modules"]
                .as_array()
                .context("completion modules")?;
            ensure!(!paths.is_empty(), "empty completion modules");
            for p in paths {
                referenced.insert(p.as_str().context("module path")?.to_string());
            }
        }
    }
    for item in coverage["core_library"]
        .as_array()
        .context("core inventory")?
    {
        for p in item["modules"].as_array().context("core modules")? {
            referenced.insert(p.as_str().context("module path")?.to_string());
        }
    }
    let inventory_files = inventory["files"].as_array().context("source inventory")?;
    for item in inventory_files {
        let path = item["path"].as_str().context("artifact path")?;
        ensure!(root.join(path).exists(), "missing artifact {path}");
        if item["classification"] == "production-behavior" {
            let specs = item["behavioral_specification"]
                .as_array()
                .context("behavioral specifications")?;
            ensure!(
                !specs.is_empty(),
                "missing behavioral specifications for {path}"
            );
            for p in specs {
                referenced.insert(p.as_str().context("specification path")?.to_string());
            }
        }
    }
    for path in &referenced {
        ensure!(root.join(path).exists(), "missing referenced path {path}");
        let name = Path::new(path)
            .strip_prefix("spec")?
            .with_extension("")
            .to_string_lossy()
            .replace('/', ".");
        ensure!(reached.contains(&name), "unreachable module {path}");
    }
    let binding = read(&root, "spec/Mimir/MigrationScriptBinding.agda")?;
    let re = Regex::new(r#"(?m)^source Schema\.(\w+) = toList (".*")$"#)?;
    let mut bound = BTreeMap::new();
    for c in re.captures_iter(&binding) {
        let value: String = serde_json::from_str(&c[2])?;
        bound.insert(c[1].to_string(), value.trim().to_string());
    }
    let keys = [
        "initial",
        "searchPath",
        "embeddingTable",
        "evidenceEdges",
        "betaBeliefs",
        "learning",
        "candidates",
        "assessment",
        "owners",
        "allocation",
        "workEvents",
    ];
    let mut sql = Vec::new();
    files(&root.join("crates/core/migrations"), "sql", &mut sql)?;
    sql.sort();
    ensure!(
        sql.len() == keys.len() && bound.len() == keys.len(),
        "migration inventory mismatch"
    );
    for (path, key) in sql.iter().zip(keys) {
        ensure!(
            Some(&migration_body(&fs::read_to_string(path)?)?) == bound.get(key),
            "migration source binding differs: {}",
            path.display()
        );
    }
    println!(
        "{}",
        serde_json::to_string_pretty(
            &json!({"result":"passed", "mcp_operations":operations.len(), "cli_leaves":cli.len(), "lifecycle_groups":coverage["lifecycles"].as_array().map_or(0,Vec::len), "source_artifacts":inventory_files.len(), "production_artifacts":inventory_files.iter().filter(|x| x["classification"] == "production-behavior").count(), "safe_modules":agda.len(), "root_reachable_modules":reached.len(), "referenced_modules":referenced.len(), "exact_migration_bodies":sql.len(), "boundary":"Inventory and structural audit; Agda checking and Rust correspondence are separate."})
        )?
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::migration_body;
    const H: &str = "-- #!migration\n-- name: \"upgrade\",\n-- description: \"Keep old IDs\";\n";
    #[test]
    fn preserves_sql_comments_and_semicolons() {
        let body = "-- Keep old IDs.\nDO $$ BEGIN PERFORM f(); END $$;\nSELECT ';';";
        assert_eq!(migration_body(&format!("{H}\n{body}\n")).unwrap(), body);
    }
    #[test]
    fn metadata_semicolon_and_requires() {
        let h = H.replace(
            "IDs\";",
            "IDs; add default\",\n-- requires: [\"initial\", \"owners\"]; ",
        );
        assert_eq!(
            migration_body(&format!("{h}\nSELECT 1;")).unwrap(),
            "SELECT 1;"
        );
    }
    #[test]
    fn refuses_unterminated_missing_and_repeated_migrations() {
        assert!(migration_body(&H.replace("IDs\";", "IDs\",")).is_err());
        assert!(migration_body("-- #!migration\n-- name: \"x\";\nSELECT 1;").is_err());
        assert!(migration_body(&format!("{H}SELECT 1;\n{H}SELECT 2;")).is_err());
    }
    #[test]
    fn detects_changed_sql_comment() {
        let a = format!("{H}-- Keep old IDs.\nSELECT 1;");
        assert_ne!(
            migration_body(&a).unwrap(),
            migration_body(&a.replace("Keep old IDs.", "Replace IDs.")).unwrap()
        );
    }
}
