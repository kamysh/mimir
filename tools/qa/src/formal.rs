use anyhow::{ensure, Context, Result};
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
fn files(dir: &Path, accepts: &impl Fn(&Path) -> bool, result: &mut Vec<PathBuf>) -> Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if entry.file_type()?.is_dir() {
            files(&path, accepts, result)?;
        } else if accepts(&path) {
            result.push(path);
        }
    }
    Ok(())
}

fn module_stem(path: &Path) -> Option<&str> {
    let name = path.file_name()?.to_str()?;
    name.strip_suffix(".lagda.md")
        .or_else(|| name.strip_suffix(".agda"))
}

fn module_name(path: &Path) -> Result<String> {
    let stem = module_stem(path).context("expected a formal module path")?;
    Ok(path
        .strip_prefix("spec")?
        .with_file_name(stem)
        .to_string_lossy()
        .replace('/', "."))
}

fn markdown_agda(source: &str) -> Result<String> {
    let mut code = String::new();
    let mut in_code = false;
    for line in source.lines() {
        if in_code {
            if line.trim() == "```" {
                in_code = false;
            } else {
                code.push_str(line);
                code.push('\n');
            }
        } else if line.trim_end().ends_with("```agda") {
            // Agda scans for its own fences even inside other Markdown blocks.
            in_code = true;
        }
    }
    ensure!(!in_code, "unterminated Agda code fence");
    Ok(code)
}

#[derive(Debug, PartialEq, Eq)]
struct BoundMigration {
    sql: String,
    requires: BTreeSet<String>,
}

fn check_migrations(
    manifest: &str,
    binding: &str,
    actual: Vec<kryzhen::Migration>,
) -> Result<usize> {
    let names = Regex::new(r#"(?m)^name (\w+) = "([^"]+)"$"#)?;
    let mut by_constructor = BTreeMap::new();
    for c in names.captures_iter(manifest) {
        ensure!(
            by_constructor
                .insert(c[1].to_owned(), c[2].to_owned())
                .is_none(),
            "duplicate migration constructor {}",
            &c[1]
        );
    }
    let mut dependencies = BTreeMap::new();
    let requires = Regex::new(r"(?m)^requires (\w+) = (.+)$")?;
    for c in requires.captures_iter(manifest) {
        let mut list = c[2].split('∷').map(str::trim).collect::<Vec<_>>();
        ensure!(
            list.pop() == Some("[]"),
            "unsupported dependency list for {}",
            &c[1]
        );
        let names = list
            .into_iter()
            .map(|ctor| {
                by_constructor
                    .get(ctor)
                    .cloned()
                    .with_context(|| format!("unknown dependency {ctor}"))
            })
            .collect::<Result<_>>()?;
        ensure!(
            dependencies.insert(c[1].to_owned(), names).is_none(),
            "duplicate dependency declaration for {}",
            &c[1]
        );
    }
    let sources = Regex::new(r#"(?m)^source Manifest\.(\w+) = toList (".*")$"#)?;
    let mut expected = BTreeMap::new();
    for c in sources.captures_iter(binding) {
        let name = by_constructor
            .remove(&c[1])
            .with_context(|| format!("missing or repeated migration name for {}", &c[1]))?;
        let requires = dependencies
            .remove(&c[1])
            .with_context(|| format!("missing dependencies for {name}"))?;
        let sql: String = serde_json::from_str(&c[2])?;
        ensure!(
            expected
                .insert(
                    name.clone(),
                    BoundMigration {
                        sql: sql.trim().into(),
                        requires
                    }
                )
                .is_none(),
            "duplicate specification for {name}"
        );
    }
    ensure!(
        by_constructor.is_empty() && dependencies.is_empty(),
        "migration declaration has no SQL binding"
    );
    let count = actual.len();
    for migration in actual {
        let name = &migration.name.0;
        let spec = expected
            .remove(name)
            .with_context(|| format!("missing or duplicate migration binding: {name}"))?;
        ensure!(
            spec.sql == migration.script.trim(),
            "migration SQL differs: {name}"
        );
        let requires = migration
            .requires
            .into_iter()
            .map(|dep| dep.0)
            .collect::<BTreeSet<_>>();
        ensure!(
            spec.requires == requires,
            "migration dependencies differ: {name}"
        );
    }
    ensure!(
        expected.is_empty(),
        "missing migration blocks: {:?}",
        expected.keys()
    );
    Ok(count)
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
    files(
        &root.join("spec"),
        &|path| module_stem(path).is_some(),
        &mut agda,
    )?;
    let mut modules = BTreeMap::new();
    for path in &agda {
        let name = module_name(path.strip_prefix(&root)?)?;
        let source = fs::read_to_string(path)?;
        let code = if path.extension().is_some_and(|ext| ext == "md") {
            markdown_agda(&source).with_context(|| path.display().to_string())?
        } else {
            source
        };
        ensure!(
            modules.insert(name.clone(), (path, code)).is_none(),
            "duplicate formal module {name}"
        );
    }
    let imports = Regex::new(r"\bimport\s+(Mimir(?:\.[A-Za-z0-9_]+)*)")?;
    let mut reached = BTreeSet::new();
    let mut pending = vec!["Mimir".to_string()];
    while let Some(name) = pending.pop() {
        if !reached.insert(name.clone()) {
            continue;
        }
        let (_, source) = modules
            .get(&name)
            .with_context(|| format!("missing module {name}"))?;
        for c in imports.captures_iter(source) {
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
    for (path, source) in modules.values() {
        ensure!(safe.is_match(source), "unsafe module {}", path.display());
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
        let name = module_name(Path::new(path))?;
        ensure!(reached.contains(&name), "unreachable module {path}");
    }
    let binding = read(&root, "spec/Mimir/MigrationScriptBinding.agda")?;
    let manifest = read(&root, "spec/Mimir/Migrations.agda")?;
    let mut paths = Vec::new();
    files(
        &root.join("crates/core/migrations"),
        &|path| path.extension().is_some_and(|ext| ext == "sql"),
        &mut paths,
    )?;
    let mut migrations = Vec::new();
    for path in paths {
        let parsed =
            kryzhen::parser::parse_file(&fs::read_to_string(&path)?, &path.display().to_string())?;
        migrations.extend(kryzhen::file::apply_implicit_deps(parsed));
    }
    let migration_count = check_migrations(&manifest, &binding, migrations)?;
    println!(
        "{}",
        serde_json::to_string_pretty(
            &json!({"result":"passed", "mcp_operations":operations.len(), "cli_leaves":cli.len(), "lifecycle_groups":coverage["lifecycles"].as_array().map_or(0,Vec::len), "source_artifacts":inventory_files.len(), "production_artifacts":inventory_files.iter().filter(|x| x["classification"] == "production-behavior").count(), "safe_modules":agda.len(), "root_reachable_modules":reached.len(), "referenced_modules":referenced.len(), "exact_migration_bodies":migration_count, "boundary":"Inventory and structural audit; Agda checking and Rust correspondence are separate."})
        )?
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{check_migrations, markdown_agda, module_name};
    use std::path::Path;

    #[test]
    fn literate_modules_use_agda_names_and_scan_agda_fences() {
        let source = "Prose: import Mimir.Prose\n\
                      ````text\n```agda\nimport Mimir.CheckedInsideText\n```\n````\n\
                      ```agda\n{-# OPTIONS --safe #-}\nimport Mimir.Real\n```\n\
                      ```text\npostulate example\n```\n";
        assert_eq!(
            module_name(Path::new("spec/Mimir/Reader/Example.lagda.md")).unwrap(),
            "Mimir.Reader.Example"
        );
        assert_eq!(
            markdown_agda(source).unwrap(),
            "import Mimir.CheckedInsideText\n{-# OPTIONS --safe #-}\nimport Mimir.Real\n"
        );
        assert!(markdown_agda("```agda\nimport Mimir.Unclosed\n").is_err());
    }
    #[test]
    fn migrations_bind_by_name_across_files_and_within_one_file() {
        let names = "name one = \"first\"\nname two = \"second\"\nrequires one = []\nrequires two = one ∷ []";
        let sql = "source Manifest.one = toList \"-- Keep IDs.\\nSELECT ';';\"\nsource Manifest.two = toList \"SELECT 2;\"";
        let first = "-- #!migration\n-- name: \"first\",\n-- description: \"First\";\n-- Keep IDs.\nSELECT ';';\n";
        let second = "-- #!migration\n-- name: \"second\",\n-- description: \"Second\",\n-- requires: \"first\";\nSELECT 2;\n";
        let parse = |text: &str, label| {
            kryzhen::file::apply_implicit_deps(kryzhen::parser::parse_file(text, label).unwrap())
        };
        let mut reversed_files = parse(second, "a.sql");
        reversed_files.extend(parse(first, "z.sql"));
        assert_eq!(check_migrations(names, sql, reversed_files).unwrap(), 2);
        let combined = format!("{first}{second}");
        assert_eq!(
            check_migrations(names, sql, parse(&combined, "both.sql")).unwrap(),
            2
        );
        for wrong in [
            sql.replace("SELECT 2", "SELECT 3"),
            sql.replace("Keep IDs", "Remove IDs"),
        ] {
            assert!(check_migrations(names, &wrong, parse(&combined, "both.sql")).is_err());
        }
        assert!(check_migrations(
            &names.replace("one ∷ []", "[]"),
            sql,
            parse(&combined, "both.sql")
        )
        .is_err());
        assert!(check_migrations(
            names,
            sql,
            parse(&format!("{first}{first}"), "duplicate.sql")
        )
        .is_err());
        assert!(check_migrations(names, sql, parse(first, "missing.sql")).is_err());
    }
}
