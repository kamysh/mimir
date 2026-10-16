//! PostgreSQL password sources and password-file grammar.
use std::path::PathBuf;

pub(crate) fn resolve(
    configured: Option<&str>,
    passfile: Option<&str>,
    host: &str,
    port: u16,
    database: &str,
    user: &str,
) -> Option<String> {
    configured
        .map(str::to_owned)
        .or_else(|| {
            std::env::var("PGPASSWORD")
                .ok()
                .filter(|value| !value.is_empty())
        })
        .or_else(|| {
            let path = passfile
                .map(PathBuf::from)
                .or_else(|| std::env::var_os("PGPASSFILE").map(PathBuf::from))
                .or_else(|| {
                    std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".pgpass"))
                })?;
            let metadata = std::fs::metadata(&path).ok()?;
            if !metadata.is_file() {
                return None;
            }
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                if metadata.permissions().mode() & 0o077 != 0 {
                    tracing::warn!(
                        "password file ignored: group or world permissions; use chmod 600"
                    );
                    return None;
                }
            }
            let content = std::fs::read_to_string(path).ok()?;
            lookup(&content, host, port, database, user)
        })
}

fn field(input: &str) -> (String, Option<&str>) {
    let mut value = String::new();
    let mut chars = input.char_indices();
    while let Some((index, ch)) = chars.next() {
        match ch {
            ':' => return (value, Some(&input[index + 1..])),
            '\\' => value.push(chars.next().map_or('\\', |(_, escaped)| escaped)),
            _ => value.push(ch),
        }
    }
    (value, None)
}

fn lookup(content: &str, host: &str, port: u16, database: &str, user: &str) -> Option<String> {
    let port = port.to_string();
    'lines: for line in content.split('\n') {
        let line = line.trim_end_matches('\r');
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut rest = line;
        for expected in [host, &port, database, user] {
            let wildcard = rest.starts_with("*:");
            let (value, next) = field(rest);
            let Some(next) = next else {
                continue 'lines;
            };
            if !wildcard && value != expected {
                continue 'lines;
            }
            rest = next;
        }
        return Some(field(rest).0);
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escapes_quotes_spaces_and_unicode_are_preserved() {
        let content = "host\\:name:5432:db\\\\name:user\\:name:  '\"пароль\\:with\\\\spaces  \r\n";
        assert_eq!(
            lookup(content, "host:name", 5432, "db\\name", "user:name").as_deref(),
            Some("  '\"пароль:with\\spaces  ")
        );
    }

    #[test]
    fn first_match_comments_wildcards_and_malformed_lines() {
        let content = "#*:*:*:*:comment\nbad:line\nother:*:*:*:wrong\nlocalhost:*:db:user:first\n*:*:*:*:last";
        assert_eq!(
            lookup(content, "localhost", 5432, "db", "user").as_deref(),
            Some("first")
        );
        assert_eq!(
            lookup("localhost:5432:db:user", "localhost", 5432, "db", "user"),
            None
        );
        assert_eq!(
            lookup("*:*:*:*:", "localhost", 5432, "db", "user"),
            Some(String::new())
        );
    }

    #[test]
    fn escaped_star_is_literal_and_line_endings_are_not_password_spaces() {
        let content = "*:*:\\*:user:literal\n*:*:*:*:fallback";
        assert_eq!(
            lookup(content, "host", 5432, "*", "user").as_deref(),
            Some("literal")
        );
        assert_eq!(
            lookup(content, "host", 5432, "db", "user").as_deref(),
            Some("fallback")
        );
        for ending in ["", "\n", "\r\n", "\r"] {
            assert_eq!(
                lookup(
                    &format!("*:*:*:*: value {ending}"),
                    "host",
                    5432,
                    "db",
                    "user"
                )
                .as_deref(),
                Some(" value ")
            );
        }
        assert_eq!(
            lookup("*:*:*:*:end\\", "host", 5432, "db", "user").as_deref(),
            Some("end\\")
        );
        assert_eq!(
            lookup("*:*:*:*:first:ignored", "host", 5432, "db", "user").as_deref(),
            Some("first")
        );
    }

    #[test]
    fn configured_password_bypasses_all_fallbacks() {
        for value in ["", "  '\"x:y\\z  "] {
            assert_eq!(
                resolve(
                    Some(value),
                    Some("/nonexistent/passwords"),
                    "host",
                    5432,
                    "db",
                    "user"
                )
                .as_deref(),
                Some(value)
            );
        }
    }
}
