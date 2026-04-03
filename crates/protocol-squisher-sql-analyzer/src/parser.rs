// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! SQL DDL parser — extracts CREATE TABLE statements from SQL files.
//!
//! This is a pragmatic parser, not a full SQL parser. It handles the
//! subset of DDL that defines data shapes: CREATE TABLE with column
//! definitions, primary keys, NOT NULL, DEFAULT, and foreign keys.
//!
//! Supported dialects: PostgreSQL, MySQL, SQLite (common subset).

use crate::AnalyzerError;

/// A parsed SQL schema — a collection of table definitions.
#[derive(Debug, Clone)]
pub struct SqlSchema {
    /// The schema name (usually the filename).
    pub name: String,
    /// The detected SQL dialect.
    pub dialect: SqlDialect,
    /// All parsed table definitions.
    pub tables: Vec<TableDef>,
}

/// SQL dialect hint (affects type mapping).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SqlDialect {
    /// PostgreSQL-flavoured SQL.
    PostgreSql,
    /// MySQL-flavoured SQL.
    MySql,
    /// SQLite-flavoured SQL.
    Sqlite,
    /// Generic SQL (best-effort type mapping).
    Generic,
}

/// A parsed CREATE TABLE definition.
#[derive(Debug, Clone)]
pub struct TableDef {
    /// Table name.
    pub name: String,
    /// Column definitions.
    pub columns: Vec<ColumnDef>,
    /// Primary key columns (may be composite).
    pub primary_key: Vec<String>,
    /// Foreign key constraints.
    pub foreign_keys: Vec<ForeignKey>,
}

/// A parsed column definition.
#[derive(Debug, Clone)]
pub struct ColumnDef {
    /// Column name.
    pub name: String,
    /// SQL data type (raw string, e.g. "INTEGER", "VARCHAR(255)").
    pub sql_type: String,
    /// Whether the column has NOT NULL constraint.
    pub not_null: bool,
    /// Whether this column is a primary key (from inline PK declaration).
    pub is_primary_key: bool,
    /// Default value expression, if any.
    pub default: Option<String>,
    /// Whether this column has UNIQUE constraint.
    pub is_unique: bool,
}

/// A parsed foreign key constraint.
#[derive(Debug, Clone)]
pub struct ForeignKey {
    /// Local column(s).
    pub columns: Vec<String>,
    /// Referenced table.
    pub ref_table: String,
    /// Referenced column(s).
    pub ref_columns: Vec<String>,
}

/// The SQL DDL parser.
#[derive(Debug, Default)]
pub struct SqlParser;

impl SqlParser {
    /// Parse a SQL file.
    pub fn parse_file(&self, path: &std::path::Path) -> Result<SqlSchema, AnalyzerError> {
        let content = std::fs::read_to_string(path)?;
        let name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("sql");
        self.parse_str(&content, name)
    }

    /// Parse a SQL string.
    pub fn parse_str(&self, content: &str, name: &str) -> Result<SqlSchema, AnalyzerError> {
        let dialect = detect_dialect(content);
        let tables = parse_create_tables(content)?;

        Ok(SqlSchema {
            name: name.to_string(),
            dialect,
            tables,
        })
    }
}

/// Detect SQL dialect from content heuristics.
fn detect_dialect(content: &str) -> SqlDialect {
    let upper = content.to_uppercase();
    if upper.contains("SERIAL") || upper.contains("BIGSERIAL") || upper.contains("TIMESTAMPTZ") {
        SqlDialect::PostgreSql
    } else if upper.contains("AUTO_INCREMENT") || upper.contains("ENGINE=") {
        SqlDialect::MySql
    } else if upper.contains("AUTOINCREMENT") || upper.contains("WITHOUT ROWID") {
        SqlDialect::Sqlite
    } else {
        SqlDialect::Generic
    }
}

/// Parse all CREATE TABLE statements from SQL content.
fn parse_create_tables(content: &str) -> Result<Vec<TableDef>, AnalyzerError> {
    let mut tables = Vec::new();

    // Strip SQL comments
    let cleaned = strip_comments(content);

    // Find CREATE TABLE blocks
    let upper = cleaned.to_uppercase();
    let mut search_from = 0;

    while let Some(create_pos) = upper[search_from..].find("CREATE TABLE") {
        let abs_pos = search_from + create_pos;

        // Find the opening paren
        let Some(paren_start) = cleaned[abs_pos..].find('(') else {
            search_from = abs_pos + 12;
            continue;
        };
        let paren_start = abs_pos + paren_start;

        // Extract table name (between CREATE TABLE and opening paren)
        let name_region = cleaned[abs_pos + 12..paren_start].trim();
        let table_name = extract_table_name(name_region);

        // Find matching closing paren
        let Some(paren_end) = find_matching_paren(&cleaned[paren_start..]) else {
            return Err(AnalyzerError::ParseError(format!(
                "Unmatched parenthesis in CREATE TABLE {}",
                table_name
            )));
        };
        let paren_end = paren_start + paren_end;

        // Parse the column definitions inside the parens
        let body = &cleaned[paren_start + 1..paren_end];
        let table = parse_table_body(&table_name, body)?;
        tables.push(table);

        search_from = paren_end + 1;
    }

    Ok(tables)
}

/// Strip SQL line comments (--) and block comments (/* */).
fn strip_comments(content: &str) -> String {
    let mut result = String::with_capacity(content.len());
    let mut chars = content.chars().peekable();

    while let Some(c) = chars.next() {
        match c {
            '-' if chars.peek() == Some(&'-') => {
                // Line comment — skip to end of line
                for c2 in chars.by_ref() {
                    if c2 == '\n' {
                        result.push('\n');
                        break;
                    }
                }
            }
            '/' if chars.peek() == Some(&'*') => {
                // Block comment — skip to */
                chars.next(); // consume *
                let mut prev = ' ';
                for c2 in chars.by_ref() {
                    if prev == '*' && c2 == '/' {
                        break;
                    }
                    prev = c2;
                }
            }
            '\'' => {
                // String literal — preserve as-is
                result.push(c);
                for c2 in chars.by_ref() {
                    result.push(c2);
                    if c2 == '\'' {
                        break;
                    }
                }
            }
            _ => result.push(c),
        }
    }

    result
}

/// Extract table name, handling IF NOT EXISTS, schema prefix, and quoting.
fn extract_table_name(region: &str) -> String {
    let region = region.trim();
    // Strip IF NOT EXISTS
    let region = if region.to_uppercase().starts_with("IF NOT EXISTS") {
        region[13..].trim()
    } else {
        region
    };

    // Strip schema prefix (e.g., "public.users" → "users")
    let name = if let Some(dot_pos) = region.rfind('.') {
        &region[dot_pos + 1..]
    } else {
        region
    };

    // Strip quotes
    name.trim_matches(|c: char| c == '"' || c == '`' || c == '[' || c == ']')
        .trim()
        .to_string()
}

/// Find the position of the matching closing paren.
fn find_matching_paren(s: &str) -> Option<usize> {
    let mut depth = 0;
    let mut in_string = false;

    for (i, c) in s.char_indices() {
        if in_string {
            if c == '\'' {
                in_string = false;
            }
            continue;
        }
        match c {
            '\'' => in_string = true,
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Parse the body of a CREATE TABLE (inside the parentheses).
fn parse_table_body(table_name: &str, body: &str) -> Result<TableDef, AnalyzerError> {
    let mut columns = Vec::new();
    let mut primary_key = Vec::new();
    let mut foreign_keys = Vec::new();

    // Split on commas, respecting parenthesised sub-expressions
    let parts = split_top_level_commas(body);

    for part in &parts {
        let trimmed = part.trim();
        if trimmed.is_empty() {
            continue;
        }

        let upper = trimmed.to_uppercase();

        // Table-level constraints
        if upper.starts_with("PRIMARY KEY") {
            if let Some(cols) = extract_paren_list(trimmed) {
                primary_key = cols;
            }
        } else if upper.starts_with("FOREIGN KEY") {
            if let Some(fk) = parse_foreign_key(trimmed) {
                foreign_keys.push(fk);
            }
        } else if upper.starts_with("CONSTRAINT")
            || upper.starts_with("UNIQUE")
            || upper.starts_with("CHECK")
            || upper.starts_with("INDEX")
        {
            // Table-level constraint — check for embedded PRIMARY KEY
            if upper.contains("PRIMARY KEY") {
                if let Some(cols) = extract_paren_list(trimmed) {
                    primary_key = cols;
                }
            }
            // Skip other table-level constraints for now
        } else {
            // Column definition
            if let Some(col) = parse_column_def(trimmed) {
                if col.is_primary_key {
                    primary_key.push(col.name.clone());
                }
                columns.push(col);
            }
        }
    }

    Ok(TableDef {
        name: table_name.to_string(),
        columns,
        primary_key,
        foreign_keys,
    })
}

/// Split a string on commas, but not inside parentheses.
fn split_top_level_commas(s: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth = 0;
    let mut in_string = false;

    for c in s.chars() {
        if in_string {
            current.push(c);
            if c == '\'' {
                in_string = false;
            }
            continue;
        }
        match c {
            '\'' => {
                in_string = true;
                current.push(c);
            }
            '(' => {
                depth += 1;
                current.push(c);
            }
            ')' => {
                depth -= 1;
                current.push(c);
            }
            ',' if depth == 0 => {
                parts.push(current.clone());
                current.clear();
            }
            _ => current.push(c),
        }
    }

    if !current.trim().is_empty() {
        parts.push(current);
    }
    parts
}

/// Extract a parenthesised comma-separated list of names.
fn extract_paren_list(s: &str) -> Option<Vec<String>> {
    let start = s.find('(')?;
    let end = s[start..].find(')')? + start;
    let inner = &s[start + 1..end];
    Some(
        inner
            .split(',')
            .map(|c| {
                c.trim()
                    .trim_matches(|c: char| c == '"' || c == '`' || c == '[' || c == ']')
                    .to_string()
            })
            .filter(|s| !s.is_empty())
            .collect(),
    )
}

/// Parse a FOREIGN KEY constraint.
fn parse_foreign_key(s: &str) -> Option<ForeignKey> {
    let upper = s.to_uppercase();
    let fk_pos = upper.find("FOREIGN KEY")?;
    let ref_pos = upper.find("REFERENCES")?;

    let local_region = &s[fk_pos + 11..ref_pos];
    let ref_region = &s[ref_pos + 10..];

    let columns = extract_paren_list(local_region)?;

    // Parse "table_name(col1, col2)" from references region
    let ref_trimmed = ref_region.trim();
    let paren_pos = ref_trimmed.find('(')?;
    let ref_table = ref_trimmed[..paren_pos]
        .trim()
        .trim_matches(|c: char| c == '"' || c == '`')
        .to_string();
    let ref_columns = extract_paren_list(ref_trimmed)?;

    Some(ForeignKey {
        columns,
        ref_table,
        ref_columns,
    })
}

/// Parse a single column definition.
fn parse_column_def(s: &str) -> Option<ColumnDef> {
    let tokens = tokenize_column(s);
    if tokens.len() < 2 {
        return None;
    }

    let name = tokens[0]
        .trim_matches(|c: char| c == '"' || c == '`' || c == '[' || c == ']')
        .to_string();

    // Skip if this looks like a keyword, not a column name
    let upper_name = name.to_uppercase();
    if matches!(
        upper_name.as_str(),
        "PRIMARY" | "FOREIGN" | "UNIQUE" | "CHECK" | "CONSTRAINT" | "INDEX"
    ) {
        return None;
    }

    let sql_type = tokens[1].to_uppercase();

    // Handle types with size specifier: VARCHAR(255), DECIMAL(10,2), etc.
    let sql_type = if tokens.len() > 2 && tokens[2].starts_with('(') {
        format!("{}{}", sql_type, tokens[2])
    } else {
        sql_type
    };

    let upper_rest: String = tokens[2..].iter().map(|t| t.to_uppercase()).collect::<Vec<_>>().join(" ");

    let not_null = upper_rest.contains("NOT NULL");
    let is_primary_key = upper_rest.contains("PRIMARY KEY");
    let is_unique = upper_rest.contains("UNIQUE");

    let default = if let Some(pos) = upper_rest.find("DEFAULT") {
        let rest_tokens: Vec<&str> = upper_rest[pos + 7..].trim().splitn(2, ' ').collect();
        rest_tokens.first().map(|s| s.to_string())
    } else {
        None
    };

    Some(ColumnDef {
        name,
        sql_type,
        not_null,
        is_primary_key,
        default,
        is_unique,
    })
}

/// Tokenize a column definition, keeping parenthesised groups and quoted
/// identifiers together.
fn tokenize_column(s: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut depth = 0;
    let mut in_string = false;
    let mut in_dquote = false;

    for c in s.chars() {
        if in_string {
            current.push(c);
            if c == '\'' {
                in_string = false;
            }
            continue;
        }
        if in_dquote {
            current.push(c);
            if c == '"' {
                in_dquote = false;
            }
            continue;
        }
        match c {
            '\'' => {
                in_string = true;
                current.push(c);
            }
            '"' => {
                in_dquote = true;
                current.push(c);
            }
            '(' => {
                if depth == 0 && !current.is_empty() {
                    tokens.push(current.clone());
                    current.clear();
                }
                depth += 1;
                current.push(c);
            }
            ')' => {
                depth -= 1;
                current.push(c);
                if depth == 0 {
                    tokens.push(current.clone());
                    current.clear();
                }
            }
            c if c.is_whitespace() && depth == 0 => {
                if !current.is_empty() {
                    tokens.push(current.clone());
                    current.clear();
                }
            }
            _ => current.push(c),
        }
    }

    if !current.is_empty() {
        tokens.push(current);
    }
    tokens
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_simple_table() {
        let sql = "CREATE TABLE users (
            id INTEGER PRIMARY KEY,
            name VARCHAR(255) NOT NULL,
            email TEXT
        );";
        let parser = SqlParser;
        let schema = parser.parse_str(sql, "test").expect("parsing should succeed");
        assert_eq!(schema.tables.len(), 1);
        assert_eq!(schema.tables[0].name, "users");
        assert_eq!(schema.tables[0].columns.len(), 3);
        assert!(schema.tables[0].primary_key.contains(&"id".to_string()));
    }

    #[test]
    fn parse_not_null_and_default() {
        let sql = "CREATE TABLE settings (
            key TEXT NOT NULL,
            value TEXT DEFAULT 'empty',
            active BOOLEAN NOT NULL DEFAULT TRUE
        );";
        let parser = SqlParser;
        let schema = parser.parse_str(sql, "test").expect("parsing should succeed");
        let cols = &schema.tables[0].columns;
        assert!(cols[0].not_null);
        assert!(!cols[1].not_null);
        assert!(cols[1].default.is_some());
        assert!(cols[2].not_null);
    }

    #[test]
    fn parse_table_level_pk() {
        let sql = "CREATE TABLE orders (
            order_id INTEGER NOT NULL,
            product_id INTEGER NOT NULL,
            quantity INTEGER,
            PRIMARY KEY (order_id, product_id)
        );";
        let parser = SqlParser;
        let schema = parser.parse_str(sql, "test").expect("parsing should succeed");
        assert_eq!(schema.tables[0].primary_key.len(), 2);
    }

    #[test]
    fn parse_foreign_key() {
        let sql = "CREATE TABLE orders (
            id INTEGER PRIMARY KEY,
            user_id INTEGER NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id)
        );";
        let parser = SqlParser;
        let schema = parser.parse_str(sql, "test").expect("parsing should succeed");
        assert_eq!(schema.tables[0].foreign_keys.len(), 1);
        assert_eq!(schema.tables[0].foreign_keys[0].ref_table, "users");
    }

    #[test]
    fn parse_multiple_tables() {
        let sql = "
            CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT);
            CREATE TABLE posts (id INTEGER PRIMARY KEY, user_id INTEGER, body TEXT);
        ";
        let parser = SqlParser;
        let schema = parser.parse_str(sql, "test").expect("parsing should succeed");
        assert_eq!(schema.tables.len(), 2);
    }

    #[test]
    fn strip_sql_comments() {
        let sql = "
            -- This is a comment
            CREATE TABLE test (
                id INTEGER /* inline comment */ PRIMARY KEY,
                name TEXT -- trailing comment
            );
        ";
        let parser = SqlParser;
        let schema = parser.parse_str(sql, "test").expect("parsing should succeed");
        assert_eq!(schema.tables[0].columns.len(), 2);
    }

    #[test]
    fn detect_postgres_dialect() {
        let sql = "CREATE TABLE users (id SERIAL PRIMARY KEY, name TEXT);";
        let parser = SqlParser;
        let schema = parser.parse_str(sql, "test").expect("parsing should succeed");
        assert_eq!(schema.dialect, SqlDialect::PostgreSql);
    }

    #[test]
    fn detect_mysql_dialect() {
        let sql = "CREATE TABLE users (id INT AUTO_INCREMENT PRIMARY KEY, name VARCHAR(255));";
        let parser = SqlParser;
        let schema = parser.parse_str(sql, "test").expect("parsing should succeed");
        assert_eq!(schema.dialect, SqlDialect::MySql);
    }

    #[test]
    fn handle_if_not_exists() {
        let sql = "CREATE TABLE IF NOT EXISTS users (id INTEGER PRIMARY KEY);";
        let parser = SqlParser;
        let schema = parser.parse_str(sql, "test").expect("parsing should succeed");
        assert_eq!(schema.tables[0].name, "users");
    }

    #[test]
    fn handle_quoted_names() {
        let sql = r#"CREATE TABLE "public"."user_accounts" ("id" INTEGER PRIMARY KEY, "full name" TEXT);"#;
        let parser = SqlParser;
        let schema = parser.parse_str(sql, "test").expect("parsing should succeed");
        assert_eq!(schema.tables[0].name, "user_accounts");
        assert_eq!(schema.tables[0].columns[1].name, "full name");
    }
}
