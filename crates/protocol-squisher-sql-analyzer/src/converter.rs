// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! SQL DDL → Protocol Squisher IR converter.
//!
//! Maps SQL column types to IR types and table definitions to struct types.
//!
//! ## Type Mappings
//!
//! | SQL Type                 | IR Type       | Notes                           |
//! |--------------------------|---------------|---------------------------------|
//! | INTEGER, INT, SMALLINT   | I32 / I16     | Width-dependent                 |
//! | BIGINT, BIGSERIAL        | I64           | 64-bit integer                  |
//! | SERIAL                   | I32           | PostgreSQL auto-increment       |
//! | REAL, FLOAT              | F32           | Single precision                |
//! | DOUBLE, DOUBLE PRECISION | F64           | Double precision                |
//! | DECIMAL, NUMERIC         | Decimal       | Arbitrary precision             |
//! | BOOLEAN, BOOL            | Bool          | Boolean                         |
//! | TEXT, VARCHAR, CHAR       | String        | Text types                      |
//! | BYTEA, BLOB, BINARY      | Bytes         | Binary data                     |
//! | DATE                     | Date          | Calendar date                   |
//! | TIME, TIMETZ             | Duration      | Time of day                     |
//! | TIMESTAMP, TIMESTAMPTZ   | DateTime      | Date + time                     |
//! | UUID                     | Uuid          | 128-bit identifier              |
//! | JSON, JSONB              | Special(Json) | JSON document                   |

use crate::parser::{ColumnDef, SqlDialect, SqlSchema, TableDef};
use crate::AnalyzerError;
use protocol_squisher_ir::*;

/// The SQL → IR converter.
#[derive(Debug, Default)]
pub struct SqlConverter;

impl SqlConverter {
    /// Convert a parsed SQL schema to an IR schema.
    pub fn convert(&self, parsed: &SqlSchema) -> Result<IrSchema, AnalyzerError> {
        let mut schema = IrSchema::new(&parsed.name, dialect_format_name(parsed.dialect));

        for table in &parsed.tables {
            let type_def = self.convert_table(table)?;
            schema.add_type(table.name.clone(), type_def);
            schema.add_root(table.name.clone());
        }

        Ok(schema)
    }

    /// Convert a single table definition to an IR struct.
    fn convert_table(&self, table: &TableDef) -> Result<TypeDef, AnalyzerError> {
        let fields: Vec<FieldDef> = table
            .columns
            .iter()
            .map(|col| self.convert_column(col, &table.primary_key))
            .collect::<Result<Vec<_>, _>>()?;

        let mut metadata = TypeMetadata::default();
        if !table.primary_key.is_empty() {
            metadata
                .extra
                .insert("primary_key".into(), table.primary_key.join(","));
        }
        if !table.foreign_keys.is_empty() {
            let fk_strs: Vec<String> = table
                .foreign_keys
                .iter()
                .map(|fk| {
                    format!(
                        "{}({}) -> {}({})",
                        table.name,
                        fk.columns.join(","),
                        fk.ref_table,
                        fk.ref_columns.join(","),
                    )
                })
                .collect();
            metadata
                .extra
                .insert("foreign_keys".into(), fk_strs.join(";"));
        }

        Ok(TypeDef::Struct(StructDef {
            name: table.name.clone(),
            fields,
            metadata,
        }))
    }

    /// Convert a single column to an IR field.
    fn convert_column(
        &self,
        col: &ColumnDef,
        primary_key: &[String],
    ) -> Result<FieldDef, AnalyzerError> {
        let base_type = convert_sql_type(&col.sql_type)?;
        let is_pk = col.is_primary_key || primary_key.contains(&col.name);

        // Nullable columns (no NOT NULL) become Optional, unless they are PK
        let ty = if !col.not_null && !is_pk {
            IrType::Container(ContainerType::Option(Box::new(base_type)))
        } else {
            base_type
        };

        let mut constraints = Vec::new();
        if col.is_unique || is_pk {
            constraints.push(Constraint::UniqueItems);
        }
        if col.not_null {
            constraints.push(Constraint::NonEmpty);
        }

        Ok(FieldDef {
            name: col.name.clone(),
            ty,
            optional: !col.not_null && !is_pk,
            constraints,
            metadata: FieldMetadata::default(),
        })
    }
}

/// Map a SQL type string to an IR type.
fn convert_sql_type(sql_type: &str) -> Result<IrType, AnalyzerError> {
    // Normalise: uppercase, strip leading/trailing whitespace
    let upper = sql_type.to_uppercase();
    let upper = upper.trim();

    // Strip size specifiers for matching: "VARCHAR(255)" → "VARCHAR"
    let base = if let Some(paren_pos) = upper.find('(') {
        upper[..paren_pos].trim()
    } else {
        upper
    };

    let ir_type = match base {
        // Integer types
        "INT" | "INTEGER" | "INT4" | "MEDIUMINT" => IrType::Primitive(PrimitiveType::I32),
        "SMALLINT" | "INT2" | "TINYINT" => IrType::Primitive(PrimitiveType::I16),
        "BIGINT" | "INT8" => IrType::Primitive(PrimitiveType::I64),
        "SERIAL" | "SERIAL4" => IrType::Primitive(PrimitiveType::I32),
        "BIGSERIAL" | "SERIAL8" => IrType::Primitive(PrimitiveType::I64),
        "SMALLSERIAL" | "SERIAL2" => IrType::Primitive(PrimitiveType::I16),

        // Floating point
        "REAL" | "FLOAT" | "FLOAT4" => IrType::Primitive(PrimitiveType::F32),
        "DOUBLE" | "DOUBLE PRECISION" | "FLOAT8" => IrType::Primitive(PrimitiveType::F64),

        // Decimal / numeric
        "DECIMAL" | "NUMERIC" | "MONEY" => IrType::Primitive(PrimitiveType::Decimal),

        // Boolean
        "BOOLEAN" | "BOOL" => IrType::Primitive(PrimitiveType::Bool),

        // Text
        "TEXT" | "VARCHAR" | "CHARACTER VARYING" | "CHAR" | "CHARACTER" | "NCHAR" | "NVARCHAR"
        | "CLOB" | "TINYTEXT" | "MEDIUMTEXT" | "LONGTEXT" | "ENUM" | "SET" => {
            IrType::Primitive(PrimitiveType::String)
        }

        // Binary
        "BYTEA" | "BLOB" | "BINARY" | "VARBINARY" | "TINYBLOB" | "MEDIUMBLOB" | "LONGBLOB"
        | "BIT" => IrType::Primitive(PrimitiveType::Bytes),

        // Date/time
        "DATE" => IrType::Primitive(PrimitiveType::Date),
        "TIME" | "TIMETZ" | "TIME WITH TIME ZONE" | "TIME WITHOUT TIME ZONE" => {
            IrType::Primitive(PrimitiveType::Time)
        }
        "TIMESTAMP" | "TIMESTAMPTZ" | "TIMESTAMP WITH TIME ZONE"
        | "TIMESTAMP WITHOUT TIME ZONE" | "DATETIME" => {
            IrType::Primitive(PrimitiveType::DateTime)
        }
        "INTERVAL" => IrType::Primitive(PrimitiveType::Duration),

        // UUID
        "UUID" => IrType::Primitive(PrimitiveType::Uuid),

        // JSON
        "JSON" | "JSONB" => IrType::Special(SpecialType::Json),

        // Arrays (PostgreSQL style)
        _ if base.ends_with("[]") => {
            let inner_type = convert_sql_type(&base[..base.len() - 2])?;
            IrType::Container(ContainerType::Vec(Box::new(inner_type)))
        }

        // Fallback
        _ => {
            // Try to handle "ARRAY" suffix or unknown types as String
            IrType::Primitive(PrimitiveType::String)
        }
    };

    Ok(ir_type)
}

/// Get the format name for a dialect.
fn dialect_format_name(dialect: SqlDialect) -> &'static str {
    match dialect {
        SqlDialect::PostgreSql => "sql-postgresql",
        SqlDialect::MySql => "sql-mysql",
        SqlDialect::Sqlite => "sql-sqlite",
        SqlDialect::Generic => "sql",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::SqlParser;

    fn convert(sql: &str) -> IrSchema {
        let parser = SqlParser;
        let parsed = parser.parse_str(sql, "test").unwrap();
        SqlConverter.convert(&parsed).unwrap()
    }

    #[test]
    fn basic_type_mapping() {
        let schema = convert(
            "CREATE TABLE t (
                a INTEGER NOT NULL,
                b TEXT,
                c BOOLEAN NOT NULL,
                d REAL NOT NULL
            );",
        );
        let td = &schema.types["t"];
        match td {
            TypeDef::Struct(s) => {
                assert_eq!(s.fields.len(), 4);
                assert!(matches!(
                    s.fields[0].ty,
                    IrType::Primitive(PrimitiveType::I32)
                ));
                // b is nullable → Optional<String>
                assert!(matches!(
                    s.fields[1].ty,
                    IrType::Container(ContainerType::Option(_))
                ));
                assert!(matches!(
                    s.fields[2].ty,
                    IrType::Primitive(PrimitiveType::Bool)
                ));
                assert!(matches!(
                    s.fields[3].ty,
                    IrType::Primitive(PrimitiveType::F32)
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn postgres_types() {
        let schema = convert(
            "CREATE TABLE pg (
                id BIGSERIAL NOT NULL,
                data JSONB,
                created_at TIMESTAMPTZ NOT NULL,
                tags TEXT[] NOT NULL,
                uid UUID NOT NULL
            );",
        );
        match &schema.types["pg"] {
            TypeDef::Struct(s) => {
                assert!(matches!(
                    s.fields[0].ty,
                    IrType::Primitive(PrimitiveType::I64)
                ));
                assert!(matches!(
                    s.fields[1].ty,
                    IrType::Container(ContainerType::Option(_))
                ));
                assert!(matches!(
                    s.fields[2].ty,
                    IrType::Primitive(PrimitiveType::DateTime)
                ));
                assert!(matches!(
                    s.fields[3].ty,
                    IrType::Container(ContainerType::Vec(_))
                ));
                assert!(matches!(
                    s.fields[4].ty,
                    IrType::Primitive(PrimitiveType::Uuid)
                ));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn nullable_columns_are_optional() {
        let schema = convert(
            "CREATE TABLE t (
                required_col TEXT NOT NULL,
                nullable_col TEXT
            );",
        );
        match &schema.types["t"] {
            TypeDef::Struct(s) => {
                assert!(!s.fields[0].optional);
                assert!(s.fields[1].optional);
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn primary_key_is_not_optional() {
        let schema = convert("CREATE TABLE t (id INTEGER PRIMARY KEY, name TEXT);");
        match &schema.types["t"] {
            TypeDef::Struct(s) => {
                // id is PK → not optional even without NOT NULL
                assert!(!s.fields[0].optional);
                // name has no NOT NULL → optional
                assert!(s.fields[1].optional);
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn primary_key_metadata() {
        let schema = convert("CREATE TABLE t (id INTEGER PRIMARY KEY, name TEXT NOT NULL);");
        match &schema.types["t"] {
            TypeDef::Struct(s) => {
                assert_eq!(s.metadata.extra.get("primary_key").unwrap(), "id");
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn foreign_key_metadata() {
        let schema = convert(
            "CREATE TABLE orders (
                id INTEGER PRIMARY KEY,
                user_id INTEGER NOT NULL,
                FOREIGN KEY (user_id) REFERENCES users(id)
            );",
        );
        match &schema.types["orders"] {
            TypeDef::Struct(s) => {
                let fk = s.metadata.extra.get("foreign_keys").unwrap();
                assert!(fk.contains("users"));
            }
            other => panic!("Expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn multiple_tables_produce_multiple_types() {
        let schema = convert(
            "CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT NOT NULL);
             CREATE TABLE posts (id INTEGER PRIMARY KEY, body TEXT NOT NULL);",
        );
        assert_eq!(schema.types.len(), 2);
        assert!(schema.types.contains_key("users"));
        assert!(schema.types.contains_key("posts"));
        assert_eq!(schema.roots.len(), 2);
    }

    #[test]
    fn schema_format_reflects_dialect() {
        let schema = convert("CREATE TABLE t (id SERIAL PRIMARY KEY);");
        assert_eq!(schema.source_format, "sql-postgresql");
    }
}
