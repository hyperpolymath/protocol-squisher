// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Comprehensive interop tests for ReScript analyzer

use protocol_squisher_ephapax_ir::IRContext;
use protocol_squisher_rescript_analyzer::{analyze_transport_compatibility, ReScriptAnalyzer, TransportAnalysis};
use protocol_squisher_ir::{IrType, PrimitiveType, ContainerType};
use std::path::Path;

#[test]
fn test_parse_interop_test_file() {
    let analyzer = ReScriptAnalyzer::new();
    let path = Path::new("tests/interop_test.res");

    let result = analyzer.analyze_file(path);
    assert!(result.is_ok());

    let schema = result.unwrap();

    // Verify all types were parsed
    assert!(schema.types.contains_key("user"));
    assert!(schema.types.contains_key("profile"));
    assert!(schema.types.contains_key("userStatus"));
    assert!(schema.types.contains_key("result"));
    assert!(schema.types.contains_key("address"));
    assert!(schema.types.contains_key("person"));
    assert!(schema.types.contains_key("apiUser"));
    assert!(schema.types.contains_key("coordinates"));
    assert!(schema.types.contains_key("config"));
    assert!(schema.types.contains_key("response"));
    assert!(schema.types.contains_key("userId"));
    assert!(schema.types.contains_key("timestamp"));
    assert!(schema.types.contains_key("post"));
}

#[test]
fn test_rescript_to_rust_interop() {
    let ctx = IRContext::new();

    // ReScript int -> Rust i64 (Concorde)
    let rescript_int = IrType::Primitive(PrimitiveType::I64);
    let rust_i64 = IrType::Primitive(PrimitiveType::I64);

    let class = analyze_transport_compatibility(&ctx, &rescript_int, &rust_i64).unwrap();
    assert_eq!(class, protocol_squisher_ephapax_ir::TransportClass::Concorde);

    // ReScript string -> Rust String (Concorde)
    let rescript_string = IrType::Primitive(PrimitiveType::String);
    let rust_string = IrType::Primitive(PrimitiveType::String);

    let class = analyze_transport_compatibility(&ctx, &rescript_string, &rust_string).unwrap();
    assert_eq!(class, protocol_squisher_ephapax_ir::TransportClass::Concorde);

    // ReScript array<T> -> Rust Vec<T> (Concorde)
    let rescript_array = IrType::Container(ContainerType::Vec(Box::new(
        IrType::Primitive(PrimitiveType::String)
    )));
    let rust_vec = IrType::Container(ContainerType::Vec(Box::new(
        IrType::Primitive(PrimitiveType::String)
    )));

    let class = analyze_transport_compatibility(&ctx, &rescript_array, &rust_vec).unwrap();
    assert_eq!(class, protocol_squisher_ephapax_ir::TransportClass::Concorde);
}

#[test]
fn test_rescript_to_julia_interop() {
    let ctx = IRContext::new();

    // ReScript int -> Julia Int64 (Concorde)
    let rescript_int = IrType::Primitive(PrimitiveType::I64);
    let julia_int64 = IrType::Primitive(PrimitiveType::I64);

    let analysis = TransportAnalysis::new(&ctx, &rescript_int, &julia_int64).unwrap();
    assert!(analysis.is_zero_copy());
    assert_eq!(analysis.fidelity, 100);

    // ReScript float -> Julia Float64 (Concorde)
    let rescript_float = IrType::Primitive(PrimitiveType::F64);
    let julia_float64 = IrType::Primitive(PrimitiveType::F64);

    let analysis = TransportAnalysis::new(&ctx, &rescript_float, &julia_float64).unwrap();
    assert!(analysis.is_zero_copy());
}

#[test]
fn test_rescript_to_gleam_interop() {
    let ctx = IRContext::new();

    // ReScript option<T> -> Gleam Option(T) (Concorde)
    let rescript_option = IrType::Container(ContainerType::Option(Box::new(
        IrType::Primitive(PrimitiveType::String)
    )));
    let gleam_option = IrType::Container(ContainerType::Option(Box::new(
        IrType::Primitive(PrimitiveType::String)
    )));

    let analysis = TransportAnalysis::new(&ctx, &rescript_option, &gleam_option).unwrap();
    assert!(analysis.is_zero_copy());
}

#[test]
fn test_rescript_option_semantics() {
    let analyzer = ReScriptAnalyzer::new();

    let rescript = r#"
        type user = {
            id: int,
            name: string,
            email: option<string>,
        }
    "#;

    let schema = analyzer.analyze_str(rescript, "user").unwrap();
    let user_type = schema.types.get("user").unwrap();

    if let protocol_squisher_ir::TypeDef::Struct(struct_def) = user_type {
        let email_field = struct_def.fields.iter().find(|f| f.name == "email").unwrap();

        // ReScript option<T> should map to IR Option container
        match &email_field.ty {
            IrType::Container(ContainerType::Option(inner)) => {
                assert!(matches!(**inner, IrType::Primitive(PrimitiveType::String)));
            }
            _ => panic!("Expected Option type for email field"),
        }

        assert!(email_field.optional);
    } else {
        panic!("Expected struct type");
    }
}

#[test]
fn test_rescript_variant_to_rust_enum() {
    let analyzer = ReScriptAnalyzer::new();

    let rescript = r#"
        type status =
          | Active
          | Inactive
          | Pending
    "#;

    let schema = analyzer.analyze_str(rescript, "status").unwrap();
    let status_type = schema.types.get("status").unwrap();

    if let protocol_squisher_ir::TypeDef::Enum(enum_def) = status_type {
        assert_eq!(enum_def.variants.len(), 3);
        assert_eq!(enum_def.variants[0].name, "Active");
        assert_eq!(enum_def.variants[1].name, "Inactive");
        assert_eq!(enum_def.variants[2].name, "Pending");

        // All should be unit variants (no payload)
        for variant in &enum_def.variants {
            assert!(variant.payload.is_none());
        }
    } else {
        panic!("Expected enum type");
    }
}

#[test]
fn test_rescript_variant_with_payload() {
    let analyzer = ReScriptAnalyzer::new();

    let rescript = r#"
        type result<'a, 'e> =
          | Ok('a)
          | Error('e)
    "#;

    let schema = analyzer.analyze_str(rescript, "result").unwrap();
    let result_type = schema.types.get("result").unwrap();

    if let protocol_squisher_ir::TypeDef::Enum(enum_def) = result_type {
        assert_eq!(enum_def.variants.len(), 2);

        // Both should have payloads
        for variant in &enum_def.variants {
            assert!(variant.payload.is_some());
        }
    } else {
        panic!("Expected enum type");
    }
}

#[test]
fn test_rescript_js_interop_attributes() {
    let analyzer = ReScriptAnalyzer::new();

    let rescript = r#"
        type apiUser = {
            @as("user_id") id: int,
            @as("user_name") name: string,
        }
    "#;

    let schema = analyzer.analyze_str(rescript, "apiUser").unwrap();
    let user_type = schema.types.get("apiUser").unwrap();

    if let protocol_squisher_ir::TypeDef::Struct(struct_def) = user_type {
        let id_field = struct_def.fields.iter().find(|f| f.name == "id").unwrap();
        let name_field = struct_def.fields.iter().find(|f| f.name == "name").unwrap();

        // Check that @as attributes are captured as aliases
        assert_eq!(id_field.metadata.aliases.len(), 1);
        assert_eq!(id_field.metadata.aliases[0], "user_id");

        assert_eq!(name_field.metadata.aliases.len(), 1);
        assert_eq!(name_field.metadata.aliases[0], "user_name");
    } else {
        panic!("Expected struct type");
    }
}

#[test]
fn test_rescript_tuple_interop() {
    let analyzer = ReScriptAnalyzer::new();

    let rescript = r#"
        type coordinates = (float, float, float)
    "#;

    let schema = analyzer.analyze_str(rescript, "coordinates").unwrap();
    let coord_type = schema.types.get("coordinates").unwrap();

    // Type alias wraps the tuple
    if let protocol_squisher_ir::TypeDef::Struct(struct_def) = coord_type {
        let value_field = &struct_def.fields[0];

        if let IrType::Container(ContainerType::Tuple(elements)) = &value_field.ty {
            assert_eq!(elements.len(), 3);
            for elem in elements {
                assert!(matches!(elem, IrType::Primitive(PrimitiveType::F64)));
            }
        } else {
            panic!("Expected tuple type");
        }
    }
}

#[test]
fn test_rescript_js_dict_interop() {
    let analyzer = ReScriptAnalyzer::new();

    let rescript = r#"
        type config = {
            name: string,
            settings: Js.Dict.t<string>,
        }
    "#;

    let schema = analyzer.analyze_str(rescript, "config").unwrap();
    let config_type = schema.types.get("config").unwrap();

    if let protocol_squisher_ir::TypeDef::Struct(struct_def) = config_type {
        let settings_field = struct_def.fields.iter().find(|f| f.name == "settings").unwrap();

        // Js.Dict.t<string> should map to Map<String, String>
        match &settings_field.ty {
            IrType::Container(ContainerType::Map(key, value)) => {
                assert!(matches!(**key, IrType::Primitive(PrimitiveType::String)));
                assert!(matches!(**value, IrType::Primitive(PrimitiveType::String)));
            }
            _ => panic!("Expected Map type for settings field"),
        }
    } else {
        panic!("Expected struct type");
    }
}

#[test]
fn test_rescript_polymorphic_type() {
    let analyzer = ReScriptAnalyzer::new();

    let rescript = r#"
        type response<'data> = {
            status: int,
            data: 'data,
        }
    "#;

    let schema = analyzer.analyze_str(rescript, "response").unwrap();
    let response_type = schema.types.get("response").unwrap();

    if let protocol_squisher_ir::TypeDef::Struct(struct_def) = response_type {
        let data_field = struct_def.fields.iter().find(|f| f.name == "data").unwrap();

        // Type parameter should be captured as a Reference
        match &data_field.ty {
            IrType::Reference(name) => {
                assert_eq!(name, "'data");
            }
            _ => panic!("Expected Reference type for type parameter"),
        }
    } else {
        panic!("Expected struct type");
    }
}

#[test]
fn test_complex_nested_structure() {
    let analyzer = ReScriptAnalyzer::new();

    let rescript = r#"
        type userId = int

        type status =
          | Active
          | Inactive

        type post = {
            id: int,
            authorId: userId,
            title: string,
            tags: array<string>,
            status: status,
        }
    "#;

    let schema = analyzer.analyze_str(rescript, "blog").unwrap();

    // All types should be present
    assert!(schema.types.contains_key("userId"));
    assert!(schema.types.contains_key("status"));
    assert!(schema.types.contains_key("post"));

    // Verify post structure
    let post_type = schema.types.get("post").unwrap();
    if let protocol_squisher_ir::TypeDef::Struct(struct_def) = post_type {
        assert_eq!(struct_def.fields.len(), 5);

        // Check authorId field references userId
        let author_id = struct_def.fields.iter().find(|f| f.name == "authorId").unwrap();
        match &author_id.ty {
            IrType::Reference(name) => assert_eq!(name, "userId"),
            _ => panic!("Expected Reference to userId"),
        }

        // Check status field references status enum
        let status = struct_def.fields.iter().find(|f| f.name == "status").unwrap();
        match &status.ty {
            IrType::Reference(name) => assert_eq!(name, "status"),
            _ => panic!("Expected Reference to status"),
        }
    }
}

#[test]
fn test_transport_class_summary() {
    let ctx = IRContext::new();

    // Concorde: Zero-copy, identical types
    let concorde_source = IrType::Primitive(PrimitiveType::I64);
    let concorde_target = IrType::Primitive(PrimitiveType::I64);
    let analysis = TransportAnalysis::new(&ctx, &concorde_source, &concorde_target).unwrap();
    assert!(analysis.is_zero_copy());
    assert_eq!(analysis.fidelity, 100);
    assert_eq!(analysis.overhead, 0);

    // Business: Safe widening
    let business_source = IrType::Primitive(PrimitiveType::I32);
    let business_target = IrType::Primitive(PrimitiveType::I64);
    let analysis = TransportAnalysis::new(&ctx, &business_source, &business_target).unwrap();
    assert!(!analysis.is_zero_copy());
    assert!(analysis.is_safe());
    assert_eq!(analysis.fidelity, 98);

    // Wheelbarrow: Incompatible types
    let wheelbarrow_source = IrType::Primitive(PrimitiveType::I64);
    let wheelbarrow_target = IrType::Primitive(PrimitiveType::String);
    let analysis = TransportAnalysis::new(&ctx, &wheelbarrow_source, &wheelbarrow_target).unwrap();
    assert!(analysis.requires_json_fallback());
    assert_eq!(analysis.fidelity, 50);
}
