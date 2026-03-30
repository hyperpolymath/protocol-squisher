// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Comprehensive interop tests for ReScript analyzer

use protocol_squisher_ir::{ContainerType, IrType, PrimitiveType, TypeDef};
use protocol_squisher_rescript_analyzer::{
    analyze_transport_compatibility, ReScriptAnalyzer, TransportAnalysis,
};
use protocol_squisher_transport_primitives::IRContext;
use std::path::Path;

#[test]
fn test_parse_interop_test_file() {
    let analyzer = ReScriptAnalyzer::new();
    let path = Path::new("tests/interop_test.res");

    let schema = analyzer.analyze_file(path).expect("analyze interop test .res file");

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

    let class = analyze_transport_compatibility(&ctx, &rescript_int, &rust_i64).expect("ReScript int→Rust i64 transport");
    assert_eq!(
        class,
        protocol_squisher_transport_primitives::TransportClass::Concorde
    );

    // ReScript string -> Rust String (Concorde)
    let rescript_string = IrType::Primitive(PrimitiveType::String);
    let rust_string = IrType::Primitive(PrimitiveType::String);

    let class = analyze_transport_compatibility(&ctx, &rescript_string, &rust_string).expect("ReScript string→Rust String transport");
    assert_eq!(
        class,
        protocol_squisher_transport_primitives::TransportClass::Concorde
    );

    // ReScript array<T> -> Rust Vec<T> (Concorde)
    let rescript_array = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
        PrimitiveType::String,
    ))));
    let rust_vec = IrType::Container(ContainerType::Vec(Box::new(IrType::Primitive(
        PrimitiveType::String,
    ))));

    let class = analyze_transport_compatibility(&ctx, &rescript_array, &rust_vec).expect("ReScript array→Rust Vec transport");
    assert_eq!(
        class,
        protocol_squisher_transport_primitives::TransportClass::Concorde
    );
}

#[test]
fn test_rescript_to_julia_interop() {
    let ctx = IRContext::new();

    // ReScript int -> Julia Int64 (Concorde)
    let rescript_int = IrType::Primitive(PrimitiveType::I64);
    let julia_int64 = IrType::Primitive(PrimitiveType::I64);

    let analysis = TransportAnalysis::new(&ctx, &rescript_int, &julia_int64).expect("ReScript int→Julia Int64 transport");
    assert!(analysis.is_zero_copy());
    assert_eq!(analysis.fidelity, 100);

    // ReScript float -> Julia Float64 (Concorde)
    let rescript_float = IrType::Primitive(PrimitiveType::F64);
    let julia_float64 = IrType::Primitive(PrimitiveType::F64);

    let analysis = TransportAnalysis::new(&ctx, &rescript_float, &julia_float64).expect("ReScript float→Julia Float64 transport");
    assert!(analysis.is_zero_copy());
}

#[test]
fn test_rescript_to_gleam_interop() {
    let ctx = IRContext::new();

    // ReScript option<T> -> Gleam Option(T) (Concorde)
    let rescript_option = IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
        PrimitiveType::String,
    ))));
    let gleam_option = IrType::Container(ContainerType::Option(Box::new(IrType::Primitive(
        PrimitiveType::String,
    ))));

    let analysis = TransportAnalysis::new(&ctx, &rescript_option, &gleam_option).expect("ReScript option→Gleam Option transport");
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

    let schema = analyzer.analyze_str(rescript, "user").expect("analyze user with option field");
    let user_type = schema.types.get("user").expect("user type must exist");

    assert!(
        matches!(user_type, TypeDef::Struct(_)),
        "Expected struct type"
    );
    let TypeDef::Struct(struct_def) = user_type else {
        unreachable!("asserted struct");
    };
    let email_field = struct_def
        .fields
        .iter()
        .find(|f| f.name == "email")
        .expect("email field must exist");

    // ReScript option<T> should map to IR Option container
    assert!(
        matches!(
            &email_field.ty,
            IrType::Container(ContainerType::Option(inner))
                if matches!(inner.as_ref(), IrType::Primitive(PrimitiveType::String))
        ),
        "Expected Option<String> type for email field"
    );

    assert!(email_field.optional);
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

    let schema = analyzer.analyze_str(rescript, "status").expect("analyze status variant");
    let status_type = schema.types.get("status").expect("status type must exist");

    assert!(
        matches!(status_type, TypeDef::Enum(_)),
        "Expected enum type"
    );
    let TypeDef::Enum(enum_def) = status_type else {
        unreachable!("asserted enum");
    };
    assert_eq!(enum_def.variants.len(), 3);
    assert_eq!(enum_def.variants[0].name, "Active");
    assert_eq!(enum_def.variants[1].name, "Inactive");
    assert_eq!(enum_def.variants[2].name, "Pending");

    // All should be unit variants (no payload)
    for variant in &enum_def.variants {
        assert!(variant.payload.is_none());
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

    let schema = analyzer.analyze_str(rescript, "result").expect("analyze result variant with payload");
    let result_type = schema.types.get("result").expect("result type must exist");

    assert!(
        matches!(result_type, TypeDef::Enum(_)),
        "Expected enum type"
    );
    let TypeDef::Enum(enum_def) = result_type else {
        unreachable!("asserted enum");
    };
    assert_eq!(enum_def.variants.len(), 2);

    // Both should have payloads
    for variant in &enum_def.variants {
        assert!(variant.payload.is_some());
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

    let schema = analyzer.analyze_str(rescript, "apiUser").expect("analyze apiUser with @as attrs");
    let user_type = schema.types.get("apiUser").expect("apiUser type must exist");

    assert!(
        matches!(user_type, TypeDef::Struct(_)),
        "Expected struct type"
    );
    let TypeDef::Struct(struct_def) = user_type else {
        unreachable!("asserted struct");
    };
    let id_field = struct_def.fields.iter().find(|f| f.name == "id").expect("id field must exist");
    let name_field = struct_def.fields.iter().find(|f| f.name == "name").expect("name field must exist");

    // Check that @as attributes are captured as aliases
    assert_eq!(id_field.metadata.aliases.len(), 1);
    assert_eq!(id_field.metadata.aliases[0], "user_id");

    assert_eq!(name_field.metadata.aliases.len(), 1);
    assert_eq!(name_field.metadata.aliases[0], "user_name");
}

#[test]
fn test_rescript_tuple_interop() {
    let analyzer = ReScriptAnalyzer::new();

    let rescript = r#"
        type coordinates = (float, float, float)
    "#;

    let schema = analyzer.analyze_str(rescript, "coordinates").expect("analyze coordinates tuple");
    let coord_type = schema.types.get("coordinates").expect("coordinates type must exist");

    // Type alias wraps the tuple
    assert!(
        matches!(coord_type, TypeDef::Struct(_)),
        "Expected tuple alias to be represented as struct wrapper"
    );
    let TypeDef::Struct(struct_def) = coord_type else {
        unreachable!("asserted struct");
    };
    let value_field = &struct_def.fields[0];

    assert!(
        matches!(&value_field.ty, IrType::Container(ContainerType::Tuple(_))),
        "Expected tuple type"
    );
    let IrType::Container(ContainerType::Tuple(elements)) = &value_field.ty else {
        unreachable!("asserted tuple");
    };
    assert_eq!(elements.len(), 3);
    for elem in elements {
        assert!(matches!(elem, IrType::Primitive(PrimitiveType::F64)));
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

    let schema = analyzer.analyze_str(rescript, "config").expect("analyze config with Js.Dict");
    let config_type = schema.types.get("config").expect("config type must exist");

    assert!(
        matches!(config_type, TypeDef::Struct(_)),
        "Expected struct type"
    );
    let TypeDef::Struct(struct_def) = config_type else {
        unreachable!("asserted struct");
    };
    let settings_field = struct_def
        .fields
        .iter()
        .find(|f| f.name == "settings")
        .expect("settings field must exist");

    // Js.Dict.t<string> should map to Map<String, String>
    assert!(
        matches!(
            &settings_field.ty,
            IrType::Container(ContainerType::Map(key, value))
                if matches!(key.as_ref(), IrType::Primitive(PrimitiveType::String))
                    && matches!(value.as_ref(), IrType::Primitive(PrimitiveType::String))
        ),
        "Expected Map<String, String> type for settings field"
    );
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

    let schema = analyzer.analyze_str(rescript, "response").expect("analyze polymorphic response");
    let response_type = schema.types.get("response").expect("response type must exist");

    assert!(
        matches!(response_type, TypeDef::Struct(_)),
        "Expected struct type for polymorphic response"
    );
    let TypeDef::Struct(struct_def) = response_type else {
        unreachable!("asserted struct");
    };
    let data_field = struct_def.fields.iter().find(|f| f.name == "data").expect("data field must exist");

    // Type parameter should be captured as a Reference
    assert!(
        matches!(&data_field.ty, IrType::Reference(name) if name == "'data"),
        "Expected Reference type for type parameter"
    );
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

    let schema = analyzer.analyze_str(rescript, "blog").expect("analyze complex nested blog schema");

    // All types should be present
    assert!(schema.types.contains_key("userId"));
    assert!(schema.types.contains_key("status"));
    assert!(schema.types.contains_key("post"));

    // Verify post structure
    let post_type = schema.types.get("post").expect("post type must exist");
    assert!(
        matches!(post_type, TypeDef::Struct(_)),
        "Expected post to be a struct"
    );
    let TypeDef::Struct(struct_def) = post_type else {
        unreachable!("asserted struct");
    };
    assert_eq!(struct_def.fields.len(), 5);

    // Check authorId field references userId
    let author_id = struct_def
        .fields
        .iter()
        .find(|f| f.name == "authorId")
        .expect("authorId field must exist");
    assert!(
        matches!(&author_id.ty, IrType::Reference(name) if name == "userId"),
        "Expected Reference to userId"
    );

    // Check status field references status enum
    let status = struct_def
        .fields
        .iter()
        .find(|f| f.name == "status")
        .expect("status field must exist");
    assert!(
        matches!(&status.ty, IrType::Reference(name) if name == "status"),
        "Expected Reference to status"
    );
}

#[test]
fn test_transport_class_summary() {
    let ctx = IRContext::new();

    // Concorde: Zero-copy, identical types
    let concorde_source = IrType::Primitive(PrimitiveType::I64);
    let concorde_target = IrType::Primitive(PrimitiveType::I64);
    let analysis = TransportAnalysis::new(&ctx, &concorde_source, &concorde_target).expect("Concorde transport analysis");
    assert!(analysis.is_zero_copy());
    assert_eq!(analysis.fidelity, 100);
    assert_eq!(analysis.overhead, 0);

    // Business: Safe widening
    let business_source = IrType::Primitive(PrimitiveType::I32);
    let business_target = IrType::Primitive(PrimitiveType::I64);
    let analysis = TransportAnalysis::new(&ctx, &business_source, &business_target).expect("Business transport analysis");
    assert!(!analysis.is_zero_copy());
    assert!(analysis.is_safe());
    assert_eq!(analysis.fidelity, 98);

    // Wheelbarrow: Incompatible types
    let wheelbarrow_source = IrType::Primitive(PrimitiveType::I64);
    let wheelbarrow_target = IrType::Primitive(PrimitiveType::String);
    let analysis = TransportAnalysis::new(&ctx, &wheelbarrow_source, &wheelbarrow_target).expect("Wheelbarrow transport analysis");
    assert!(analysis.requires_json_fallback());
    assert_eq!(analysis.fidelity, 50);
}
