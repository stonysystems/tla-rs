//! Code generation for ProtocolMessage implementations.
//!
//! Generates:
//! - Message enum definition with named-field variants
//! - Tag constants for serialization
//! - `impl ProtocolMessage` with `serialize_to_bytes` and `deserialize_from_bytes`
//! - `read_u64` helper function

use crate::config::MessageConfig;

/// Generate a complete message.rs file from a MessageConfig.
///
/// Returns the generated Rust source code as a string.
pub fn generate_message_code(config: &MessageConfig) -> String {
    let mut out = String::new();

    // Module doc comment
    if !config.doc_comment.is_empty() {
        for line in config.doc_comment.lines() {
            out.push_str(&format!("//! {}\n", line));
        }
        out.push('\n');
    }

    // Import
    out.push_str(&format!("use {};\n\n", config.import_path));

    // Enum definition
    generate_enum_def(&mut out, config);

    // Tag constants
    generate_tag_constants(&mut out, config);

    // read_u64 helper
    generate_read_u64_helper(&mut out);

    // ProtocolMessage impl
    generate_protocol_message_impl(&mut out, config);

    out
}

/// Generate the enum definition.
fn generate_enum_def(out: &mut String, config: &MessageConfig) {
    out.push_str("#[derive(Clone)]\n");
    out.push_str(&format!("pub enum {} {{\n", config.enum_name));
    for variant in &config.variants {
        if !variant.doc.is_empty() {
            out.push_str(&format!("    /// {}\n", variant.doc));
        }
        if variant.fields.is_empty() {
            out.push_str(&format!("    {},\n", variant.name));
        } else {
            out.push_str(&format!("    {} {{\n", variant.name));
            for field in &variant.fields {
                let (name, ty) = (&field[0], &field[1]);
                out.push_str(&format!("        {}: {},\n", name, ty));
            }
            out.push_str("    },\n");
        }
    }
    out.push_str("}\n\n");
}

/// Generate TAG_* constants.
fn generate_tag_constants(out: &mut String, config: &MessageConfig) {
    out.push_str("// Message tags for serialization\n");
    for (i, variant) in config.variants.iter().enumerate() {
        let tag_name = variant_to_tag_name(&variant.name);
        out.push_str(&format!("const {}: u64 = {};\n", tag_name, i + 1));
    }
    out.push('\n');
}

/// Generate the `read_u64` helper function.
fn generate_read_u64_helper(out: &mut String) {
    out.push_str("/// Read a u64 from a byte slice at the given byte offset.\n");
    out.push_str("fn read_u64(data: &Vec<u8>, offset: usize) -> u64 {\n");
    out.push_str("    u64::from_le_bytes([\n");
    for i in 0..8 {
        out.push_str(&format!("        data[offset + {}],\n", i));
    }
    out.push_str("    ])\n");
    out.push_str("}\n\n");
}

/// Generate `impl ProtocolMessage`.
fn generate_protocol_message_impl(out: &mut String, config: &MessageConfig) {
    let enum_name = &config.enum_name;

    out.push_str(&format!("impl ProtocolMessage for {} {{\n", enum_name));

    // serialize_to_bytes
    generate_serialize(out, config);

    out.push('\n');

    // deserialize_from_bytes
    generate_deserialize(out, config);

    out.push_str("}\n");
}

/// Generate `fn serialize_to_bytes`.
fn generate_serialize(out: &mut String, config: &MessageConfig) {
    let enum_name = &config.enum_name;
    out.push_str("    fn serialize_to_bytes(&self, buf: &mut Vec<u8>) {\n");
    out.push_str("        match self {\n");

    for variant in &config.variants {
        let tag_name = variant_to_tag_name(&variant.name);

        if variant.fields.is_empty() {
            out.push_str(&format!(
                "            {}::{} => {{\n",
                enum_name, variant.name
            ));
            out.push_str(&format!(
                "                buf.extend_from_slice(&{}.to_le_bytes());\n",
                tag_name
            ));
            out.push_str("            },\n");
        } else {
            // Pattern: EnumName::Variant { field1, field2, ... }
            let field_names: Vec<&str> = variant.fields.iter().map(|f| f[0].as_str()).collect();
            out.push_str(&format!(
                "            {}::{} {{ {} }} => {{\n",
                enum_name,
                variant.name,
                field_names.join(", ")
            ));

            // Tag
            out.push_str(&format!(
                "                buf.extend_from_slice(&{}.to_le_bytes());\n",
                tag_name
            ));

            // Fields
            for field in &variant.fields {
                let (name, ty) = (&field[0], &field[1]);
                if ty == "bool" {
                    out.push_str(&format!(
                        "                let {}_val: u64 = if *{} {{ 1 }} else {{ 0 }};\n",
                        name, name
                    ));
                    out.push_str(&format!(
                        "                buf.extend_from_slice(&{}_val.to_le_bytes());\n",
                        name
                    ));
                } else {
                    out.push_str(&format!(
                        "                buf.extend_from_slice(&{}.to_le_bytes());\n",
                        name
                    ));
                }
            }

            out.push_str("            },\n");
        }
    }

    out.push_str("        }\n");
    out.push_str("    }\n");
}

/// Generate `fn deserialize_from_bytes`.
fn generate_deserialize(out: &mut String, config: &MessageConfig) {
    let enum_name = &config.enum_name;
    out.push_str("    fn deserialize_from_bytes(data: &Vec<u8>) -> Option<Self> {\n");
    out.push_str("        if data.len() < 8 {\n");
    out.push_str("            return None;\n");
    out.push_str("        }\n");
    out.push_str("        let tag = read_u64(data, 0);\n");
    out.push_str("        match tag {\n");

    for variant in &config.variants {
        let tag_name = variant_to_tag_name(&variant.name);

        // Calculate total byte size: 8 (tag) + 8 per field
        let total_bytes = 8 + variant.fields.len() * 8;

        out.push_str(&format!("            {} => {{\n", tag_name));

        if !variant.fields.is_empty() {
            out.push_str(&format!(
                "                if data.len() < {} {{\n",
                total_bytes
            ));
            out.push_str("                    return None;\n");
            out.push_str("                }\n");
        }

        // Read fields at sequential offsets
        let mut offset = 8usize;
        let mut field_inits = Vec::new();

        for field in &variant.fields {
            let (name, ty) = (&field[0], &field[1]);
            if ty == "bool" {
                out.push_str(&format!(
                    "                let {} = read_u64(data, {}) != 0;\n",
                    name, offset
                ));
            } else {
                out.push_str(&format!(
                    "                let {} = read_u64(data, {});\n",
                    name, offset
                ));
            }
            field_inits.push(name.clone());
            offset += 8;
        }

        // Construct variant
        if variant.fields.is_empty() {
            out.push_str(&format!(
                "                Some({}::{})\n",
                enum_name, variant.name
            ));
        } else {
            out.push_str(&format!(
                "                Some({}::{} {{ {} }})\n",
                enum_name,
                variant.name,
                field_inits.join(", ")
            ));
        }

        out.push_str("            },\n");
    }

    out.push_str("            _ => None,\n");
    out.push_str("        }\n");
    out.push_str("    }\n");
}

/// Convert a variant name like "PreAcceptOk" to a tag constant name like "TAG_PRE_ACCEPT_OK".
fn variant_to_tag_name(name: &str) -> String {
    let mut result = String::from("TAG_");
    let mut prev_lower = false;

    for ch in name.chars() {
        if ch.is_uppercase() {
            if prev_lower {
                result.push('_');
            }
            result.push(ch);
            prev_lower = false;
        } else {
            result.push(ch.to_uppercase().next().unwrap());
            prev_lower = true;
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::MessageVariant;

    #[test]
    fn test_variant_to_tag_name() {
        assert_eq!(variant_to_tag_name("Prepare"), "TAG_PREPARE");
        assert_eq!(variant_to_tag_name("Promise"), "TAG_PROMISE");
        assert_eq!(variant_to_tag_name("PreAccept"), "TAG_PRE_ACCEPT");
        assert_eq!(variant_to_tag_name("PreAcceptOk"), "TAG_PRE_ACCEPT_OK");
        assert_eq!(variant_to_tag_name("AcceptOk"), "TAG_ACCEPT_OK");
        assert_eq!(variant_to_tag_name("CommitMsg"), "TAG_COMMIT_MSG");
        assert_eq!(variant_to_tag_name("RequestVote"), "TAG_REQUEST_VOTE");
        assert_eq!(variant_to_tag_name("VoteResponse"), "TAG_VOTE_RESPONSE");
        assert_eq!(variant_to_tag_name("AppendEntries"), "TAG_APPEND_ENTRIES");
        assert_eq!(variant_to_tag_name("AppendResponse"), "TAG_APPEND_RESPONSE");
        assert_eq!(variant_to_tag_name("ClientRequest"), "TAG_CLIENT_REQUEST");
        assert_eq!(variant_to_tag_name("PrePrepare"), "TAG_PRE_PREPARE");
    }

    #[test]
    fn test_generate_simple_message() {
        let config = MessageConfig {
            enum_name: "TestMessage".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: String::new(),
            variants: vec![
                MessageVariant {
                    name: "Ping".to_string(),
                    fields: vec![vec!["id".to_string(), "u64".to_string()]],
                    doc: String::new(),
                },
                MessageVariant {
                    name: "Pong".to_string(),
                    fields: vec![
                        vec!["id".to_string(), "u64".to_string()],
                        vec!["ok".to_string(), "bool".to_string()],
                    ],
                    doc: String::new(),
                },
            ],
        };

        let code = generate_message_code(&config);
        assert!(code.contains("pub enum TestMessage {"));
        assert!(code.contains("Ping {"));
        assert!(code.contains("id: u64,"));
        assert!(code.contains("Pong {"));
        assert!(code.contains("ok: bool,"));
        assert!(code.contains("const TAG_PING: u64 = 1;"));
        assert!(code.contains("const TAG_PONG: u64 = 2;"));
        assert!(code.contains("impl ProtocolMessage for TestMessage"));
        assert!(code.contains("serialize_to_bytes"));
        assert!(code.contains("deserialize_from_bytes"));
        // Bool encoding
        assert!(code.contains("let ok_val: u64 = if *ok { 1 } else { 0 };"));
        // Bool decoding
        assert!(code.contains("let ok = read_u64(data, 16) != 0;"));
        // Length check: tag(8) + id(8) + ok(8) = 24
        assert!(code.contains("if data.len() < 24"));
    }

    #[test]
    fn test_generate_unit_variant() {
        let config = MessageConfig {
            enum_name: "TestMessage".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: String::new(),
            variants: vec![MessageVariant {
                name: "Heartbeat".to_string(),
                fields: vec![],
                doc: String::new(),
            }],
        };

        let code = generate_message_code(&config);
        assert!(code.contains("    Heartbeat,\n"));
        assert!(code.contains("const TAG_HEARTBEAT: u64 = 1;"));
    }

    #[test]
    fn test_generate_paxos_like() {
        let config = MessageConfig {
            enum_name: "PaxosMessage".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: "Paxos protocol messages.".to_string(),
            variants: vec![
                MessageVariant {
                    name: "Prepare".to_string(),
                    fields: vec![vec!["ballot".to_string(), "u64".to_string()]],
                    doc: "Phase 1a".to_string(),
                },
                MessageVariant {
                    name: "Promise".to_string(),
                    fields: vec![
                        vec!["ballot".to_string(), "u64".to_string()],
                        vec!["accepted_bal".to_string(), "u64".to_string()],
                        vec!["accepted_val".to_string(), "u64".to_string()],
                    ],
                    doc: "Phase 1b".to_string(),
                },
                MessageVariant {
                    name: "Accept".to_string(),
                    fields: vec![
                        vec!["ballot".to_string(), "u64".to_string()],
                        vec!["value".to_string(), "u64".to_string()],
                    ],
                    doc: "Phase 2a".to_string(),
                },
                MessageVariant {
                    name: "Accepted".to_string(),
                    fields: vec![
                        vec!["ballot".to_string(), "u64".to_string()],
                        vec!["value".to_string(), "u64".to_string()],
                    ],
                    doc: "Phase 2b".to_string(),
                },
            ],
        };

        let code = generate_message_code(&config);

        // Check doc comment
        assert!(code.contains("//! Paxos protocol messages."));

        // Check enum
        assert!(code.contains("pub enum PaxosMessage"));
        assert!(code.contains("/// Phase 1a"));

        // Check tags
        assert!(code.contains("const TAG_PREPARE: u64 = 1;"));
        assert!(code.contains("const TAG_PROMISE: u64 = 2;"));
        assert!(code.contains("const TAG_ACCEPT: u64 = 3;"));
        assert!(code.contains("const TAG_ACCEPTED: u64 = 4;"));

        // Check serialize arms
        assert!(code.contains("PaxosMessage::Prepare { ballot }"));
        assert!(code.contains("PaxosMessage::Promise { ballot, accepted_bal, accepted_val }"));

        // Check deserialize length checks
        assert!(code.contains("if data.len() < 16")); // Prepare: 8+8
        assert!(code.contains("if data.len() < 32")); // Promise: 8+24
        assert!(code.contains("if data.len() < 24")); // Accept/Accepted: 8+16
    }

    #[test]
    fn test_generate_raft_like() {
        let config = MessageConfig {
            enum_name: "RaftMessage".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: String::new(),
            variants: vec![
                MessageVariant {
                    name: "RequestVote".to_string(),
                    fields: vec![
                        vec!["term".to_string(), "u64".to_string()],
                        vec!["candidate_id".to_string(), "u64".to_string()],
                        vec!["last_log_index".to_string(), "u64".to_string()],
                        vec!["last_log_term".to_string(), "u64".to_string()],
                    ],
                    doc: String::new(),
                },
                MessageVariant {
                    name: "VoteResponse".to_string(),
                    fields: vec![
                        vec!["term".to_string(), "u64".to_string()],
                        vec!["granted".to_string(), "bool".to_string()],
                        vec!["voter".to_string(), "u64".to_string()],
                    ],
                    doc: String::new(),
                },
                MessageVariant {
                    name: "AppendEntries".to_string(),
                    fields: vec![
                        vec!["term".to_string(), "u64".to_string()],
                        vec!["leader_id".to_string(), "u64".to_string()],
                        vec!["prev_log_index".to_string(), "u64".to_string()],
                        vec!["prev_log_term".to_string(), "u64".to_string()],
                        vec!["value".to_string(), "u64".to_string()],
                        vec!["has_entry".to_string(), "bool".to_string()],
                        vec!["leader_commit".to_string(), "u64".to_string()],
                    ],
                    doc: String::new(),
                },
                MessageVariant {
                    name: "AppendResponse".to_string(),
                    fields: vec![
                        vec!["term".to_string(), "u64".to_string()],
                        vec!["success".to_string(), "bool".to_string()],
                        vec!["match_index".to_string(), "u64".to_string()],
                        vec!["follower".to_string(), "u64".to_string()],
                    ],
                    doc: String::new(),
                },
            ],
        };

        let code = generate_message_code(&config);

        // Tag names
        assert!(code.contains("const TAG_REQUEST_VOTE: u64 = 1;"));
        assert!(code.contains("const TAG_VOTE_RESPONSE: u64 = 2;"));
        assert!(code.contains("const TAG_APPEND_ENTRIES: u64 = 3;"));
        assert!(code.contains("const TAG_APPEND_RESPONSE: u64 = 4;"));

        // RequestVote: 8+32=40 bytes
        assert!(code.contains("if data.len() < 40"));
        // VoteResponse: 8+24=32 bytes  (bool counts as 8)
        assert!(code.contains("if data.len() < 32"));
        // AppendEntries: 8+56=64 bytes
        assert!(code.contains("if data.len() < 64"));

        // Bool serialize
        assert!(code.contains("let granted_val: u64 = if *granted { 1 } else { 0 };"));
        assert!(code.contains("let has_entry_val: u64 = if *has_entry { 1 } else { 0 };"));
        assert!(code.contains("let success_val: u64 = if *success { 1 } else { 0 };"));

        // Bool deserialize
        assert!(code.contains("let granted = read_u64(data, 16) != 0;"));
        assert!(code.contains("let has_entry = read_u64(data, 48) != 0;"));
        assert!(code.contains("let success = read_u64(data, 16) != 0;"));
    }

    #[test]
    fn test_generate_message_with_doc_comment() {
        let config = MessageConfig {
            enum_name: "TestMsg".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: "Test protocol.\nLine 2.".to_string(),
            variants: vec![MessageVariant {
                name: "Ping".to_string(),
                fields: vec![vec!["id".to_string(), "u64".to_string()]],
                doc: "A ping message".to_string(),
            }],
        };

        let code = generate_message_code(&config);
        assert!(code.contains("//! Test protocol.\n//! Line 2."));
        assert!(code.contains("/// A ping message"));
    }

    // --- variant_to_tag_name edge cases ---

    #[test]
    fn test_variant_to_tag_single_char() {
        assert_eq!(variant_to_tag_name("A"), "TAG_A");
    }

    #[test]
    fn test_variant_to_tag_with_numbers() {
        assert_eq!(variant_to_tag_name("Msg2"), "TAG_MSG2");
    }

    #[test]
    fn test_variant_to_tag_all_caps() {
        assert_eq!(variant_to_tag_name("PREPARE"), "TAG_PREPARE");
    }

    #[test]
    fn test_variant_to_tag_consecutive_caps() {
        assert_eq!(variant_to_tag_name("PrepareOK"), "TAG_PREPARE_OK");
    }

    // --- generate_message_code scenarios ---

    #[test]
    fn test_generate_single_variant_enum() {
        let config = MessageConfig {
            enum_name: "SingleMsg".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: String::new(),
            variants: vec![MessageVariant {
                name: "Foo".to_string(),
                fields: vec![vec!["x".to_string(), "u64".to_string()]],
                doc: String::new(),
            }],
        };
        let code = generate_message_code(&config);
        assert!(code.contains("pub enum SingleMsg"));
        assert!(code.contains("const TAG_FOO: u64 = 1;"));
        assert!(code.contains("SingleMsg::Foo { x }"));
    }

    #[test]
    fn test_generate_many_fields_offsets() {
        let fields: Vec<Vec<String>> = (0..6)
            .map(|i| vec![format!("f{}", i), "u64".to_string()])
            .collect();
        let config = MessageConfig {
            enum_name: "BigMsg".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: String::new(),
            variants: vec![MessageVariant {
                name: "Wide".to_string(),
                fields,
                doc: String::new(),
            }],
        };
        let code = generate_message_code(&config);
        // Total: tag(8) + 6*8 = 56
        assert!(
            code.contains("if data.len() < 56"),
            "Should check length 56: {}",
            code
        );
        // Check individual offsets
        assert!(code.contains("read_u64(data, 8)"), "f0 at offset 8");
        assert!(code.contains("read_u64(data, 16)"), "f1 at offset 16");
        assert!(code.contains("read_u64(data, 40)"), "f4 at offset 40");
        assert!(code.contains("read_u64(data, 48)"), "f5 at offset 48");
    }

    #[test]
    fn test_generate_multiple_bool_fields() {
        let config = MessageConfig {
            enum_name: "BoolMsg".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: String::new(),
            variants: vec![MessageVariant {
                name: "Flags".to_string(),
                fields: vec![
                    vec!["a".to_string(), "bool".to_string()],
                    vec!["b".to_string(), "bool".to_string()],
                    vec!["c".to_string(), "bool".to_string()],
                ],
                doc: String::new(),
            }],
        };
        let code = generate_message_code(&config);
        assert!(code.contains("let a_val: u64 = if *a { 1 } else { 0 };"));
        assert!(code.contains("let b_val: u64 = if *b { 1 } else { 0 };"));
        assert!(code.contains("let c_val: u64 = if *c { 1 } else { 0 };"));
        assert!(code.contains("let a = read_u64(data, 8) != 0;"));
        assert!(code.contains("let b = read_u64(data, 16) != 0;"));
        assert!(code.contains("let c = read_u64(data, 24) != 0;"));
    }

    #[test]
    fn test_generate_mixed_u64_bool_interleaved() {
        let config = MessageConfig {
            enum_name: "MixMsg".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: String::new(),
            variants: vec![MessageVariant {
                name: "Mix".to_string(),
                fields: vec![
                    vec!["a".to_string(), "u64".to_string()],
                    vec!["b".to_string(), "bool".to_string()],
                    vec!["c".to_string(), "u64".to_string()],
                    vec!["d".to_string(), "bool".to_string()],
                ],
                doc: String::new(),
            }],
        };
        let code = generate_message_code(&config);
        // a: u64 at offset 8, b: bool at offset 16, c: u64 at offset 24, d: bool at offset 32
        assert!(
            code.contains("let a = read_u64(data, 8);"),
            "a at 8: {}",
            code
        );
        assert!(
            code.contains("let b = read_u64(data, 16) != 0;"),
            "b bool at 16"
        );
        assert!(
            code.contains("let c = read_u64(data, 24);"),
            "c at 24: {}",
            code
        );
        assert!(
            code.contains("let d = read_u64(data, 32) != 0;"),
            "d bool at 32"
        );
        // Total: tag(8) + 4*8 = 40
        assert!(code.contains("if data.len() < 40"));
    }

    #[test]
    fn test_generate_empty_doc_comment() {
        let config = MessageConfig {
            enum_name: "NoDocMsg".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: String::new(),
            variants: vec![MessageVariant {
                name: "Ping".to_string(),
                fields: vec![],
                doc: String::new(),
            }],
        };
        let code = generate_message_code(&config);
        assert!(
            !code.contains("//!"),
            "Empty doc_comment should produce no //! lines"
        );
    }

    #[test]
    fn test_generate_multiline_doc_comment() {
        let config = MessageConfig {
            enum_name: "DocMsg".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: "Line one.\nLine two.\nLine three.".to_string(),
            variants: vec![MessageVariant {
                name: "Ping".to_string(),
                fields: vec![],
                doc: String::new(),
            }],
        };
        let code = generate_message_code(&config);
        assert!(code.contains("//! Line one.\n//! Line two.\n//! Line three."));
    }

    #[test]
    fn test_generate_sequential_tags() {
        let variants: Vec<MessageVariant> = (1..=5)
            .map(|i| MessageVariant {
                name: format!("V{}", i),
                fields: vec![],
                doc: String::new(),
            })
            .collect();
        let config = MessageConfig {
            enum_name: "SeqMsg".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: String::new(),
            variants,
        };
        let code = generate_message_code(&config);
        for i in 1..=5 {
            assert!(code.contains(&format!("const TAG_V{}: u64 = {};", i, i)));
        }
    }

    #[test]
    fn test_generate_custom_import_path() {
        let config = MessageConfig {
            enum_name: "CustomMsg".to_string(),
            import_path: "my_crate::custom::ProtocolMessage".to_string(),
            doc_comment: String::new(),
            variants: vec![MessageVariant {
                name: "Ping".to_string(),
                fields: vec![],
                doc: String::new(),
            }],
        };
        let code = generate_message_code(&config);
        assert!(code.contains("use my_crate::custom::ProtocolMessage;"));
    }

    #[test]
    fn test_generate_deser_dispatch() {
        let config = MessageConfig {
            enum_name: "DispMsg".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: String::new(),
            variants: vec![
                MessageVariant {
                    name: "A".to_string(),
                    fields: vec![],
                    doc: String::new(),
                },
                MessageVariant {
                    name: "B".to_string(),
                    fields: vec![],
                    doc: String::new(),
                },
            ],
        };
        let code = generate_message_code(&config);
        assert!(
            code.contains("match tag {"),
            "Should have match tag dispatch"
        );
        assert!(code.contains("_ => None"), "Should have fallback None arm");
    }

    #[test]
    fn test_generate_read_u64_helper() {
        let config = MessageConfig {
            enum_name: "HelpMsg".to_string(),
            import_path: "crate::common::framework::protocol_trait::ProtocolMessage".to_string(),
            doc_comment: String::new(),
            variants: vec![MessageVariant {
                name: "Ping".to_string(),
                fields: vec![vec!["id".to_string(), "u64".to_string()]],
                doc: String::new(),
            }],
        };
        let code = generate_message_code(&config);
        assert!(code.contains("fn read_u64"));
        assert!(code.contains("u64::from_le_bytes"));
    }
}
