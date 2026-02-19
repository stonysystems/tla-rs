//! Code generation for `impl Marshalable` on struct types.
//!
//! Generates field-by-field serialize/deserialize implementations that match
//! the output of the `derive_marshalable_for_struct!` macro in
//! `src/implementation/common/marshalling.rs`.
//!
//! The generated code lives inside a `verus!{}` block and includes:
//! - `view_equal`, `is_marshalable`, `ghost_serialize` (spec fns)
//! - `_is_marshalable`, `serialized_size`, `serialize`, `deserialize` (exec fns)
//! - `lemma_view_equal_symmetric`, `lemma_serialization_is_not_a_prefix_of`,
//!   `lemma_same_views_serialize_the_same`, `lemma_serialize_injective` (proof fns)

use crate::config::MarshalableConfig;

/// A field in a struct for Marshalable generation.
struct Field {
    name: String,
    ty: String,
}

impl Field {
    fn new(name: &str, ty: &str) -> Self {
        Self {
            name: name.to_string(),
            ty: ty.to_string(),
        }
    }
}

/// Generate `impl Marshalable` blocks for all types in the config.
///
/// Returns Verus code (intended to be placed inside a `verus!{}` block)
/// containing one `impl Marshalable for T` per configured type.
pub fn generate_marshalable_impls(config: &MarshalableConfig) -> String {
    let mut out = String::new();
    for (i, ty) in config.types.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        let fields: Vec<Field> = ty
            .fields
            .iter()
            .map(|f| Field::new(&f[0], &f[1]))
            .collect();
        generate_one_impl(&mut out, &ty.name, &fields);
    }
    out
}

/// Generate a single `impl Marshalable for StructName { ... }`.
fn generate_one_impl(out: &mut String, struct_name: &str, fields: &[Field]) {
    out.push_str(&format!(
        "impl Marshalable for {} {{\n",
        struct_name
    ));

    gen_view_equal(out, fields);
    gen_lemma_view_equal_symmetric(out, fields);
    gen_is_marshalable(out, fields);
    gen_exec_is_marshalable(out, fields);
    gen_ghost_serialize(out, fields);
    gen_serialized_size(out, fields);
    gen_serialize(out, fields);
    gen_deserialize(out, struct_name, fields);
    gen_lemma_serialization_is_not_a_prefix_of(out, fields);
    gen_lemma_same_views_serialize_the_same(out, fields);
    gen_lemma_serialize_injective(out);

    out.push_str("}\n");
}

// ---------------------------------------------------------------------------
// Individual method generators
// ---------------------------------------------------------------------------

fn gen_view_equal(out: &mut String, fields: &[Field]) {
    out.push_str("    open spec fn view_equal(&self, other: &Self) -> bool {\n");
    for (i, f) in fields.iter().enumerate() {
        let prefix = if i == 0 { "        " } else { "        &&& " };
        out.push_str(&format!(
            "{}self.{}.view_equal(&other.{})\n",
            prefix, f.name, f.name
        ));
    }
    out.push_str("    }\n");
}

fn gen_lemma_view_equal_symmetric(out: &mut String, fields: &[Field]) {
    out.push_str("    proof fn lemma_view_equal_symmetric(&self, other: &Self)\n");
    out.push_str("    // req, ens from trait\n");
    out.push_str("    {\n");
    for f in fields {
        out.push_str(&format!(
            "        self.{}.lemma_view_equal_symmetric(&other.{});\n",
            f.name, f.name
        ));
    }
    out.push_str("    }\n");
}

fn gen_is_marshalable(out: &mut String, fields: &[Field]) {
    out.push_str("    open spec fn is_marshalable(&self) -> bool {\n");
    for (i, f) in fields.iter().enumerate() {
        let prefix = if i == 0 { "        " } else { "        &&& " };
        out.push_str(&format!(
            "{}self.{}.is_marshalable()\n",
            prefix, f.name
        ));
    }
    // overflow guard
    out.push_str("        &&& 0");
    for f in fields {
        out.push_str(&format!(" + self.{}.ghost_serialize().len()", f.name));
    }
    out.push_str(" <= usize::MAX\n");
    out.push_str("    }\n");
}

fn gen_exec_is_marshalable(out: &mut String, fields: &[Field]) {
    out.push_str("    exec fn _is_marshalable(&self) -> bool\n");
    out.push_str("      // req, ens from trait\n");
    out.push_str("    {\n");
    // Build the conjunction of field._is_marshalable() && no_usize_overflows
    for (i, f) in fields.iter().enumerate() {
        let prefix = if i == 0 { "        " } else { "        &&& " };
        out.push_str(&format!(
            "{}self.{}._is_marshalable()\n",
            prefix, f.name
        ));
    }
    // overflow check: chain of `usize::MAX - running_total >= next_size`
    out.push_str("        &&& ");
    gen_no_usize_overflows(out, fields);
    out.push('\n');
    out.push_str("    }\n");
}

/// Generate the overflow-check expression matching `no_usize_overflows!` macro output.
fn gen_no_usize_overflows(out: &mut String, fields: &[Field]) {
    if fields.is_empty() {
        out.push_str("true");
        return;
    }
    if fields.len() == 1 {
        out.push_str(&format!(
            "usize::MAX - 0 >= self.{}.serialized_size()",
            fields[0].name
        ));
        return;
    }
    // Chain: usize::MAX - 0 >= f0.serialized_size()
    //     && usize::MAX - (0 + f0.serialized_size()) >= f1.serialized_size()
    //     && ...
    let mut running = "0".to_string();
    for (i, f) in fields.iter().enumerate() {
        if i > 0 {
            out.push_str("\n        && ");
        }
        out.push_str(&format!(
            "usize::MAX - ({}) >= self.{}.serialized_size()",
            running, f.name
        ));
        if i == 0 {
            running = format!("self.{}.serialized_size()", f.name);
        } else {
            running = format!("{} + self.{}.serialized_size()", running, f.name);
        }
    }
}

fn gen_ghost_serialize(out: &mut String, fields: &[Field]) {
    out.push_str("    open spec fn ghost_serialize(&self) -> Seq<u8> {\n");
    out.push_str("        Seq::empty()");
    for f in fields {
        out.push_str(&format!(" + self.{}.ghost_serialize()", f.name));
    }
    out.push('\n');
    out.push_str("    }\n");
}

fn gen_serialized_size(out: &mut String, fields: &[Field]) {
    out.push_str("    exec fn serialized_size(&self) -> (res: usize)\n");
    out.push_str("      // req, ens from trait\n");
    out.push_str("    {\n");
    out.push_str("        0");
    for f in fields {
        out.push_str(&format!(" + self.{}.serialized_size()", f.name));
    }
    out.push('\n');
    out.push_str("    }\n");
}

fn gen_serialize(out: &mut String, fields: &[Field]) {
    out.push_str("    exec fn serialize(&self, data: &mut Vec<u8>)\n");
    out.push_str("      // req, ens from trait\n");
    out.push_str("    {\n");
    for f in fields {
        out.push_str(&format!("        self.{}.serialize(data);\n", f.name));
    }
    out.push_str("        proof {\n");
    out.push_str(
        "            assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);\n",
    );
    out.push_str("            assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.ghost_serialize());\n");
    out.push_str("        }\n");
    out.push_str("    }\n");
}

fn gen_deserialize(out: &mut String, struct_name: &str, fields: &[Field]) {
    out.push_str(
        "    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)\n",
    );
    out.push_str("      // req, ens from trait\n");
    out.push_str("    {\n");
    out.push_str("        let mid = start;\n");
    for f in fields {
        out.push_str(&format!(
            "        let ({}, mid) = match {}::deserialize(data, mid) {{ None => {{\n",
            f.name, f.ty
        ));
        out.push_str("          return None;\n");
        out.push_str("        }, Some(x) => x, };\n");
    }
    out.push_str("        let end = mid;\n");
    out.push_str(&format!("        let res = {} {{\n", struct_name));
    for f in fields {
        out.push_str(&format!("            {},\n", f.name));
    }
    out.push_str("        };\n");
    out.push_str("        proof {\n");
    out.push_str("            assert(data@.subrange(start as int, end as int) =~= res.ghost_serialize());\n");
    out.push_str("        }\n");
    out.push_str("        Some((res, end))\n");
    out.push_str("    }\n");
}

fn gen_lemma_serialization_is_not_a_prefix_of(out: &mut String, fields: &[Field]) {
    out.push_str(
        "    proof fn lemma_serialization_is_not_a_prefix_of(self: &Self, other: &Self)\n",
    );
    out.push_str("    // req, ens from trait\n");
    out.push_str("    {\n");
    out.push_str("        let si = self.ghost_serialize();\n");
    out.push_str("        let so = other.ghost_serialize();\n");
    out.push_str("        let mid: int = 0;\n");

    for f in fields {
        // if-else block per field: divergent → prove prefix violation; equal → advance mid
        out.push_str(&format!(
            "        if !self.{f}.view_equal(&other.{f}) {{\n",
            f = f.name
        ));
        out.push_str(&format!(
            "            let (x0, x1) = (self.{f}, other.{f});\n",
            f = f.name
        ));
        out.push_str(
            "            let (s0, s1) = (x0.ghost_serialize(), x1.ghost_serialize());\n",
        );
        out.push_str("            x0.lemma_view_equal_symmetric(&x1);\n");
        out.push_str("            let (x0, x1, s0, s1) = if s0.len() <= s1.len() {\n");
        out.push_str("                (x0, x1, s0, s1)\n");
        out.push_str("            } else {\n");
        out.push_str("                (x1, x0, s1, s0)\n");
        out.push_str("            };\n");
        out.push_str("            x0.lemma_serialization_is_not_a_prefix_of(&x1);\n");
        out.push_str(
            "            assert(!(s0 =~= s1.subrange(0, s0.len() as int))); // OBSERVE\n",
        );
        out.push_str(
            "            let idx = choose |i:int| 0 <= i < s0.len() as int && s0[i] != s1[i];\n",
        );
        out.push_str("            if si == so.subrange(0, si.len() as int) {\n");
        out.push_str(
            "                assert(si[mid + idx] == so[mid + idx]); // OBSERVE\n",
        );
        out.push_str("            }\n");
        out.push_str("            return;\n");
        out.push_str("        } else {\n");
        out.push_str(&format!(
            "            self.{f}.lemma_same_views_serialize_the_same(&other.{f});\n",
            f = f.name
        ));
        out.push_str("        }\n");
        out.push_str(&format!(
            "        let mid = mid + self.{}.ghost_serialize().len();\n",
            f.name
        ));
    }

    out.push_str("    }\n");
}

fn gen_lemma_same_views_serialize_the_same(out: &mut String, fields: &[Field]) {
    out.push_str("    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)\n");
    out.push_str("    // req, ens from trait\n");
    out.push_str("    {\n");
    for f in fields {
        out.push_str(&format!(
            "        self.{}.lemma_same_views_serialize_the_same(&other.{});\n",
            f.name, f.name
        ));
    }
    out.push_str("    }\n");
}

fn gen_lemma_serialize_injective(out: &mut String) {
    out.push_str("    proof fn lemma_serialize_injective(self: &Self, other: &Self) {\n");
    out.push_str("        if !self.view_equal(other) {\n");
    out.push_str("            self.lemma_serialization_is_not_a_prefix_of(other);\n");
    out.push_str("            assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)\n");
    out.push_str("                   =~= other.ghost_serialize()); // OBSERVE\n");
    out.push_str("        }\n");
    out.push_str("    }\n");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{MarshalableConfig, MarshalableType};

    fn make_config(types: Vec<MarshalableType>) -> MarshalableConfig {
        MarshalableConfig { types }
    }

    fn make_type(name: &str, fields: Vec<(&str, &str)>) -> MarshalableType {
        MarshalableType {
            name: name.to_string(),
            fields: fields
                .into_iter()
                .map(|(n, t)| vec![n.to_string(), t.to_string()])
                .collect(),
        }
    }

    #[test]
    fn test_empty_config_produces_empty_output() {
        let config = make_config(vec![]);
        let result = generate_marshalable_impls(&config);
        assert!(result.is_empty());
    }

    #[test]
    fn test_single_u64_field() {
        let config = make_config(vec![make_type("Simple", vec![("val", "u64")])]);
        let result = generate_marshalable_impls(&config);
        assert!(result.contains("impl Marshalable for Simple {"));
        assert!(result.contains("self.val.view_equal(&other.val)"));
        assert!(result.contains("self.val.serialize(data);"));
        assert!(result.contains("let (val, mid) = match u64::deserialize(data, mid)"));
        assert!(result.contains("let res = Simple {"));
    }

    #[test]
    fn test_two_u64_fields_ballot_like() {
        let config = make_config(vec![make_type(
            "CBallot",
            vec![("seqno", "u64"), ("proposer_id", "u64")],
        )]);
        let result = generate_marshalable_impls(&config);
        assert!(result.contains("impl Marshalable for CBallot {"));
        // view_equal: both fields
        assert!(result.contains("self.seqno.view_equal(&other.seqno)"));
        assert!(result.contains("self.proposer_id.view_equal(&other.proposer_id)"));
        // ghost_serialize: concatenation
        assert!(result.contains(
            "Seq::empty() + self.seqno.ghost_serialize() + self.proposer_id.ghost_serialize()"
        ));
        // serialized_size: addition
        assert!(
            result.contains("0 + self.seqno.serialized_size() + self.proposer_id.serialized_size()")
        );
        // deserialize: sequential
        assert!(result.contains("let (seqno, mid) = match u64::deserialize(data, mid)"));
        assert!(result.contains("let (proposer_id, mid) = match u64::deserialize(data, mid)"));
    }

    #[test]
    fn test_nested_struct_field() {
        let config = make_config(vec![make_type(
            "CVote",
            vec![("max_value_bal", "CBallot"), ("max_val", "CRequestBatch")],
        )]);
        let result = generate_marshalable_impls(&config);
        assert!(result.contains("let (max_value_bal, mid) = match CBallot::deserialize(data, mid)"));
        assert!(
            result.contains("let (max_val, mid) = match CRequestBatch::deserialize(data, mid)")
        );
    }

    #[test]
    fn test_proof_lemmas_present() {
        let config = make_config(vec![make_type("T", vec![("a", "u64"), ("b", "u64")])]);
        let result = generate_marshalable_impls(&config);
        assert!(result.contains("proof fn lemma_view_equal_symmetric"));
        assert!(result.contains("proof fn lemma_serialization_is_not_a_prefix_of"));
        assert!(result.contains("proof fn lemma_same_views_serialize_the_same"));
        assert!(result.contains("proof fn lemma_serialize_injective"));
    }

    #[test]
    fn test_is_marshalable_overflow_guard() {
        let config = make_config(vec![make_type(
            "T",
            vec![("a", "u64"), ("b", "u64")],
        )]);
        let result = generate_marshalable_impls(&config);
        // spec is_marshalable overflow guard
        assert!(result
            .contains("0 + self.a.ghost_serialize().len() + self.b.ghost_serialize().len() <= usize::MAX"));
    }

    #[test]
    fn test_exec_is_marshalable_overflow_chain() {
        let config = make_config(vec![make_type(
            "T",
            vec![("a", "u64"), ("b", "u64"), ("c", "u64")],
        )]);
        let result = generate_marshalable_impls(&config);
        // Should have chained overflow checks
        assert!(result.contains("usize::MAX - (0) >= self.a.serialized_size()"));
        assert!(result.contains(
            "usize::MAX - (self.a.serialized_size()) >= self.b.serialized_size()"
        ));
        assert!(result.contains(
            "usize::MAX - (self.a.serialized_size() + self.b.serialized_size()) >= self.c.serialized_size()"
        ));
    }

    #[test]
    fn test_serialize_proof_block() {
        let config = make_config(vec![make_type("T", vec![("x", "u64")])]);
        let result = generate_marshalable_impls(&config);
        assert!(result.contains(
            "assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);"
        ));
        assert!(result.contains(
            "assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.ghost_serialize());"
        ));
    }

    #[test]
    fn test_deserialize_proof_block() {
        let config = make_config(vec![make_type("T", vec![("x", "u64")])]);
        let result = generate_marshalable_impls(&config);
        assert!(result.contains(
            "assert(data@.subrange(start as int, end as int) =~= res.ghost_serialize());"
        ));
    }

    #[test]
    fn test_prefix_lemma_structure() {
        let config = make_config(vec![make_type(
            "T",
            vec![("a", "u64"), ("b", "u64")],
        )]);
        let result = generate_marshalable_impls(&config);
        // Should have the divergence detection pattern for each field
        assert!(result.contains("if !self.a.view_equal(&other.a) {"));
        assert!(result.contains("if !self.b.view_equal(&other.b) {"));
        assert!(result
            .contains("let mid = mid + self.a.ghost_serialize().len();"));
        assert!(result
            .contains("let mid = mid + self.b.ghost_serialize().len();"));
    }

    #[test]
    fn test_multiple_types() {
        let config = make_config(vec![
            make_type("A", vec![("x", "u64")]),
            make_type("B", vec![("y", "bool")]),
        ]);
        let result = generate_marshalable_impls(&config);
        assert!(result.contains("impl Marshalable for A {"));
        assert!(result.contains("impl Marshalable for B {"));
        assert!(result.contains("let (x, mid) = match u64::deserialize(data, mid)"));
        assert!(result.contains("let (y, mid) = match bool::deserialize(data, mid)"));
    }

    #[test]
    fn test_vec_u8_field() {
        let config = make_config(vec![make_type("EndPoint", vec![("id", "Vec<u8>")])]);
        let result = generate_marshalable_impls(&config);
        assert!(result.contains("let (id, mid) = match Vec<u8>::deserialize(data, mid)"));
        assert!(result.contains("self.id.serialize(data);"));
    }

    #[test]
    fn test_toml_parsing() {
        let toml = r#"
            [[marshalable.types]]
            name = "CBallot"
            fields = [["seqno", "u64"], ["proposer_id", "u64"]]

            [[marshalable.types]]
            name = "CVote"
            fields = [["max_value_bal", "CBallot"], ["max_val", "CRequestBatch"]]
        "#;
        let config: crate::config::TranspilerConfig =
            toml::from_str(toml).expect("Failed to parse TOML");
        let marsh = config.marshalable.expect("marshalable should be present");
        assert_eq!(marsh.types.len(), 2);
        assert_eq!(marsh.types[0].name, "CBallot");
        assert_eq!(marsh.types[0].fields.len(), 2);
        assert_eq!(marsh.types[1].name, "CVote");
        assert_eq!(marsh.types[1].fields[0], vec!["max_value_bal", "CBallot"]);
    }

    #[test]
    fn test_marshalable_config_default_none() {
        let config = crate::config::TranspilerConfig::default();
        assert!(config.marshalable.is_none());
    }
}
