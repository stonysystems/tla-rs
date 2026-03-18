//! Code generation for `impl Marshalable` on struct and enum types.
//!
//! Generates field-by-field serialize/deserialize implementations that match
//! the output of the `derive_marshalable_for_struct!` and
//! `derive_marshalable_for_enum!` macros in
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

/// Generate `impl Marshalable` blocks for all types and enums in the config.
///
/// Returns Verus code (intended to be placed inside a `verus!{}` block)
/// containing one `impl Marshalable for T` per configured type/enum.
pub fn generate_marshalable_impls(config: &MarshalableConfig) -> String {
    let mut out = String::new();
    let mut first = true;
    for ty in &config.types {
        if !first {
            out.push('\n');
        }
        first = false;
        let fields: Vec<Field> = ty.fields.iter().map(|f| Field::new(&f[0], &f[1])).collect();
        generate_one_impl(&mut out, &ty.name, &fields);
    }
    for e in &config.enums {
        if !first {
            out.push('\n');
        }
        first = false;
        let variants: Vec<Variant> = e
            .variants
            .iter()
            .map(|v| Variant {
                name: v.name.clone(),
                tag: v.tag,
                fields: v.fields.iter().map(|f| Field::new(&f[0], &f[1])).collect(),
            })
            .collect();
        generate_enum_impl(&mut out, &e.name, &variants);
    }
    out
}

/// Generate a single `impl Marshalable for StructName { ... }`.
fn generate_one_impl(out: &mut String, struct_name: &str, fields: &[Field]) {
    out.push_str(&format!("impl Marshalable for {} {{\n", struct_name));

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
        out.push_str(&format!("{}self.{}.is_marshalable()\n", prefix, f.name));
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
        out.push_str(&format!("{}self.{}._is_marshalable()\n", prefix, f.name));
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
    out.push_str(
        "            assert(data@.subrange(start as int, end as int) =~= res.ghost_serialize());\n",
    );
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
        out.push_str("            let (s0, s1) = (x0.ghost_serialize(), x1.ghost_serialize());\n");
        out.push_str("            x0.lemma_view_equal_symmetric(&x1);\n");
        out.push_str("            let (x0, x1, s0, s1) = if s0.len() <= s1.len() {\n");
        out.push_str("                (x0, x1, s0, s1)\n");
        out.push_str("            } else {\n");
        out.push_str("                (x1, x0, s1, s0)\n");
        out.push_str("            };\n");
        out.push_str("            x0.lemma_serialization_is_not_a_prefix_of(&x1);\n");
        out.push_str("            assert(!(s0 =~= s1.subrange(0, s0.len() as int))); // OBSERVE\n");
        out.push_str(
            "            let idx = choose |i:int| 0 <= i < s0.len() as int && s0[i] != s1[i];\n",
        );
        out.push_str("            if si == so.subrange(0, si.len() as int) {\n");
        out.push_str("                assert(si[mid + idx] == so[mid + idx]); // OBSERVE\n");
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

// ===========================================================================
// Enum Marshalable generation
// ===========================================================================

/// An enum variant for Marshalable generation.
struct Variant {
    name: String,
    tag: u8,
    fields: Vec<Field>,
}

/// Generate a single `impl Marshalable for EnumName { ... }`.
fn generate_enum_impl(out: &mut String, enum_name: &str, variants: &[Variant]) {
    out.push_str(&format!("impl Marshalable for {} {{\n", enum_name));

    enum_gen_view_equal(out, enum_name, variants);
    enum_gen_lemma_view_equal_symmetric(out, enum_name, variants);
    enum_gen_is_marshalable(out, enum_name, variants);
    enum_gen_exec_is_marshalable(out, enum_name, variants);
    enum_gen_ghost_serialize(out, enum_name, variants);
    enum_gen_serialized_size(out, enum_name, variants);
    enum_gen_serialize(out, enum_name, variants);
    enum_gen_deserialize(out, enum_name, variants);
    enum_gen_lemma_serialization_is_not_a_prefix_of(out, enum_name, variants);
    enum_gen_lemma_same_views_serialize_the_same(out, enum_name, variants);
    gen_lemma_serialize_injective(out); // same for structs and enums

    out.push_str("}\n");
}

/// Helper: generate pattern binding like `EnumName::Variant { f1, f2 }` or `EnumName::Variant`
fn variant_pattern(enum_name: &str, v: &Variant) -> String {
    if v.fields.is_empty() {
        format!("{}::{}", enum_name, v.name)
    } else {
        let bindings: Vec<&str> = v.fields.iter().map(|f| f.name.as_str()).collect();
        format!("{}::{} {{ {} }}", enum_name, v.name, bindings.join(", "))
    }
}

/// Helper: like variant_pattern but with "other_" prefix on field names for the other argument
fn variant_pattern_other(enum_name: &str, v: &Variant) -> String {
    if v.fields.is_empty() {
        format!("{}::{}", enum_name, v.name)
    } else {
        let bindings: Vec<String> = v
            .fields
            .iter()
            .map(|f| format!("{}: o_{}", f.name, f.name))
            .collect();
        format!("{}::{} {{ {} }}", enum_name, v.name, bindings.join(", "))
    }
}

fn enum_gen_view_equal(out: &mut String, enum_name: &str, variants: &[Variant]) {
    out.push_str("    open spec fn view_equal(&self, other: &Self) -> bool {\n");
    out.push_str("        &&& match (self, other) {\n");
    for v in variants {
        let pat_self = variant_pattern(enum_name, v);
        let pat_other = variant_pattern_other(enum_name, v);
        out.push_str(&format!(
            "            ({}, {}) => {{\n",
            pat_self, pat_other
        ));
        for f in &v.fields {
            out.push_str(&format!(
                "                &&& {}.view_equal(&o_{})\n",
                f.name, f.name
            ));
        }
        out.push_str("                &&& true\n");
        out.push_str("            }\n");
    }
    out.push_str("            _ => false,\n");
    out.push_str("        }\n");
    out.push_str("    }\n");
}

fn enum_gen_lemma_view_equal_symmetric(out: &mut String, enum_name: &str, variants: &[Variant]) {
    out.push_str("    proof fn lemma_view_equal_symmetric(&self, other: &Self)\n");
    out.push_str("    // req, ens from trait\n");
    out.push_str("    {\n");
    out.push_str("        match (self, other) {\n");
    for v in variants {
        let pat_self = variant_pattern(enum_name, v);
        let pat_other = variant_pattern_other(enum_name, v);
        out.push_str(&format!(
            "            ({}, {}) => {{\n",
            pat_self, pat_other
        ));
        for f in &v.fields {
            out.push_str(&format!(
                "                {}.lemma_view_equal_symmetric(&o_{});\n",
                f.name, f.name
            ));
        }
        out.push_str("            }\n");
    }
    out.push_str("            _ => (),\n");
    out.push_str("        }\n");
    out.push_str("    }\n");
}

fn enum_gen_is_marshalable(out: &mut String, enum_name: &str, variants: &[Variant]) {
    out.push_str("    open spec fn is_marshalable(&self) -> bool {\n");
    out.push_str("        &&& match self {\n");
    for v in variants {
        let pat = variant_pattern(enum_name, v);
        out.push_str(&format!("            {} => {{\n", pat));
        for f in &v.fields {
            out.push_str(&format!(
                "                &&& {}.is_marshalable()\n",
                f.name
            ));
        }
        // overflow guard: 1 (tag) + field serializations
        out.push_str("                &&& 1");
        for f in &v.fields {
            out.push_str(&format!(" + {}.ghost_serialize().len()", f.name));
        }
        out.push_str(" <= usize::MAX\n");
        out.push_str("            }\n");
    }
    out.push_str("        }\n");
    out.push_str("    }\n");
}

fn enum_gen_exec_is_marshalable(out: &mut String, enum_name: &str, variants: &[Variant]) {
    out.push_str("    exec fn _is_marshalable(&self) -> bool {\n");
    out.push_str("        match self {\n");
    for v in variants {
        let pat = variant_pattern(enum_name, v);
        out.push_str(&format!("            {} => {{\n", pat));
        out.push_str("                &&& true\n");
        for f in &v.fields {
            out.push_str(&format!(
                "                &&& {}._is_marshalable()\n",
                f.name
            ));
        }
        // overflow check
        if !v.fields.is_empty() {
            out.push_str("                &&& ");
            enum_gen_no_usize_overflows(out, &v.fields);
            out.push('\n');
        }
        out.push_str("            }\n");
    }
    out.push_str("        }\n");
    out.push_str("    }\n");
}

/// Generate overflow chain for enum variant: starts from 1 (tag byte)
fn enum_gen_no_usize_overflows(out: &mut String, fields: &[Field]) {
    let mut running = "1".to_string();
    for (i, f) in fields.iter().enumerate() {
        if i > 0 {
            out.push_str("\n                && ");
        }
        out.push_str(&format!(
            "usize::MAX - ({}) >= {}.serialized_size()",
            running, f.name
        ));
        if i == 0 {
            running = format!("1 + {}.serialized_size()", f.name);
        } else {
            running = format!("{} + {}.serialized_size()", running, f.name);
        }
    }
}

fn enum_gen_ghost_serialize(out: &mut String, enum_name: &str, variants: &[Variant]) {
    out.push_str("    open spec fn ghost_serialize(&self) -> Seq<u8> {\n");
    out.push_str("        match self {\n");
    for v in variants {
        let pat = variant_pattern(enum_name, v);
        out.push_str(&format!("            {} => {{\n", pat));
        out.push_str(&format!("                seq![{}u8]", v.tag));
        for f in &v.fields {
            out.push_str(&format!(" + {}.ghost_serialize()", f.name));
        }
        out.push('\n');
        out.push_str("            }\n");
    }
    out.push_str("        }\n");
    out.push_str("    }\n");
}

fn enum_gen_serialized_size(out: &mut String, enum_name: &str, variants: &[Variant]) {
    out.push_str("    exec fn serialized_size(&self) -> (res: usize)\n");
    out.push_str("      // req, ens from trait\n");
    out.push_str("    {\n");
    out.push_str("        match self {\n");
    for v in variants {
        let pat = variant_pattern(enum_name, v);
        out.push_str(&format!("            {} => {{\n", pat));
        out.push_str("                1");
        for f in &v.fields {
            out.push_str(&format!(" + {}.serialized_size()", f.name));
        }
        out.push('\n');
        out.push_str("            }\n");
    }
    out.push_str("        }\n");
    out.push_str("    }\n");
}

fn enum_gen_serialize(out: &mut String, enum_name: &str, variants: &[Variant]) {
    out.push_str("    exec fn serialize(&self, data: &mut Vec<u8>)\n");
    out.push_str("      // req, ens from trait\n");
    out.push_str("    {\n");
    out.push_str("        match self {\n");
    for v in variants {
        let pat = variant_pattern(enum_name, v);
        out.push_str(&format!("            {} => {{\n", pat));
        out.push_str(&format!("                data.push({}u8);\n", v.tag));
        if !v.fields.is_empty() {
            out.push_str(
                "                let mid_data_len: Ghost<int> = Ghost(data@.len() as int);\n",
            );
            for f in &v.fields {
                out.push_str("                proof {\n");
                out.push_str(&format!(
                    "                    assert(data@.subrange(old(data)@.len() as int, mid_data_len@) =~= seq![{}u8]);\n",
                    v.tag
                ));
                out.push_str("                    assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);\n");
                out.push_str("                }\n");
                out.push_str(&format!("                {}.serialize(data);\n", f.name));
            }
        }
        out.push_str("                proof {\n");
        out.push_str("                    assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.ghost_serialize());\n");
        out.push_str("                    assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);\n");
        out.push_str("                }\n");
        out.push_str("            }\n");
    }
    out.push_str("        }\n");
    out.push_str("    }\n");
}

fn enum_gen_deserialize(out: &mut String, enum_name: &str, variants: &[Variant]) {
    out.push_str(
        "    exec fn deserialize(data: &Vec<u8>, start: usize) -> (res: Option<(Self, usize)>)\n",
    );
    out.push_str("      // req, ens from trait\n");
    out.push_str("    {\n");
    out.push_str("        if data.len() == 0 || start >= data.len() - 1 {\n");
    out.push_str("            return None;\n");
    out.push_str("        }\n");
    out.push_str("        let tag = data[start];\n");
    out.push_str("        let (x, end) = ");

    // if-else chain for tag dispatch
    for v in variants {
        out.push_str(&format!("if tag == {}u8 {{\n", v.tag));
        out.push_str("            let mid = start + 1;\n");
        for f in &v.fields {
            out.push_str(&format!(
                "            let ({}, mid) = match {}::deserialize(data, mid) {{ None => {{\n",
                f.name, f.ty
            ));
            out.push_str("              return None;\n");
            out.push_str("            }, Some(x) => x, };\n");
        }
        // construct variant
        let construction = if v.fields.is_empty() {
            format!("{}::{}", enum_name, v.name)
        } else {
            let field_names: Vec<&str> = v.fields.iter().map(|f| f.name.as_str()).collect();
            format!("{}::{} {{ {} }}", enum_name, v.name, field_names.join(", "))
        };
        out.push_str(&format!("            ({}, mid)\n", construction));
        out.push_str("        } else ");
    }
    out.push_str("{\n");
    out.push_str("            return None;\n");
    out.push_str("        };\n");

    // proof block
    out.push_str("        proof {\n");
    out.push_str("            assert(data@.subrange(start as int, end as int) == x.ghost_serialize()) by {\n");
    out.push_str("                assert(data@.subrange(start as int, end as int).len() == x.ghost_serialize().len());\n");
    out.push_str("                assert(data@.subrange(start as int, end as int) =~= x.ghost_serialize());\n");
    out.push_str("            }\n");
    out.push_str("        }\n");
    out.push_str("        Some((x, end))\n");
    out.push_str("    }\n");
}

fn enum_gen_lemma_serialization_is_not_a_prefix_of(
    out: &mut String,
    enum_name: &str,
    variants: &[Variant],
) {
    out.push_str(
        "    proof fn lemma_serialization_is_not_a_prefix_of(self: &Self, other: &Self)\n",
    );
    out.push_str("    // req, ens from trait\n");
    out.push_str("    {\n");
    out.push_str("        let si = self.ghost_serialize();\n");
    out.push_str("        let so = other.ghost_serialize();\n");
    out.push_str("        match (self, other) {\n");

    // Same-variant arms: field-by-field divergence
    for v in variants {
        let pat_self = variant_pattern(enum_name, v);
        let pat_other = variant_pattern_other(enum_name, v);
        out.push_str(&format!(
            "            ({}, {}) => {{\n",
            pat_self, pat_other
        ));
        out.push_str("                let mid: int = 1;\n");
        for f in &v.fields {
            out.push_str(&format!(
                "                if !{f}.view_equal(&o_{f}) {{\n",
                f = f.name
            ));
            out.push_str(&format!(
                "                    let (x0, x1) = ({f}, o_{f});\n",
                f = f.name
            ));
            out.push_str("                    let (s0, s1) = (x0.ghost_serialize(), x1.ghost_serialize());\n");
            out.push_str("                    x0.lemma_view_equal_symmetric(&x1);\n");
            out.push_str("                    let (x0, x1, s0, s1) = if s0.len() <= s1.len() {\n");
            out.push_str("                        (x0, x1, s0, s1)\n");
            out.push_str("                    } else {\n");
            out.push_str("                        (x1, x0, s1, s0)\n");
            out.push_str("                    };\n");
            out.push_str("                    x0.lemma_serialization_is_not_a_prefix_of(&x1);\n");
            out.push_str("                    assert(!(s0 =~= s1.subrange(0, s0.len() as int))); // OBSERVE\n");
            out.push_str("                    let idx = choose |i:int| 0 <= i < s0.len() as int && s0[i] != s1[i];\n");
            out.push_str("                    if si == so.subrange(0, si.len() as int) {\n");
            out.push_str(
                "                        assert(si[mid + idx] == so[mid + idx]); // OBSERVE\n",
            );
            out.push_str("                    }\n");
            out.push_str("                    return;\n");
            out.push_str("                } else {\n");
            out.push_str(&format!(
                "                    {f}.lemma_same_views_serialize_the_same(&o_{f});\n",
                f = f.name
            ));
            out.push_str("                }\n");
            out.push_str(&format!(
                "                let mid = mid + {}.ghost_serialize().len();\n",
                f.name
            ));
        }
        out.push_str("            }\n");
    }

    // Cross-variant catch-all: tag divergence
    out.push_str("            _ => {\n");
    out.push_str("                if si == so.subrange(0, si.len() as int) {\n");
    out.push_str("                    assert(si[0] == so[0]); // OBSERVE\n");
    out.push_str("                }\n");
    out.push_str("            },\n");
    out.push_str("        }\n");
    out.push_str("    }\n");
}

fn enum_gen_lemma_same_views_serialize_the_same(
    out: &mut String,
    enum_name: &str,
    variants: &[Variant],
) {
    out.push_str("    proof fn lemma_same_views_serialize_the_same(self: &Self, other: &Self)\n");
    out.push_str("    // req, ens from trait\n");
    out.push_str("    {\n");
    out.push_str("        match (self, other) {\n");
    for v in variants {
        let pat_self = variant_pattern(enum_name, v);
        let pat_other = variant_pattern_other(enum_name, v);
        out.push_str(&format!(
            "            ({}, {}) => {{\n",
            pat_self, pat_other
        ));
        for f in &v.fields {
            out.push_str(&format!(
                "                {}.lemma_same_views_serialize_the_same(&o_{});\n",
                f.name, f.name
            ));
        }
        out.push_str("            }\n");
    }
    out.push_str("            _ => (),\n");
    out.push_str("        }\n");
    out.push_str("    }\n");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{
        MarshalableConfig, MarshalableEnum, MarshalableEnumVariant, MarshalableType,
    };

    fn make_config(types: Vec<MarshalableType>) -> MarshalableConfig {
        MarshalableConfig {
            types,
            enums: vec![],
        }
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
        assert!(result
            .contains("0 + self.seqno.serialized_size() + self.proposer_id.serialized_size()"));
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
        assert!(result.contains("let (max_val, mid) = match CRequestBatch::deserialize(data, mid)"));
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
        let config = make_config(vec![make_type("T", vec![("a", "u64"), ("b", "u64")])]);
        let result = generate_marshalable_impls(&config);
        // spec is_marshalable overflow guard
        assert!(result.contains(
            "0 + self.a.ghost_serialize().len() + self.b.ghost_serialize().len() <= usize::MAX"
        ));
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
        assert!(
            result.contains("usize::MAX - (self.a.serialized_size()) >= self.b.serialized_size()")
        );
        assert!(result.contains(
            "usize::MAX - (self.a.serialized_size() + self.b.serialized_size()) >= self.c.serialized_size()"
        ));
    }

    #[test]
    fn test_serialize_proof_block() {
        let config = make_config(vec![make_type("T", vec![("x", "u64")])]);
        let result = generate_marshalable_impls(&config);
        assert!(
            result.contains("assert(data@.subrange(0, old(data)@.len() as int) =~= old(data)@);")
        );
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
        let config = make_config(vec![make_type("T", vec![("a", "u64"), ("b", "u64")])]);
        let result = generate_marshalable_impls(&config);
        // Should have the divergence detection pattern for each field
        assert!(result.contains("if !self.a.view_equal(&other.a) {"));
        assert!(result.contains("if !self.b.view_equal(&other.b) {"));
        assert!(result.contains("let mid = mid + self.a.ghost_serialize().len();"));
        assert!(result.contains("let mid = mid + self.b.ghost_serialize().len();"));
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

    // ===== Enum Marshalable tests =====

    fn make_enum_config(enums: Vec<MarshalableEnum>) -> MarshalableConfig {
        MarshalableConfig {
            types: vec![],
            enums,
        }
    }

    fn make_enum(name: &str, variants: Vec<MarshalableEnumVariant>) -> MarshalableEnum {
        MarshalableEnum {
            name: name.to_string(),
            variants,
        }
    }

    fn make_variant(name: &str, tag: u8, fields: Vec<(&str, &str)>) -> MarshalableEnumVariant {
        MarshalableEnumVariant {
            name: name.to_string(),
            tag,
            fields: fields
                .into_iter()
                .map(|(n, t)| vec![n.to_string(), t.to_string()])
                .collect(),
        }
    }

    #[test]
    fn test_enum_unit_variants_only() {
        let config = make_enum_config(vec![make_enum(
            "SimpleEnum",
            vec![make_variant("A", 0, vec![]), make_variant("B", 1, vec![])],
        )]);
        let result = generate_marshalable_impls(&config);
        assert!(result.contains("impl Marshalable for SimpleEnum {"));
        // ghost_serialize uses tag only for unit variants
        assert!(result.contains("seq![0u8]"));
        assert!(result.contains("seq![1u8]"));
        // serialized_size is just 1 for unit variants
        assert!(result.contains("1\n"));
        // deserialize checks tag
        assert!(result.contains("if tag == 0u8 {"));
        assert!(result.contains("if tag == 1u8 {"));
    }

    #[test]
    fn test_enum_variant_with_fields() {
        let config = make_enum_config(vec![make_enum(
            "Msg",
            vec![
                make_variant("Empty", 0, vec![]),
                make_variant("Data", 1, vec![("val", "u64"), ("ok", "bool")]),
            ],
        )]);
        let result = generate_marshalable_impls(&config);
        // view_equal: match with other bindings
        assert!(result.contains("Msg::Data { val, ok }"));
        assert!(result.contains("Msg::Data { val: o_val, ok: o_ok }"));
        assert!(result.contains("val.view_equal(&o_val)"));
        assert!(result.contains("ok.view_equal(&o_ok)"));
        // serialize: push tag then fields
        assert!(result.contains("data.push(1u8);"));
        assert!(result.contains("val.serialize(data);"));
        assert!(result.contains("ok.serialize(data);"));
        // deserialize: type dispatch
        assert!(result.contains("let (val, mid) = match u64::deserialize(data, mid)"));
        assert!(result.contains("let (ok, mid) = match bool::deserialize(data, mid)"));
        assert!(result.contains("Msg::Data { val, ok }"));
    }

    #[test]
    fn test_enum_ghost_serialize_with_fields() {
        let config = make_enum_config(vec![make_enum(
            "M",
            vec![make_variant("V", 5, vec![("x", "u64"), ("y", "u64")])],
        )]);
        let result = generate_marshalable_impls(&config);
        assert!(result.contains("seq![5u8] + x.ghost_serialize() + y.ghost_serialize()"));
    }

    #[test]
    fn test_enum_serialized_size_with_fields() {
        let config = make_enum_config(vec![make_enum(
            "M",
            vec![make_variant("V", 0, vec![("a", "u64"), ("b", "CBallot")])],
        )]);
        let result = generate_marshalable_impls(&config);
        assert!(result.contains("1 + a.serialized_size() + b.serialized_size()"));
    }

    #[test]
    fn test_enum_is_marshalable_overflow() {
        let config = make_enum_config(vec![make_enum(
            "M",
            vec![make_variant("V", 0, vec![("x", "u64"), ("y", "u64")])],
        )]);
        let result = generate_marshalable_impls(&config);
        // spec is_marshalable: 1 + field ghost sizes
        assert!(result
            .contains("1 + x.ghost_serialize().len() + y.ghost_serialize().len() <= usize::MAX"));
        // exec _is_marshalable: overflow chain starting from 1
        assert!(result.contains("usize::MAX - (1) >= x.serialized_size()"));
        assert!(result.contains("usize::MAX - (1 + x.serialized_size()) >= y.serialized_size()"));
    }

    #[test]
    fn test_enum_deserialize_if_else_chain() {
        let config = make_enum_config(vec![make_enum(
            "M",
            vec![
                make_variant("A", 0, vec![]),
                make_variant("B", 1, vec![("x", "u64")]),
                make_variant("C", 2, vec![]),
            ],
        )]);
        let result = generate_marshalable_impls(&config);
        // if-else chain
        assert!(result.contains("if tag == 0u8 {"));
        assert!(result.contains("} else if tag == 1u8 {"));
        assert!(result.contains("} else if tag == 2u8 {"));
        assert!(result.contains("} else {\n            return None;\n        };"));
    }

    #[test]
    fn test_enum_prefix_lemma_tag_divergence() {
        let config = make_enum_config(vec![make_enum(
            "M",
            vec![make_variant("A", 0, vec![]), make_variant("B", 1, vec![])],
        )]);
        let result = generate_marshalable_impls(&config);
        // Cross-variant catch-all with tag divergence
        assert!(result.contains("_ => {"));
        assert!(result.contains("assert(si[0] == so[0]); // OBSERVE"));
    }

    #[test]
    fn test_enum_prefix_lemma_field_divergence() {
        let config = make_enum_config(vec![make_enum(
            "M",
            vec![make_variant("V", 0, vec![("a", "u64"), ("b", "u64")])],
        )]);
        let result = generate_marshalable_impls(&config);
        // Same-variant field divergence
        assert!(result.contains("if !a.view_equal(&o_a) {"));
        assert!(result.contains("if !b.view_equal(&o_b) {"));
        assert!(result.contains("let mid: int = 1;"));
        assert!(result.contains("let mid = mid + a.ghost_serialize().len();"));
    }

    #[test]
    fn test_enum_serialize_proof_blocks() {
        let config = make_enum_config(vec![make_enum(
            "M",
            vec![make_variant("V", 3, vec![("x", "u64")])],
        )]);
        let result = generate_marshalable_impls(&config);
        // Mid-field proof assertion
        assert!(result.contains(
            "assert(data@.subrange(old(data)@.len() as int, mid_data_len@) =~= seq![3u8]);"
        ));
        // Final proof assertion
        assert!(result.contains(
            "assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.ghost_serialize());"
        ));
    }

    #[test]
    fn test_enum_all_11_methods_present() {
        let config = make_enum_config(vec![make_enum(
            "M",
            vec![
                make_variant("A", 0, vec![]),
                make_variant("B", 1, vec![("x", "u64")]),
            ],
        )]);
        let result = generate_marshalable_impls(&config);
        assert!(result.contains("open spec fn view_equal("));
        assert!(result.contains("proof fn lemma_view_equal_symmetric("));
        assert!(result.contains("open spec fn is_marshalable("));
        assert!(result.contains("exec fn _is_marshalable("));
        assert!(result.contains("open spec fn ghost_serialize("));
        assert!(result.contains("exec fn serialized_size("));
        assert!(result.contains("exec fn serialize("));
        assert!(result.contains("exec fn deserialize("));
        assert!(result.contains("proof fn lemma_serialization_is_not_a_prefix_of("));
        assert!(result.contains("proof fn lemma_same_views_serialize_the_same("));
        assert!(result.contains("proof fn lemma_serialize_injective("));
    }

    #[test]
    fn test_enum_toml_parsing() {
        let toml = r#"
            [[marshalable.enums]]
            name = "CAppMessage"
            [[marshalable.enums.variants]]
            name = "CAppIncrement"
            tag = 0
            [[marshalable.enums.variants]]
            name = "CAppReply"
            tag = 1
            fields = [["response", "u64"]]
            [[marshalable.enums.variants]]
            name = "CAppInvalid"
            tag = 2
        "#;
        let config: crate::config::TranspilerConfig =
            toml::from_str(toml).expect("Failed to parse TOML");
        let marsh = config.marshalable.expect("marshalable should be present");
        assert_eq!(marsh.enums.len(), 1);
        assert_eq!(marsh.enums[0].name, "CAppMessage");
        assert_eq!(marsh.enums[0].variants.len(), 3);
        assert_eq!(marsh.enums[0].variants[0].tag, 0);
        assert_eq!(marsh.enums[0].variants[1].tag, 1);
        assert_eq!(marsh.enums[0].variants[1].fields.len(), 1);
        assert_eq!(marsh.enums[0].variants[2].tag, 2);
        assert_eq!(marsh.enums[0].variants[2].fields.len(), 0);
    }

    #[test]
    fn test_mixed_structs_and_enums() {
        let config = MarshalableConfig {
            types: vec![make_type("S", vec![("x", "u64")])],
            enums: vec![make_enum(
                "E",
                vec![make_variant("V", 0, vec![("y", "u64")])],
            )],
        };
        let result = generate_marshalable_impls(&config);
        assert!(result.contains("impl Marshalable for S {"));
        assert!(result.contains("impl Marshalable for E {"));
    }

    // ===== 17.3.3c: Verify generated code matches derive_marshalable_for_enum! macro pattern =====

    /// Verify generated CAppMessage matches the structure produced by the
    /// `derive_marshalable_for_enum!` macro in marshalling.rs.
    ///
    /// CAppMessage has: CAppIncrement (tag=0), CAppReply{response:u64} (tag=1), CAppInvalid (tag=2)
    #[test]
    fn test_enum_macro_match_capp_message_view_equal() {
        let config = make_enum_config(vec![make_enum(
            "CAppMessage",
            vec![
                make_variant("CAppIncrement", 0, vec![]),
                make_variant("CAppReply", 1, vec![("response", "u64")]),
                make_variant("CAppInvalid", 2, vec![]),
            ],
        )]);
        let code = generate_marshalable_impls(&config);

        // Macro produces: match (self, other) { (Variant, Variant) => { ... &&& true }, _ => false }
        assert!(code.contains("&&& match (self, other) {"));
        assert!(code.contains("(CAppMessage::CAppIncrement, CAppMessage::CAppIncrement) => {"));
        assert!(code.contains("(CAppMessage::CAppReply { response }, CAppMessage::CAppReply { response: o_response }) => {"));
        assert!(code.contains("(CAppMessage::CAppInvalid, CAppMessage::CAppInvalid) => {"));
        assert!(code.contains("&&& response.view_equal(&o_response)"));
        // view_equal arms end with &&& true (check in the view_equal section)
        let view_eq_start = code.find("open spec fn view_equal(").unwrap();
        let view_eq_end = code.find("proof fn lemma_view_equal_symmetric(").unwrap();
        let view_eq_section = &code[view_eq_start..view_eq_end];
        assert_eq!(view_eq_section.matches("&&& true").count(), 3);
        assert!(code.contains("_ => false,"));
    }

    #[test]
    fn test_enum_macro_match_capp_message_is_marshalable() {
        let config = make_enum_config(vec![make_enum(
            "CAppMessage",
            vec![
                make_variant("CAppIncrement", 0, vec![]),
                make_variant("CAppReply", 1, vec![("response", "u64")]),
                make_variant("CAppInvalid", 2, vec![]),
            ],
        )]);
        let code = generate_marshalable_impls(&config);

        // Macro produces: &&& match self { Variant => { ... &&& 1 [+ sizes] <= usize::MAX } }
        assert!(code.contains("&&& match self {"));
        // Unit variant: just 1 <= usize::MAX
        assert!(
            code.contains("CAppMessage::CAppIncrement => {\n                &&& 1 <= usize::MAX")
        );
        // Field variant: 1 + field size
        assert!(code.contains("&&& response.is_marshalable()"));
        assert!(code.contains("&&& 1 + response.ghost_serialize().len() <= usize::MAX"));
        assert!(code.contains("CAppMessage::CAppInvalid => {\n                &&& 1 <= usize::MAX"));
    }

    #[test]
    fn test_enum_macro_match_capp_message_exec_is_marshalable() {
        let config = make_enum_config(vec![make_enum(
            "CAppMessage",
            vec![
                make_variant("CAppIncrement", 0, vec![]),
                make_variant("CAppReply", 1, vec![("response", "u64")]),
                make_variant("CAppInvalid", 2, vec![]),
            ],
        )]);
        let code = generate_marshalable_impls(&config);

        // Macro produces: match self { Variant => { &&& true [&&& field._is_marshalable()]* [&&& no_usize_overflows!(...)] } }
        // Unit variants: just &&& true (no overflow check)
        assert!(code
            .contains("CAppMessage::CAppIncrement => {\n                &&& true\n            }"));
        // Field variant: &&& true &&& field._is_marshalable() &&& overflow
        assert!(code.contains("&&& response._is_marshalable()"));
        assert!(code.contains("usize::MAX - (1) >= response.serialized_size()"));
    }

    #[test]
    fn test_enum_macro_match_capp_message_ghost_serialize() {
        let config = make_enum_config(vec![make_enum(
            "CAppMessage",
            vec![
                make_variant("CAppIncrement", 0, vec![]),
                make_variant("CAppReply", 1, vec![("response", "u64")]),
                make_variant("CAppInvalid", 2, vec![]),
            ],
        )]);
        let code = generate_marshalable_impls(&config);

        // Macro produces: match self { Variant => seq![tag] [+ field.ghost_serialize()]* }
        assert!(code.contains("seq![0u8]\n"));
        assert!(code.contains("seq![1u8] + response.ghost_serialize()"));
        assert!(code.contains("seq![2u8]\n"));
    }

    #[test]
    fn test_enum_macro_match_capp_message_serialize() {
        let config = make_enum_config(vec![make_enum(
            "CAppMessage",
            vec![
                make_variant("CAppIncrement", 0, vec![]),
                make_variant("CAppReply", 1, vec![("response", "u64")]),
                make_variant("CAppInvalid", 2, vec![]),
            ],
        )]);
        let code = generate_marshalable_impls(&config);

        // Macro: data.push(tag); [mid_data_len ghost; proof+serialize per field;] final proof
        assert!(code.contains("data.push(0u8);"));
        assert!(code.contains("data.push(1u8);"));
        assert!(code.contains("data.push(2u8);"));
        // Field variant has mid_data_len ghost
        assert!(code.contains("let mid_data_len: Ghost<int> = Ghost(data@.len() as int);"));
        // Mid-field proof for CAppReply
        assert!(code.contains(
            "assert(data@.subrange(old(data)@.len() as int, mid_data_len@) =~= seq![1u8]);"
        ));
        assert!(code.contains("response.serialize(data);"));
        // Final proof in every arm
        assert_eq!(
            code.matches("assert(data@.subrange(old(data)@.len() as int, data@.len() as int) =~= self.ghost_serialize());")
                .count(),
            3,
            "Each variant arm must have the final serialize proof assertion"
        );
    }

    #[test]
    fn test_enum_macro_match_capp_message_deserialize() {
        let config = make_enum_config(vec![make_enum(
            "CAppMessage",
            vec![
                make_variant("CAppIncrement", 0, vec![]),
                make_variant("CAppReply", 1, vec![("response", "u64")]),
                make_variant("CAppInvalid", 2, vec![]),
            ],
        )]);
        let code = generate_marshalable_impls(&config);

        // Macro: if data.len() == 0 || start >= data.len() - 1 { return None; }
        assert!(code.contains("if data.len() == 0 || start >= data.len() - 1 {"));
        assert!(code.contains("let tag = data[start];"));
        // if-else chain
        assert!(code.contains("if tag == 0u8 {"));
        assert!(code.contains("} else if tag == 1u8 {"));
        assert!(code.contains("} else if tag == 2u8 {"));
        // Field deserialization
        assert!(code.contains("let (response, mid) = match u64::deserialize(data, mid)"));
        // Construction
        assert!(code.contains("(CAppMessage::CAppIncrement, mid)"));
        assert!(code.contains("(CAppMessage::CAppReply { response }, mid)"));
        assert!(code.contains("(CAppMessage::CAppInvalid, mid)"));
        // Final else + proof block
        assert!(code.contains("} else {\n            return None;\n        };"));
        assert!(code
            .contains("assert(data@.subrange(start as int, end as int) == x.ghost_serialize())"));
        assert!(code.contains(
            "assert(data@.subrange(start as int, end as int).len() == x.ghost_serialize().len());"
        ));
        assert!(code
            .contains("assert(data@.subrange(start as int, end as int) =~= x.ghost_serialize());"));
    }

    #[test]
    fn test_enum_macro_match_capp_message_prefix_lemma() {
        let config = make_enum_config(vec![make_enum(
            "CAppMessage",
            vec![
                make_variant("CAppIncrement", 0, vec![]),
                make_variant("CAppReply", 1, vec![("response", "u64")]),
                make_variant("CAppInvalid", 2, vec![]),
            ],
        )]);
        let code = generate_marshalable_impls(&config);

        // Macro: let si = self.ghost_serialize(); let so = other.ghost_serialize();
        assert!(code.contains("let si = self.ghost_serialize();"));
        assert!(code.contains("let so = other.ghost_serialize();"));
        // Same-variant arm with fields: field-by-field divergence
        assert!(code.contains("if !response.view_equal(&o_response) {"));
        assert!(code.contains("let (x0, x1) = (response, o_response);"));
        assert!(code.contains("x0.lemma_view_equal_symmetric(&x1);"));
        assert!(code.contains("x0.lemma_serialization_is_not_a_prefix_of(&x1);"));
        assert!(code.contains("assert(!(s0 =~= s1.subrange(0, s0.len() as int))); // OBSERVE"));
        assert!(
            code.contains("let idx = choose |i:int| 0 <= i < s0.len() as int && s0[i] != s1[i];")
        );
        // Cross-variant catch-all
        assert!(code.contains("assert(si[0] == so[0]); // OBSERVE"));
    }

    #[test]
    fn test_enum_macro_match_capp_message_same_views_lemma() {
        let config = make_enum_config(vec![make_enum(
            "CAppMessage",
            vec![
                make_variant("CAppIncrement", 0, vec![]),
                make_variant("CAppReply", 1, vec![("response", "u64")]),
                make_variant("CAppInvalid", 2, vec![]),
            ],
        )]);
        let code = generate_marshalable_impls(&config);

        // lemma_same_views_serialize_the_same: match with delegation
        assert!(code.contains("response.lemma_same_views_serialize_the_same(&o_response);"));
        // Catch-all
        let same_views_section = code
            .find("proof fn lemma_same_views_serialize_the_same")
            .expect("missing lemma_same_views_serialize_the_same");
        let section = &code[same_views_section..];
        assert!(section.contains("_ => (),"));
    }

    #[test]
    fn test_enum_macro_match_capp_message_injective_lemma() {
        let config = make_enum_config(vec![make_enum(
            "CAppMessage",
            vec![
                make_variant("CAppIncrement", 0, vec![]),
                make_variant("CAppReply", 1, vec![("response", "u64")]),
                make_variant("CAppInvalid", 2, vec![]),
            ],
        )]);
        let code = generate_marshalable_impls(&config);

        // lemma_serialize_injective: same for structs and enums
        assert!(code.contains("self.lemma_serialization_is_not_a_prefix_of(other);"));
        assert!(code.contains(
            "assert(other.ghost_serialize().subrange(0, self.ghost_serialize().len() as int)"
        ));
    }
}
