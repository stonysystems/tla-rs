use crate::ast::{Path, Type};
use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::config::{DomainSpec, ModelConfig, ModelValue};
use crate::modelcheck::ir::TransitionBranchIr;
use crate::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue};
use crate::spec_analyzer::SpecSchema;
use crate::types::{EnumDef, StructDef, VariantFields};
use std::collections::{BTreeMap, BTreeSet};

/// Concrete assignment for existential variables in one `LNext` branch.
pub type ExistentialAssignment = BTreeMap<String, RuntimeValue>;

/// Expand a branch's existential variables into concrete assignments using
/// configured finite domains.
pub fn expand_branch_existentials(
    branch: &TransitionBranchIr,
    schema: &SpecSchema,
    model: &ModelConfig,
) -> TranspileResult<Vec<ExistentialAssignment>> {
    let expansion_limit = model.search.max_states;
    let bounds = RuntimeCollectionBounds::from(&model.collections);
    let mut var_domains = Vec::new();

    for var in &branch.existential_vars {
        if var.name == "_" {
            return Err(TranspileError::Config {
                message: format!(
                    "Branch `{}` contains wildcard existential binding `_`; \
                     model checking requires named existential variables.",
                    branch.label
                ),
            });
        }

        let ty = var.ty.as_ref().ok_or_else(|| TranspileError::Config {
            message: format!(
                "Branch `{}` existential `{}` is missing a type annotation. \
                 Add an explicit type or configure a derivation path.",
                branch.label, var.name
            ),
        })?;

        let domain = expand_type_domain(ty, schema, model, &bounds, expansion_limit, 0)?;
        if domain.is_empty() {
            return Err(TranspileError::Config {
                message: format!(
                    "Branch `{}` existential `{}` expanded to an empty domain for type `{}`.",
                    branch.label,
                    var.name,
                    format_type_name(ty)
                ),
            });
        }
        var_domains.push((var.name.clone(), domain));
    }

    cartesian_assignments(&var_domains, expansion_limit)
}

fn cartesian_assignments(
    var_domains: &[(String, Vec<RuntimeValue>)],
    expansion_limit: usize,
) -> TranspileResult<Vec<ExistentialAssignment>> {
    if var_domains.is_empty() {
        return Ok(vec![BTreeMap::new()]);
    }

    let mut assignments = vec![BTreeMap::new()];
    for (var_name, domain) in var_domains {
        let mut next = Vec::new();
        for partial in &assignments {
            for value in domain {
                let mut assignment = partial.clone();
                assignment.insert(var_name.clone(), value.clone());
                next.push(assignment);
                if next.len() > expansion_limit {
                    return Err(TranspileError::Config {
                        message: format!(
                            "Existential domain expansion exceeded limit ({} assignments). \
                             Reduce quantifier domains/collection bounds or increase max_states.",
                            expansion_limit
                        ),
                    });
                }
            }
        }
        assignments = next;
    }
    Ok(assignments)
}

fn expand_type_domain(
    ty: &Type,
    schema: &SpecSchema,
    model: &ModelConfig,
    bounds: &RuntimeCollectionBounds,
    expansion_limit: usize,
    recursion_depth: usize,
) -> TranspileResult<Vec<RuntimeValue>> {
    if recursion_depth > 16 {
        return Err(TranspileError::Config {
            message: "Type domain expansion exceeded recursion depth limit (16).".to_string(),
        });
    }

    match ty {
        Type::Unit => Ok(vec![RuntimeValue::Unit]),
        Type::Bool => Ok(vec![RuntimeValue::Bool(false), RuntimeValue::Bool(true)]),
        Type::Int => {
            let range = model
                .quantifiers
                .int
                .as_ref()
                .ok_or_else(|| TranspileError::Config {
                    message: "Missing domain for `int`: set `quantifiers.int` in model.toml."
                        .to_string(),
                })?;
            if range.min > range.max {
                return Err(TranspileError::Config {
                    message: format!(
                        "Invalid int domain: min ({}) > max ({}).",
                        range.min, range.max
                    ),
                });
            }
            Ok((range.min..=range.max)
                .map(|v| RuntimeValue::Int(i128::from(v)))
                .collect())
        }
        Type::Nat => {
            let range = model
                .quantifiers
                .nat
                .as_ref()
                .ok_or_else(|| TranspileError::Config {
                    message: "Missing domain for `nat`: set `quantifiers.nat` in model.toml."
                        .to_string(),
                })?;
            Ok((0..=range.max).map(RuntimeValue::Nat).collect())
        }
        Type::Reference { ty, .. } => expand_type_domain(
            ty,
            schema,
            model,
            bounds,
            expansion_limit,
            recursion_depth + 1,
        ),
        Type::Tuple(items) => {
            let mut item_domains = Vec::new();
            for item_ty in items {
                item_domains.push(expand_type_domain(
                    item_ty,
                    schema,
                    model,
                    bounds,
                    expansion_limit,
                    recursion_depth + 1,
                )?);
            }
            let tuples = cartesian_values(&item_domains, expansion_limit)?
                .into_iter()
                .map(RuntimeValue::Tuple)
                .collect();
            Ok(tuples)
        }
        Type::Seq(elem_ty) => {
            let elem_domain = unique_sorted(expand_type_domain(
                elem_ty,
                schema,
                model,
                bounds,
                expansion_limit,
                recursion_depth + 1,
            )?);
            generate_seq_domain(&elem_domain, bounds.max_seq_len, expansion_limit)
        }
        Type::Set(elem_ty) => {
            let elem_domain = unique_sorted(expand_type_domain(
                elem_ty,
                schema,
                model,
                bounds,
                expansion_limit,
                recursion_depth + 1,
            )?);
            generate_set_domain(&elem_domain, bounds.max_set_len, expansion_limit)
        }
        Type::Map(key_ty, value_ty) => {
            let key_domain = unique_sorted(expand_type_domain(
                key_ty,
                schema,
                model,
                bounds,
                expansion_limit,
                recursion_depth + 1,
            )?);
            let value_domain = unique_sorted(expand_type_domain(
                value_ty,
                schema,
                model,
                bounds,
                expansion_limit,
                recursion_depth + 1,
            )?);
            generate_map_domain(
                &key_domain,
                &value_domain,
                bounds.max_map_len,
                expansion_limit,
            )
        }
        Type::Named(path) => expand_named_type_domain(
            path,
            schema,
            model,
            bounds,
            expansion_limit,
            recursion_depth + 1,
        ),
        Type::Generic(path, args) => {
            let maybe_container = match (path.last(), args.as_slice()) {
                (Some("Seq"), [elem]) => Some(Type::Seq(Box::new(elem.clone()))),
                (Some("Set"), [elem]) => Some(Type::Set(Box::new(elem.clone()))),
                (Some("Map"), [key, value]) => {
                    Some(Type::Map(Box::new(key.clone()), Box::new(value.clone())))
                }
                _ => None,
            };

            if let Some(container_ty) = maybe_container {
                return expand_type_domain(
                    &container_ty,
                    schema,
                    model,
                    bounds,
                    expansion_limit,
                    recursion_depth + 1,
                );
            }

            Err(TranspileError::UnsupportedPattern {
                message: format!(
                    "existential domain expansion does not support generic type `{}`",
                    format_type_name(ty)
                ),
                span: None,
                help: Some(
                    "Use concrete built-in containers (Seq/Set/Map) or add explicit support."
                        .to_string(),
                ),
            })
        }
    }
}

fn expand_named_type_domain(
    path: &Path,
    schema: &SpecSchema,
    model: &ModelConfig,
    bounds: &RuntimeCollectionBounds,
    expansion_limit: usize,
    recursion_depth: usize,
) -> TranspileResult<Vec<RuntimeValue>> {
    let candidates = type_name_candidates(path);
    if let Some(domain) = find_quantifier_domain(model, &candidates) {
        return expand_named_domain_override(
            path,
            schema,
            domain,
            model,
            bounds,
            expansion_limit,
            recursion_depth,
        );
    }

    if let Some(alias_ty) = find_alias_type(schema, &candidates) {
        return expand_type_domain(
            alias_ty,
            schema,
            model,
            bounds,
            expansion_limit,
            recursion_depth + 1,
        );
    }

    if let Some((enum_name, enum_def)) = find_enum(schema, &candidates) {
        return expand_enum_variants(
            &enum_name,
            enum_def,
            None,
            schema,
            model,
            bounds,
            expansion_limit,
            recursion_depth,
        );
    }
    if let Some((struct_name, struct_def)) = find_struct(schema, &candidates) {
        return expand_struct_values(
            &struct_name,
            struct_def,
            schema,
            model,
            bounds,
            expansion_limit,
            recursion_depth,
        );
    }

    if let Some((primitive_name, kind)) = primitive_named_integer_kind(&candidates) {
        return expand_primitive_named_integer_domain(&primitive_name, kind, model);
    }

    Err(TranspileError::Config {
        message: format!(
            "Missing domain for named type `{}`. Provide `quantifiers.types.{}` in model.toml.",
            path.segments.join("::"),
            path.last().unwrap_or("Type")
        ),
    })
}

fn expand_named_domain_override(
    path: &Path,
    schema: &SpecSchema,
    domain: &DomainSpec,
    model: &ModelConfig,
    bounds: &RuntimeCollectionBounds,
    expansion_limit: usize,
    recursion_depth: usize,
) -> TranspileResult<Vec<RuntimeValue>> {
    if let Some((enum_name, enum_def)) = find_enum(schema, &type_name_candidates(path)) {
        return expand_enum_variants(
            &enum_name,
            enum_def,
            Some(domain),
            schema,
            model,
            bounds,
            expansion_limit,
            recursion_depth,
        );
    }

    match domain {
        DomainSpec::Values { values } => {
            let mut out = Vec::new();
            for value in values {
                out.push(runtime_from_model_value(value, &Type::Named(path.clone()))?);
            }
            Ok(unique_sorted(out))
        }
        DomainSpec::IntRange { min, max } => {
            if min > max {
                return Err(TranspileError::Config {
                    message: format!(
                        "Invalid int range override for named type `{}`: min ({}) > max ({}).",
                        path.segments.join("::"),
                        min,
                        max
                    ),
                });
            }
            Ok((*min..=*max)
                .map(|v| RuntimeValue::Int(i128::from(v)))
                .collect())
        }
        DomainSpec::NatRange { max } => Ok((0..=*max).map(RuntimeValue::Nat).collect()),
        DomainSpec::EnumSubset { .. } => Err(TranspileError::Config {
            message: format!(
                "Type `{}` is not an enum, so enum_subset cannot be used for its domain.",
                path.segments.join("::")
            ),
        }),
    }
}

fn expand_enum_variants(
    enum_name: &str,
    enum_def: &EnumDef,
    override_domain: Option<&DomainSpec>,
    schema: &SpecSchema,
    model: &ModelConfig,
    bounds: &RuntimeCollectionBounds,
    expansion_limit: usize,
    recursion_depth: usize,
) -> TranspileResult<Vec<RuntimeValue>> {
    let variant_names: Vec<String> = match override_domain {
        Some(DomainSpec::EnumSubset { variants }) => variants.clone(),
        Some(DomainSpec::Values { values }) => {
            let mut names = Vec::new();
            for value in values {
                match value {
                    ModelValue::String(name) => names.push(name.clone()),
                    _ => {
                        return Err(TranspileError::Config {
                            message: format!(
                                "Enum domain for `{}` via `values` must use string variant names.",
                                enum_name
                            ),
                        });
                    }
                }
            }
            names
        }
        Some(DomainSpec::IntRange { .. }) | Some(DomainSpec::NatRange { .. }) => {
            return Err(TranspileError::Config {
                message: format!(
                    "Enum domain for `{}` cannot use numeric range; use enum_subset or values.",
                    enum_name
                ),
            });
        }
        None => enum_def.variants.iter().map(|v| v.name.clone()).collect(),
    };

    let mut out = Vec::new();
    for variant_name in variant_names {
        let variant = enum_def
            .variants
            .iter()
            .find(|v| v.name == variant_name)
            .ok_or_else(|| TranspileError::Config {
                message: format!(
                    "Enum domain for `{}` references unknown variant `{}`.",
                    enum_name, variant_name
                ),
            })?;

        match &variant.fields {
            VariantFields::Unit => {
                out.push(RuntimeValue::enum_value(
                    enum_name.to_string(),
                    variant.name.clone(),
                    Vec::<(String, RuntimeValue)>::new(),
                )?);
            }
            VariantFields::Struct(fields) if fields.is_empty() => {
                out.push(RuntimeValue::enum_value(
                    enum_name.to_string(),
                    variant.name.clone(),
                    Vec::<(String, RuntimeValue)>::new(),
                )?);
            }
            VariantFields::Tuple(fields) if fields.is_empty() => {
                out.push(RuntimeValue::enum_value(
                    enum_name.to_string(),
                    variant.name.clone(),
                    Vec::<(String, RuntimeValue)>::new(),
                )?);
            }
            VariantFields::Struct(fields) => {
                let field_domains = fields
                    .iter()
                    .map(|field| {
                        expand_type_domain(
                            &field.ty,
                            schema,
                            model,
                            bounds,
                            expansion_limit,
                            recursion_depth + 1,
                        )
                    })
                    .collect::<TranspileResult<Vec<_>>>()?;

                for tuple in cartesian_values(&field_domains, expansion_limit)? {
                    let named_fields = fields
                        .iter()
                        .zip(tuple.into_iter())
                        .map(|(field, value)| (field.name.clone(), value))
                        .collect::<Vec<_>>();
                    out.push(RuntimeValue::enum_value(
                        enum_name.to_string(),
                        variant.name.clone(),
                        named_fields,
                    )?);
                }
            }
            VariantFields::Tuple(fields) => {
                let field_domains = fields
                    .iter()
                    .map(|field_ty| {
                        expand_type_domain(
                            field_ty,
                            schema,
                            model,
                            bounds,
                            expansion_limit,
                            recursion_depth + 1,
                        )
                    })
                    .collect::<TranspileResult<Vec<_>>>()?;

                for tuple in cartesian_values(&field_domains, expansion_limit)? {
                    let indexed_fields = tuple
                        .into_iter()
                        .enumerate()
                        .map(|(idx, value)| (format!("_{idx}"), value))
                        .collect::<Vec<_>>();
                    out.push(RuntimeValue::enum_value(
                        enum_name.to_string(),
                        variant.name.clone(),
                        indexed_fields,
                    )?);
                }
            }
        }
        if out.len() > expansion_limit {
            return Err(TranspileError::Config {
                message: format!(
                    "Enum domain expansion for `{}` exceeded limit {}.",
                    enum_name, expansion_limit
                ),
            });
        }
    }

    let out = unique_sorted(out);
    if out.is_empty() {
        return Err(TranspileError::Config {
            message: format!("Enum domain expansion for `{}` is empty.", enum_name),
        });
    }

    Ok(out)
}

fn expand_struct_values(
    struct_name: &str,
    struct_def: &StructDef,
    schema: &SpecSchema,
    model: &ModelConfig,
    bounds: &RuntimeCollectionBounds,
    expansion_limit: usize,
    recursion_depth: usize,
) -> TranspileResult<Vec<RuntimeValue>> {
    let mut combinations: Vec<Vec<(String, RuntimeValue)>> = vec![Vec::new()];
    for field in &struct_def.fields {
        let field_values = unique_sorted(expand_type_domain(
            &field.ty,
            schema,
            model,
            bounds,
            expansion_limit,
            recursion_depth + 1,
        )?);
        if field_values.is_empty() {
            return Err(TranspileError::Config {
                message: format!(
                    "Struct domain expansion for `{}` produced an empty domain for field `{}`.",
                    struct_name, field.name
                ),
            });
        }

        let mut next = Vec::new();
        for partial in &combinations {
            for value in &field_values {
                let mut candidate = partial.clone();
                candidate.push((field.name.clone(), value.clone()));
                next.push(candidate);
                if next.len() > expansion_limit {
                    return Err(TranspileError::Config {
                        message: format!(
                            "Struct domain expansion for `{}` exceeded limit {}.",
                            struct_name, expansion_limit
                        ),
                    });
                }
            }
        }
        combinations = next;
    }

    let mut out = Vec::new();
    for fields in combinations {
        out.push(RuntimeValue::struct_value(struct_def.name.clone(), fields).map_err(
            |err| TranspileError::Config {
                message: format!(
                    "Failed to construct runtime struct value for `{}`: {}",
                    struct_name, err
                ),
            },
        )?);
    }
    let out = unique_sorted(out);
    if out.is_empty() {
        return Err(TranspileError::Config {
            message: format!("Struct domain expansion for `{}` is empty.", struct_name),
        });
    }
    Ok(out)
}

fn runtime_from_model_value(
    value: &ModelValue,
    expected_ty: &Type,
) -> TranspileResult<RuntimeValue> {
    match (value, expected_ty) {
        (ModelValue::Bool(v), Type::Bool) => Ok(RuntimeValue::Bool(*v)),
        (ModelValue::Int(v), Type::Int) => Ok(RuntimeValue::Int(i128::from(*v))),
        (ModelValue::Int(v), Type::Nat) if *v >= 0 => Ok(RuntimeValue::Nat(*v as u64)),
        (ModelValue::String(v), Type::Named(_)) => Ok(RuntimeValue::String(v.clone())),
        (ModelValue::Bool(v), Type::Named(_)) => Ok(RuntimeValue::Bool(*v)),
        (ModelValue::Int(v), Type::Named(_)) => Ok(RuntimeValue::Int(i128::from(*v))),
        _ => Err(TranspileError::Config {
            message: format!(
                "Model domain value `{}` is incompatible with expected type `{}`.",
                format_model_value(value),
                format_type_name(expected_ty)
            ),
        }),
    }
}

fn generate_seq_domain(
    elements: &[RuntimeValue],
    max_len: usize,
    expansion_limit: usize,
) -> TranspileResult<Vec<RuntimeValue>> {
    let mut out = Vec::new();
    let mut current = Vec::new();
    generate_seq_values_recursive(elements, max_len, expansion_limit, &mut current, &mut out)?;
    Ok(out)
}

fn generate_seq_values_recursive(
    elements: &[RuntimeValue],
    max_len: usize,
    expansion_limit: usize,
    current: &mut Vec<RuntimeValue>,
    out: &mut Vec<RuntimeValue>,
) -> TranspileResult<()> {
    out.push(RuntimeValue::Seq(current.clone()));
    if out.len() > expansion_limit {
        return Err(TranspileError::Config {
            message: format!(
                "Sequence domain expansion exceeded limit {} assignments/values.",
                expansion_limit
            ),
        });
    }
    if current.len() == max_len {
        return Ok(());
    }
    for elem in elements {
        current.push(elem.clone());
        generate_seq_values_recursive(elements, max_len, expansion_limit, current, out)?;
        current.pop();
    }
    Ok(())
}

fn generate_set_domain(
    elements: &[RuntimeValue],
    max_len: usize,
    expansion_limit: usize,
) -> TranspileResult<Vec<RuntimeValue>> {
    let mut out = Vec::new();
    let mut current = Vec::new();
    generate_set_values_recursive(
        elements,
        max_len,
        expansion_limit,
        0,
        &mut current,
        &mut out,
    )?;
    Ok(out)
}

fn generate_set_values_recursive(
    elements: &[RuntimeValue],
    max_len: usize,
    expansion_limit: usize,
    idx: usize,
    current: &mut Vec<RuntimeValue>,
    out: &mut Vec<RuntimeValue>,
) -> TranspileResult<()> {
    if current.len() <= max_len {
        let set = current.iter().cloned().collect::<BTreeSet<_>>();
        out.push(RuntimeValue::Set(set));
        if out.len() > expansion_limit {
            return Err(TranspileError::Config {
                message: format!(
                    "Set domain expansion exceeded limit {} assignments/values.",
                    expansion_limit
                ),
            });
        }
    }

    if idx >= elements.len() || current.len() == max_len {
        return Ok(());
    }

    for next_idx in idx..elements.len() {
        current.push(elements[next_idx].clone());
        generate_set_values_recursive(
            elements,
            max_len,
            expansion_limit,
            next_idx + 1,
            current,
            out,
        )?;
        current.pop();
    }
    Ok(())
}

fn generate_map_domain(
    keys: &[RuntimeValue],
    values: &[RuntimeValue],
    max_len: usize,
    expansion_limit: usize,
) -> TranspileResult<Vec<RuntimeValue>> {
    let mut out = Vec::new();
    let mut current = BTreeMap::new();
    generate_map_values_recursive(
        keys,
        values,
        max_len,
        expansion_limit,
        0,
        &mut current,
        &mut out,
    )?;
    Ok(out)
}

fn generate_map_values_recursive(
    keys: &[RuntimeValue],
    values: &[RuntimeValue],
    max_len: usize,
    expansion_limit: usize,
    idx: usize,
    current: &mut BTreeMap<RuntimeValue, RuntimeValue>,
    out: &mut Vec<RuntimeValue>,
) -> TranspileResult<()> {
    out.push(RuntimeValue::Map(current.clone()));
    if out.len() > expansion_limit {
        return Err(TranspileError::Config {
            message: format!(
                "Map domain expansion exceeded limit {} assignments/values.",
                expansion_limit
            ),
        });
    }

    if idx >= keys.len() || current.len() == max_len {
        return Ok(());
    }

    generate_map_values_recursive(
        keys,
        values,
        max_len,
        expansion_limit,
        idx + 1,
        current,
        out,
    )?;

    for value in values {
        current.insert(keys[idx].clone(), value.clone());
        generate_map_values_recursive(
            keys,
            values,
            max_len,
            expansion_limit,
            idx + 1,
            current,
            out,
        )?;
        current.remove(&keys[idx]);
    }
    Ok(())
}

fn cartesian_values(
    domains: &[Vec<RuntimeValue>],
    expansion_limit: usize,
) -> TranspileResult<Vec<Vec<RuntimeValue>>> {
    if domains.is_empty() {
        return Ok(vec![Vec::new()]);
    }

    let mut out = vec![Vec::new()];
    for domain in domains {
        let mut next = Vec::new();
        for prefix in &out {
            for value in domain {
                let mut tuple = prefix.clone();
                tuple.push(value.clone());
                next.push(tuple);
                if next.len() > expansion_limit {
                    return Err(TranspileError::Config {
                        message: format!(
                            "Tuple/domain Cartesian expansion exceeded limit {}.",
                            expansion_limit
                        ),
                    });
                }
            }
        }
        out = next;
    }
    Ok(out)
}

fn type_name_candidates(path: &Path) -> Vec<String> {
    let full = path.segments.join("::");
    let mut candidates = vec![full];
    if let Some(last) = path.last() {
        if candidates[0] != last {
            candidates.push(last.to_string());
        }
    }
    candidates
}

fn find_quantifier_domain<'a>(
    model: &'a ModelConfig,
    candidates: &[String],
) -> Option<&'a DomainSpec> {
    for candidate in candidates {
        if let Some(domain) = model.quantifiers.types.get(candidate) {
            return Some(domain);
        }
    }
    None
}

fn find_alias_type<'a>(schema: &'a SpecSchema, candidates: &[String]) -> Option<&'a Type> {
    for candidate in candidates {
        if let Some(alias) = schema.aliases.get(candidate) {
            return Some(&alias.ty);
        }
    }
    None
}

fn find_enum<'a>(schema: &'a SpecSchema, candidates: &[String]) -> Option<(String, &'a EnumDef)> {
    for candidate in candidates {
        if let Some(enum_def) = schema.enums.get(candidate) {
            return Some((candidate.clone(), enum_def));
        }
    }
    None
}

fn find_struct<'a>(
    schema: &'a SpecSchema,
    candidates: &[String],
) -> Option<(String, &'a StructDef)> {
    for candidate in candidates {
        if let Some(struct_def) = schema.structs.get(candidate) {
            return Some((candidate.clone(), struct_def));
        }
    }
    None
}

#[derive(Clone, Copy)]
enum PrimitiveNamedIntegerKind {
    Signed,
    Unsigned,
}

fn primitive_named_integer_kind(candidates: &[String]) -> Option<(String, PrimitiveNamedIntegerKind)> {
    for candidate in candidates {
        let short = candidate.rsplit("::").next().unwrap_or(candidate.as_str());
        let kind = match short {
            "u64" | "u32" | "u16" | "u8" | "usize" => PrimitiveNamedIntegerKind::Unsigned,
            "i64" | "i32" | "i16" | "i8" | "isize" => PrimitiveNamedIntegerKind::Signed,
            _ => continue,
        };
        return Some((short.to_string(), kind));
    }
    None
}

fn expand_primitive_named_integer_domain(
    type_name: &str,
    kind: PrimitiveNamedIntegerKind,
    model: &ModelConfig,
) -> TranspileResult<Vec<RuntimeValue>> {
    match kind {
        PrimitiveNamedIntegerKind::Signed => {
            let range = model
                .quantifiers
                .int
                .as_ref()
                .ok_or_else(|| TranspileError::Config {
                    message: format!(
                        "Missing domain for named type `{}` (signed integer). \
                         Set `quantifiers.int` or provide `quantifiers.types.{}` in model.toml.",
                        type_name, type_name
                    ),
                })?;
            if range.min > range.max {
                return Err(TranspileError::Config {
                    message: format!(
                        "Invalid int domain: min ({}) > max ({}).",
                        range.min, range.max
                    ),
                });
            }
            Ok((range.min..=range.max)
                .map(|v| RuntimeValue::Int(i128::from(v)))
                .collect())
        }
        PrimitiveNamedIntegerKind::Unsigned => {
            let range = model
                .quantifiers
                .nat
                .as_ref()
                .ok_or_else(|| TranspileError::Config {
                    message: format!(
                        "Missing domain for named type `{}` (unsigned integer). \
                         Set `quantifiers.nat` or provide `quantifiers.types.{}` in model.toml.",
                        type_name, type_name
                    ),
                })?;
            Ok((0..=range.max).map(RuntimeValue::Nat).collect())
        }
    }
}

fn unique_sorted(values: Vec<RuntimeValue>) -> Vec<RuntimeValue> {
    let mut set = BTreeSet::new();
    for value in values {
        set.insert(value);
    }
    set.into_iter().collect()
}

fn format_type_name(ty: &Type) -> String {
    match ty {
        Type::Named(path) => path.segments.join("::"),
        Type::Generic(path, args) => {
            let rendered_args = args
                .iter()
                .map(format_type_name)
                .collect::<Vec<_>>()
                .join(", ");
            format!("{}<{}>", path.segments.join("::"), rendered_args)
        }
        Type::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(format_type_name)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::Seq(inner) => format!("Seq<{}>", format_type_name(inner)),
        Type::Set(inner) => format!("Set<{}>", format_type_name(inner)),
        Type::Map(key, value) => format!(
            "Map<{}, {}>",
            format_type_name(key),
            format_type_name(value)
        ),
        Type::Reference { ty, mutable } => {
            if *mutable {
                format!("&mut {}", format_type_name(ty))
            } else {
                format!("&{}", format_type_name(ty))
            }
        }
        Type::Bool => "bool".to_string(),
        Type::Int => "int".to_string(),
        Type::Nat => "nat".to_string(),
        Type::Unit => "()".to_string(),
    }
}

fn format_model_value(value: &ModelValue) -> String {
    match value {
        ModelValue::Bool(v) => format!("{v}"),
        ModelValue::Int(v) => format!("{v}"),
        ModelValue::String(v) => format!("{v:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Path, Type};
    use crate::modelcheck::config::{
        CollectionBounds, DomainSpec, IntDomain, ModelConfig, NatDomain, SearchLimits,
    };
    use crate::modelcheck::ir::{ExistentialVarIr, TransitionBranchIr};
    use crate::spec_analyzer::SpecSchema;
    use crate::types::{EnumDef, FieldDef, StructDef, VariantDef};
    use std::collections::HashMap;

    fn base_model() -> ModelConfig {
        ModelConfig {
            collections: CollectionBounds {
                max_seq_len: 2,
                max_set_len: 2,
                max_map_len: 2,
            },
            search: SearchLimits {
                max_depth: 10,
                max_states: 200,
                timeout_ms: 1_000,
                state_dedup: crate::modelcheck::config::StateDedupMode::Canonical,
                symmetry_fields: Vec::new(),
                por_heuristic: crate::modelcheck::config::PorHeuristic::None,
                candidate_eval_guardrail: 10_000,
            },
            ..Default::default()
        }
    }

    fn mk_branch(vars: Vec<ExistentialVarIr>) -> TransitionBranchIr {
        TransitionBranchIr {
            label: "branch_0".to_string(),
            existential_vars: vars,
            constraints: vec![],
        }
    }

    fn mk_enum_schema(enum_name: &str, variants: &[&str]) -> SpecSchema {
        let mut schema = SpecSchema::new();
        schema.enums.insert(
            enum_name.to_string(),
            EnumDef {
                name: enum_name.to_string(),
                generics: Default::default(),
                variants: variants
                    .iter()
                    .map(|name| VariantDef {
                        name: (*name).to_string(),
                        fields: VariantFields::Unit,
                    })
                    .collect(),
                is_spec: true,
            },
        );
        schema.enum_order.push(enum_name.to_string());
        schema
    }

    fn mk_struct_schema(struct_name: &str, fields: Vec<(&str, Type)>) -> SpecSchema {
        let mut schema = SpecSchema::new();
        schema.structs.insert(
            struct_name.to_string(),
            StructDef {
                name: struct_name.to_string(),
                generics: Default::default(),
                fields: fields
                    .into_iter()
                    .map(|(name, ty)| FieldDef {
                        name: name.to_string(),
                        ty,
                        is_public: false,
                    })
                    .collect(),
                is_spec: true,
            },
        );
        schema.struct_order.push(struct_name.to_string());
        schema
    }

    #[test]
    fn test_expand_branch_existentials_int_nat_bool() {
        let mut model = base_model();
        model.quantifiers.int = Some(IntDomain { min: -1, max: 1 });
        model.quantifiers.nat = Some(crate::modelcheck::config::NatDomain { max: 1 });

        let branch = mk_branch(vec![
            ExistentialVarIr {
                name: "i".to_string(),
                ty: Some(Type::Int),
            },
            ExistentialVarIr {
                name: "n".to_string(),
                ty: Some(Type::Nat),
            },
            ExistentialVarIr {
                name: "b".to_string(),
                ty: Some(Type::Bool),
            },
        ]);

        let assignments = expand_branch_existentials(&branch, &SpecSchema::new(), &model).unwrap();
        assert_eq!(assignments.len(), 12); // 3 * 2 * 2
        assert!(assignments.iter().all(|a| a.contains_key("i")));
        assert!(assignments.iter().all(|a| a.contains_key("n")));
        assert!(assignments.iter().all(|a| a.contains_key("b")));
    }

    #[test]
    fn test_expand_branch_existentials_enum_subset() {
        let mut model = base_model();
        model.quantifiers.types.insert(
            "LRole".to_string(),
            DomainSpec::EnumSubset {
                variants: vec!["Leader".to_string(), "Follower".to_string()],
            },
        );
        let schema = mk_enum_schema("LRole", &["Follower", "Leader", "Candidate"]);
        let branch = mk_branch(vec![ExistentialVarIr {
            name: "role".to_string(),
            ty: Some(Type::Named(Path::single("LRole".to_string()))),
        }]);

        let assignments = expand_branch_existentials(&branch, &schema, &model).unwrap();
        assert_eq!(assignments.len(), 2);
        let values: Vec<String> = assignments
            .iter()
            .map(|a| a.get("role").unwrap().canonical_key())
            .collect();
        assert!(values.iter().any(|v| v.contains("Leader")));
        assert!(values.iter().any(|v| v.contains("Follower")));
    }

    #[test]
    fn test_expand_branch_existentials_seq_domain_from_int_range() {
        let mut model = base_model();
        model.quantifiers.int = Some(IntDomain { min: 0, max: 1 });

        let branch = mk_branch(vec![ExistentialVarIr {
            name: "xs".to_string(),
            ty: Some(Type::Seq(Box::new(Type::Int))),
        }]);

        let assignments = expand_branch_existentials(&branch, &SpecSchema::new(), &model).unwrap();
        assert_eq!(assignments.len(), 7); // len<=2 over {0,1}: 1 + 2 + 4
        assert!(assignments
            .iter()
            .any(|a| matches!(a.get("xs"), Some(RuntimeValue::Seq(v)) if v.is_empty())));
    }

    #[test]
    fn test_expand_branch_existentials_errors_on_missing_int_domain() {
        let model = base_model();
        let branch = mk_branch(vec![ExistentialVarIr {
            name: "i".to_string(),
            ty: Some(Type::Int),
        }]);

        let err = expand_branch_existentials(&branch, &SpecSchema::new(), &model).unwrap_err();
        assert!(err.to_string().contains("Missing domain for `int`"));
    }

    #[test]
    fn test_expand_branch_existentials_errors_on_unknown_enum_variant() {
        let mut model = base_model();
        model.quantifiers.types.insert(
            "LRole".to_string(),
            DomainSpec::EnumSubset {
                variants: vec!["Unknown".to_string()],
            },
        );
        let schema = mk_enum_schema("LRole", &["Follower", "Leader"]);
        let branch = mk_branch(vec![ExistentialVarIr {
            name: "role".to_string(),
            ty: Some(Type::Named(Path::single("LRole".to_string()))),
        }]);

        let err = expand_branch_existentials(&branch, &schema, &model).unwrap_err();
        assert!(err.to_string().contains("unknown variant"));
    }

    #[test]
    fn test_expand_branch_existentials_enforces_assignment_limit() {
        let mut model = base_model();
        model.search.max_states = 3;
        model.quantifiers.int = Some(IntDomain { min: 0, max: 3 });

        let branch = mk_branch(vec![ExistentialVarIr {
            name: "i".to_string(),
            ty: Some(Type::Int),
        }]);

        let err = expand_branch_existentials(&branch, &SpecSchema::new(), &model).unwrap_err();
        assert!(err.to_string().contains("exceeded limit"));
    }

    #[test]
    fn test_expand_branch_existentials_alias_domain() {
        let mut model = base_model();
        model.quantifiers.int = Some(IntDomain { min: 2, max: 3 });
        let mut schema = SpecSchema::new();
        schema.aliases.insert(
            "LNodeId".to_string(),
            crate::types::TypeAlias {
                name: "LNodeId".to_string(),
                generics: Default::default(),
                ty: Type::Int,
            },
        );
        schema.alias_order.push("LNodeId".to_string());

        let branch = mk_branch(vec![ExistentialVarIr {
            name: "id".to_string(),
            ty: Some(Type::Named(Path::single("LNodeId".to_string()))),
        }]);

        let assignments = expand_branch_existentials(&branch, &schema, &model).unwrap();
        assert_eq!(assignments.len(), 2);
    }

    #[test]
    fn test_expand_branch_existentials_named_unsigned_primitive_uses_nat_domain() {
        let mut model = base_model();
        model.quantifiers.nat = Some(NatDomain { max: 2 });
        let branch = mk_branch(vec![ExistentialVarIr {
            name: "id".to_string(),
            ty: Some(Type::Named(Path::single("u64".to_string()))),
        }]);

        let assignments = expand_branch_existentials(&branch, &SpecSchema::new(), &model).unwrap();
        assert_eq!(assignments.len(), 3);
        assert!(assignments
            .iter()
            .any(|a| a.get("id") == Some(&RuntimeValue::Nat(0))));
        assert!(assignments
            .iter()
            .any(|a| a.get("id") == Some(&RuntimeValue::Nat(1))));
        assert!(assignments
            .iter()
            .any(|a| a.get("id") == Some(&RuntimeValue::Nat(2))));
    }

    #[test]
    fn test_expand_branch_existentials_named_signed_primitive_uses_int_domain() {
        let mut model = base_model();
        model.quantifiers.int = Some(IntDomain { min: -1, max: 1 });
        let branch = mk_branch(vec![ExistentialVarIr {
            name: "term".to_string(),
            ty: Some(Type::Named(Path::single("i64".to_string()))),
        }]);

        let assignments = expand_branch_existentials(&branch, &SpecSchema::new(), &model).unwrap();
        assert_eq!(assignments.len(), 3);
        assert!(assignments
            .iter()
            .any(|a| a.get("term") == Some(&RuntimeValue::Int(-1))));
        assert!(assignments
            .iter()
            .any(|a| a.get("term") == Some(&RuntimeValue::Int(0))));
        assert!(assignments
            .iter()
            .any(|a| a.get("term") == Some(&RuntimeValue::Int(1))));
    }

    #[test]
    fn test_expand_branch_existentials_named_primitive_prefers_explicit_override() {
        let mut model = base_model();
        model.quantifiers.nat = Some(NatDomain { max: 1 });
        model.quantifiers.types.insert(
            "u64".to_string(),
            DomainSpec::IntRange { min: 7, max: 7 },
        );
        let branch = mk_branch(vec![ExistentialVarIr {
            name: "id".to_string(),
            ty: Some(Type::Named(Path::single("u64".to_string()))),
        }]);

        let assignments = expand_branch_existentials(&branch, &SpecSchema::new(), &model).unwrap();
        assert_eq!(assignments.len(), 1);
        assert_eq!(
            assignments[0].get("id"),
            Some(&RuntimeValue::Int(7)),
            "explicit quantifiers.types override should win over primitive fallback"
        );
    }

    #[test]
    fn test_expand_branch_existentials_map_domain() {
        let mut model = base_model();
        model.quantifiers.int = Some(IntDomain { min: 0, max: 1 });
        model.quantifiers.types = HashMap::new();
        let branch = mk_branch(vec![ExistentialVarIr {
            name: "m".to_string(),
            ty: Some(Type::Map(Box::new(Type::Int), Box::new(Type::Bool))),
        }]);

        let assignments = expand_branch_existentials(&branch, &SpecSchema::new(), &model).unwrap();
        assert!(!assignments.is_empty());
        assert!(assignments
            .iter()
            .all(|a| matches!(a.get("m"), Some(RuntimeValue::Map(_)))));
    }

    #[test]
    fn test_expand_branch_existentials_reference_and_generic_seq_domain() {
        let mut model = base_model();
        model.quantifiers.int = Some(IntDomain { min: 0, max: 1 });

        let branch = mk_branch(vec![
            ExistentialVarIr {
                name: "r".to_string(),
                ty: Some(Type::Reference {
                    ty: Box::new(Type::Int),
                    mutable: false,
                }),
            },
            ExistentialVarIr {
                name: "xs".to_string(),
                ty: Some(Type::Generic(
                    Path::single("Seq".to_string()),
                    vec![Type::Bool],
                )),
            },
        ]);

        let assignments = expand_branch_existentials(&branch, &SpecSchema::new(), &model).unwrap();
        assert_eq!(assignments.len(), 14); // 2 int choices * 7 seq<bool> choices (len<=2)
        assert!(assignments.iter().all(|a| a.contains_key("r")));
        assert!(assignments.iter().all(|a| a.contains_key("xs")));
    }

    #[test]
    fn test_expand_branch_existentials_named_values_override_without_schema_type() {
        let mut model = base_model();
        model.quantifiers.types.insert(
            "NodeId".to_string(),
            DomainSpec::Values {
                values: vec![ModelValue::Int(5), ModelValue::Int(8)],
            },
        );

        let branch = mk_branch(vec![ExistentialVarIr {
            name: "id".to_string(),
            ty: Some(Type::Named(Path::single("NodeId".to_string()))),
        }]);

        let assignments = expand_branch_existentials(&branch, &SpecSchema::new(), &model).unwrap();
        assert_eq!(assignments.len(), 2);
        assert!(assignments
            .iter()
            .any(|a| a.get("id") == Some(&RuntimeValue::Int(5))));
        assert!(assignments
            .iter()
            .any(|a| a.get("id") == Some(&RuntimeValue::Int(8))));
    }

    #[test]
    fn test_expand_branch_existentials_missing_named_domain_has_actionable_error() {
        let model = base_model();
        let branch = mk_branch(vec![ExistentialVarIr {
            name: "x".to_string(),
            ty: Some(Type::Named(Path::single("UnknownType".to_string()))),
        }]);

        let err = expand_branch_existentials(&branch, &SpecSchema::new(), &model).unwrap_err();
        assert!(err
            .to_string()
            .contains("Missing domain for named type `UnknownType`"));
    }

    #[test]
    fn test_expand_branch_existentials_named_struct_without_override_uses_schema_fields() {
        let mut model = base_model();
        model.quantifiers.int = Some(IntDomain { min: 0, max: 0 });
        let schema = mk_struct_schema(
            "LLogEntry",
            vec![("term", Type::Int), ("value", Type::Int)],
        );
        let branch = mk_branch(vec![ExistentialVarIr {
            name: "entry".to_string(),
            ty: Some(Type::Named(Path::single("LLogEntry".to_string()))),
        }]);

        let assignments = expand_branch_existentials(&branch, &schema, &model).unwrap();
        assert_eq!(assignments.len(), 1);
        assert!(assignments.iter().any(|a| {
            a.get("entry")
                == Some(
                    &RuntimeValue::struct_value(
                        "LLogEntry".to_string(),
                        vec![
                            ("term".to_string(), RuntimeValue::Int(0)),
                            ("value".to_string(), RuntimeValue::Int(0)),
                        ],
                    )
                    .unwrap(),
                )
        }));
    }

    #[test]
    fn test_expand_branch_existentials_seq_of_named_struct_without_override() {
        let mut model = base_model();
        model.quantifiers.int = Some(IntDomain { min: 0, max: 0 });
        model.collections.max_seq_len = 1;
        let schema = mk_struct_schema("LLogEntry", vec![("term", Type::Int)]);
        let branch = mk_branch(vec![ExistentialVarIr {
            name: "log".to_string(),
            ty: Some(Type::Seq(Box::new(Type::Named(Path::single(
                "LLogEntry".to_string(),
            ))))),
        }]);

        let assignments = expand_branch_existentials(&branch, &schema, &model).unwrap();
        assert_eq!(assignments.len(), 2, "expected empty + single-entry sequences");
        assert!(assignments.iter().any(
            |a| matches!(a.get("log"), Some(RuntimeValue::Seq(values)) if values.is_empty())
        ));
        assert!(assignments.iter().any(|a| {
            matches!(
                a.get("log"),
                Some(RuntimeValue::Seq(values)) if values.len() == 1
            )
        }));
    }

    #[test]
    fn test_expand_branch_existentials_supports_payload_enum_variants() {
        let mut model = base_model();
        model.quantifiers.int = Some(IntDomain { min: 0, max: 1 });
        model.quantifiers.types.insert(
            "LRole".to_string(),
            DomainSpec::EnumSubset {
                variants: vec!["Leader".to_string()],
            },
        );

        let mut schema = SpecSchema::new();
        schema.enums.insert(
            "LRole".to_string(),
            EnumDef {
                name: "LRole".to_string(),
                generics: Default::default(),
                variants: vec![VariantDef {
                    name: "Leader".to_string(),
                    fields: VariantFields::Tuple(vec![Type::Int]),
                }],
                is_spec: true,
            },
        );
        schema.enum_order.push("LRole".to_string());

        let branch = mk_branch(vec![ExistentialVarIr {
            name: "role".to_string(),
            ty: Some(Type::Named(Path::single("LRole".to_string()))),
        }]);

        let assignments = expand_branch_existentials(&branch, &schema, &model).unwrap();
        assert_eq!(assignments.len(), 2);
        assert!(assignments.iter().any(|a| {
            a.get("role")
                == Some(
                    &RuntimeValue::enum_value(
                        "LRole".to_string(),
                        "Leader".to_string(),
                        vec![("_0".to_string(), RuntimeValue::Int(0))],
                    )
                    .unwrap(),
                )
        }));
        assert!(assignments.iter().any(|a| {
            a.get("role")
                == Some(
                    &RuntimeValue::enum_value(
                        "LRole".to_string(),
                        "Leader".to_string(),
                        vec![("_0".to_string(), RuntimeValue::Int(1))],
                    )
                    .unwrap(),
                )
        }));
    }
}
