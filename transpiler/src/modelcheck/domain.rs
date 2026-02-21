use crate::ast::{Path, Type};
use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::config::{DomainSpec, ModelConfig, ModelValue};
use crate::modelcheck::ir::TransitionBranchIr;
use crate::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue};
use crate::spec_analyzer::SpecSchema;
use crate::types::{EnumDef, VariantFields};
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
        return expand_named_domain_override(path, schema, domain, model, bounds, expansion_limit);
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
            model,
            bounds,
            expansion_limit,
        );
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
) -> TranspileResult<Vec<RuntimeValue>> {
    if let Some((enum_name, enum_def)) = find_enum(schema, &type_name_candidates(path)) {
        return expand_enum_variants(
            &enum_name,
            enum_def,
            Some(domain),
            model,
            bounds,
            expansion_limit,
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
    model: &ModelConfig,
    bounds: &RuntimeCollectionBounds,
    expansion_limit: usize,
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

        let value = match &variant.fields {
            VariantFields::Unit => RuntimeValue::enum_value(
                enum_name.to_string(),
                variant.name.clone(),
                Vec::<(String, RuntimeValue)>::new(),
            )?,
            VariantFields::Struct(fields) if fields.is_empty() => RuntimeValue::enum_value(
                enum_name.to_string(),
                variant.name.clone(),
                Vec::<(String, RuntimeValue)>::new(),
            )?,
            VariantFields::Tuple(fields) if fields.is_empty() => RuntimeValue::enum_value(
                enum_name.to_string(),
                variant.name.clone(),
                Vec::<(String, RuntimeValue)>::new(),
            )?,
            _ => {
                return Err(TranspileError::UnsupportedPattern {
                    message: format!(
                        "existential enum expansion for `{}` variant `{}` with payload fields",
                        enum_name, variant.name
                    ),
                    span: None,
                    help: Some(
                        "Use payload-free enum variants for existential domains in MVP."
                            .to_string(),
                    ),
                });
            }
        };
        out.push(value);
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

    // Touch arguments so future payload-aware enum support can compose bounds/model.
    let _ = (model, bounds);
    Ok(out)
}

fn runtime_from_model_value(value: &ModelValue, expected_ty: &Type) -> TranspileResult<RuntimeValue> {
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
    generate_seq_values_recursive(
        elements,
        max_len,
        expansion_limit,
        &mut current,
        &mut out,
    )?;
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
    generate_set_values_recursive(elements, max_len, expansion_limit, 0, &mut current, &mut out)?;
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

    generate_map_values_recursive(keys, values, max_len, expansion_limit, idx + 1, current, out)?;

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

fn find_quantifier_domain<'a>(model: &'a ModelConfig, candidates: &[String]) -> Option<&'a DomainSpec> {
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
        CollectionBounds, DomainSpec, IntDomain, ModelConfig, SearchLimits,
    };
    use crate::modelcheck::ir::{ExistentialVarIr, TransitionBranchIr};
    use crate::spec_analyzer::SpecSchema;
    use crate::types::{EnumDef, VariantDef};
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
}
