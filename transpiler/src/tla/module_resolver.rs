//! Module resolution (Phase 55.1.a): `EXTENDS` and `INSTANCE` become one module.
//!
//! The parser has always recorded module composition — [`TlaInstance`] carries
//! the local name, the module name and the `WITH` substitutions, and `V!Op`
//! parses with its qualified name kept whole — but nothing ever *loaded* the
//! referenced file. Every pass downstream therefore saw a composition module as
//! a spec with no operators: linting Jetpack's composition reported "3 of 5
//! implemented rules did not run", because with `B!RequestVote` unresolvable
//! the node set could not be identified.
//!
//! This module closes that. Given a root `.tla` path it loads the referenced
//! modules from the same directory and returns a single flattened
//! [`TlaModule`] that the linter, projection and emitter can consume unchanged.
//!
//! ## What the two forms mean
//!
//! - **`EXTENDS Foo`** — Foo's declarations become the parent's, unprefixed. A
//!   name defined in both is the parent's; TLA+ would reject the clash, and
//!   refusing here would break specs that legitimately re-state a definition.
//! - **`V == INSTANCE Foo WITH p <- e`** — Foo's *operators* become `V!name`.
//!   Inside those bodies, references to Foo's own operators are rewritten to
//!   the prefix as well, so `V!A` calling `B` becomes `V!A` calling `V!B`.
//!   Substituted parameters are replaced by their expressions.
//!
//! ## Why variables are shared rather than renamed
//!
//! `INSTANCE` in TLA+ substitutes the instantiated module's variables; anything
//! left unsubstituted refers to the *enclosing* module's variable of the same
//! name. That sharing is the whole mechanism by which Jetpack's composition
//! works — `base_raft` and `jetpack` both operate on `currentTerm`, `log` and
//! `messages`, which the composition declares once. So a resolved instance
//! contributes its operators, and contributes variables and constants only when
//! the parent has not declared them.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use crate::tla::ast::{TlaExpr, TlaModule, TlaOperator, TlaQuantBound};
use crate::tla::parser::parse_module;

/// Modules that ship with TLA+ and have no file to load.
const STANDARD_MODULES: &[&str] = &[
    "Integers",
    "Naturals",
    "Reals",
    "Sequences",
    "FiniteSets",
    "Bags",
    "TLC",
    "TLAPS",
    "Randomization",
    "RealTime",
    "Json",
];

#[derive(Debug)]
pub enum ResolveError {
    /// A referenced module is neither standard nor present beside the root.
    Missing {
        module: String,
        referenced_by: String,
        looked_in: PathBuf,
    },
    /// `A` extends `B` extends `A`.
    Cycle(Vec<String>),
    Io(String),
    Parse {
        module: String,
        message: String,
    },
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResolveError::Missing {
                module,
                referenced_by,
                looked_in,
            } => write!(
                f,
                "`{referenced_by}` references module `{module}`, which is not a \
                 standard module and was not found at {}",
                looked_in.display()
            ),
            ResolveError::Cycle(chain) => {
                write!(f, "module cycle: {}", chain.join(" -> "))
            }
            ResolveError::Io(e) => write!(f, "{e}"),
            ResolveError::Parse { module, message } => {
                write!(f, "in module `{module}`: {message}")
            }
        }
    }
}

/// Parse `path` and flatten everything it `EXTENDS` or `INSTANCE`s into it.
///
/// Resolution is relative to the root file's own directory, which is where TLA+
/// tooling looks and where a corpus case keeps its modules.
pub fn resolve_module_file(path: &Path) -> Result<TlaModule, ResolveError> {
    let source = std::fs::read_to_string(path)
        .map_err(|e| ResolveError::Io(format!("{}: {e}", path.display())))?;
    let root = parse_module(&source).map_err(|e| ResolveError::Parse {
        module: path.display().to_string(),
        message: e.to_string(),
    })?;
    let dir = path
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf();
    let mut seen = Vec::new();
    resolve(root, &dir, &mut seen)
}

/// Whether a module has anything to resolve. Callers that want to avoid the
/// filesystem for self-contained specs can check this first.
pub fn needs_resolution(module: &TlaModule) -> bool {
    !module.instances.is_empty()
        || module
            .extends
            .iter()
            .any(|m| !STANDARD_MODULES.contains(&m.as_str()))
}

fn resolve(
    mut module: TlaModule,
    dir: &Path,
    seen: &mut Vec<String>,
) -> Result<TlaModule, ResolveError> {
    if seen.contains(&module.name) {
        let mut chain = seen.clone();
        chain.push(module.name.clone());
        return Err(ResolveError::Cycle(chain));
    }
    seen.push(module.name.clone());

    // EXTENDS first: an instantiated module may rely on a definition the parent
    // picked up by extending something else.
    let extends: Vec<String> = module
        .extends
        .iter()
        .filter(|m| !STANDARD_MODULES.contains(&m.as_str()))
        .cloned()
        .collect();
    for name in extends {
        let child = load(&name, &module.name, dir, seen)?;
        merge_extends(&mut module, child);
    }

    let instances = std::mem::take(&mut module.instances);
    for instance in &instances {
        if STANDARD_MODULES.contains(&instance.module_name.as_str()) {
            continue;
        }
        let child = load(&instance.module_name, &module.name, dir, seen)?;
        merge_instance(&mut module, child, instance);
    }
    // Keep the records: a later pass may want to know the spec was composed.
    module.instances = instances;

    seen.pop();
    Ok(module)
}

fn load(
    name: &str,
    referenced_by: &str,
    dir: &Path,
    seen: &mut Vec<String>,
) -> Result<TlaModule, ResolveError> {
    let path = dir.join(format!("{name}.tla"));
    if !path.exists() {
        return Err(ResolveError::Missing {
            module: name.to_string(),
            referenced_by: referenced_by.to_string(),
            looked_in: path,
        });
    }
    let source = std::fs::read_to_string(&path)
        .map_err(|e| ResolveError::Io(format!("{}: {e}", path.display())))?;
    let child = parse_module(&source).map_err(|e| ResolveError::Parse {
        module: name.to_string(),
        message: e.to_string(),
    })?;
    resolve(child, dir, seen)
}

/// `EXTENDS Foo`: Foo's declarations become the parent's, unprefixed.
fn merge_extends(parent: &mut TlaModule, child: TlaModule) {
    for c in child.constants {
        if !parent.constants.iter().any(|p| p.name == c.name) {
            parent.constants.push(c);
        }
    }
    for v in child.variables {
        if !parent.variables.contains(&v) {
            parent.variables.push(v);
        }
    }
    for op in child.operators {
        // The parent wins: a spec that re-states a definition means the local
        // one, and rejecting the clash would be stricter than TLA+ tooling is
        // in practice.
        if !parent.operators.iter().any(|p| p.name == op.name) {
            parent.operators.push(op);
        }
    }
    parent.assumptions.extend(child.assumptions);
}

/// `V == INSTANCE Foo WITH p <- e`: Foo's operators become `V!name`.
fn merge_instance(
    parent: &mut TlaModule,
    child: TlaModule,
    instance: &crate::tla::ast::TlaInstance,
) {
    let prefix = instance.local_name.clone();
    let subst: BTreeMap<String, TlaExpr> = instance.substitutions.iter().cloned().collect();

    // Every name defined *inside* the instantiated module has to be rewritten
    // when a prefix is in play, so `V!A` calling `B` calls `V!B`.
    let local_names: BTreeSet<String> = child.operators.iter().map(|o| o.name.clone()).collect();

    for op in &child.operators {
        let qualified = match &prefix {
            Some(p) => format!("{p}!{}", op.name),
            None => op.name.clone(),
        };
        if parent.operators.iter().any(|p| p.name == qualified) {
            continue;
        }
        let params: BTreeSet<String> = op.params.iter().map(|p| p.name.clone()).collect();
        let body = rewrite(&op.body, &subst, &local_names, &params, prefix.as_deref());
        parent.operators.push(TlaOperator {
            name: qualified,
            params: op.params.clone(),
            body,
            span: op.span,
            ..op.clone()
        });
    }

    // Unsubstituted variables and constants are shared with the parent -- that
    // is what `INSTANCE` means, and it is why the Jetpack composition works:
    // `base_raft` and `jetpack` both act on variables the composition declares.
    // A declared name of the instantiated module counts as substituted when the
    // parent *defines* it, not only when a `WITH` clause names it. TLA+'s
    // implicit substitution is exactly this: `INSTANCE M` requires every
    // declared name of `M` to be defined in the instantiating context, and a
    // same-named definition serves as the substitution.
    //
    // Paxos is the case that shows the cost of missing it: `Consensus` declares
    // `VARIABLE chosen`, `Voting` substitutes it with its own definition
    // `chosen == {v \in Value : ...}` and never writes a `WITH`. Treating it as
    // unsubstituted made `chosen` a variable of Paxos, and C1 then reported a
    // global that does not exist.
    fn defined_by(parent: &TlaModule, name: &str) -> bool {
        parent.variables.iter().any(|v| v == name)
            || parent.operators.iter().any(|o| o.name == name)
            || parent.constants.iter().any(|c| c.name == name)
    }
    for v in child.variables {
        if !subst.contains_key(&v) && !defined_by(parent, &v) {
            parent.variables.push(v);
        }
    }
    for c in child.constants {
        if !subst.contains_key(&c.name) && !defined_by(parent, &c.name) {
            parent.constants.push(c);
        }
    }
}

/// Apply `WITH` substitutions and qualify references to the module's own names.
///
/// A parameter of the operator being rewritten shadows both: `Op(x) == x + p`
/// under `WITH x <- 1` must keep `x` as the parameter.
fn rewrite(
    expr: &TlaExpr,
    subst: &BTreeMap<String, TlaExpr>,
    local: &BTreeSet<String>,
    shadowed: &BTreeSet<String>,
    prefix: Option<&str>,
) -> TlaExpr {
    let go = |e: &TlaExpr, shadowed: &BTreeSet<String>| rewrite(e, subst, local, shadowed, prefix);
    match expr {
        TlaExpr::Ident(name) => {
            if shadowed.contains(name) {
                return expr.clone();
            }
            if let Some(replacement) = subst.get(name) {
                return replacement.clone();
            }
            match (prefix, local.contains(name)) {
                (Some(p), true) => TlaExpr::Ident(format!("{p}!{name}")),
                _ => expr.clone(),
            }
        }
        TlaExpr::Prime(inner) => TlaExpr::Prime(Box::new(go(inner, shadowed))),
        TlaExpr::BinOp { op, left, right } => TlaExpr::BinOp {
            op: *op,
            left: Box::new(go(left, shadowed)),
            right: Box::new(go(right, shadowed)),
        },
        TlaExpr::UnaryOp { op, operand } => TlaExpr::UnaryOp {
            op: *op,
            operand: Box::new(go(operand, shadowed)),
        },
        TlaExpr::OpApply { op, args } => TlaExpr::OpApply {
            op: Box::new(go(op, shadowed)),
            args: args.iter().map(|a| go(a, shadowed)).collect(),
        },
        TlaExpr::FnApply { func, arg } => TlaExpr::FnApply {
            func: Box::new(go(func, shadowed)),
            arg: Box::new(go(arg, shadowed)),
        },
        TlaExpr::Record(fields) => TlaExpr::Record(
            fields
                .iter()
                .map(|(n, v)| (n.clone(), go(v, shadowed)))
                .collect(),
        ),
        TlaExpr::RecordSet(fields) => TlaExpr::RecordSet(
            fields
                .iter()
                .map(|(n, v)| (n.clone(), go(v, shadowed)))
                .collect(),
        ),
        TlaExpr::RecordAccess { record, field } => TlaExpr::RecordAccess {
            record: Box::new(go(record, shadowed)),
            field: field.clone(),
        },
        TlaExpr::SetEnum(items) => {
            TlaExpr::SetEnum(items.iter().map(|i| go(i, shadowed)).collect())
        }
        TlaExpr::Tuple(items) => TlaExpr::Tuple(items.iter().map(|i| go(i, shadowed)).collect()),
        TlaExpr::IfThenElse {
            cond,
            then_expr,
            else_expr,
        } => TlaExpr::IfThenElse {
            cond: Box::new(go(cond, shadowed)),
            then_expr: Box::new(go(then_expr, shadowed)),
            else_expr: Box::new(go(else_expr, shadowed)),
        },
        // `CASE` branches like `IF`, and its arms are ordinary expressions of
        // the instantiated module. Without this arm the whole CASE fell to the
        // catch-all clone below, so references to the module's *own*
        // definitions kept their bare names while every other position was
        // qualified: base Raft's `CASE m.mresult = Ok -> ..` stayed `Ok` where
        // `<<Ok, 2>>` two lines away became `<<B!Ok, 2>>`. `Ok` then resolves
        // to no operator, and the guard projects to a bare `Ok` -- a name the
        // emitted spec never declares.
        TlaExpr::Case { arms, other } => TlaExpr::Case {
            arms: arms
                .iter()
                .map(|(cond, result)| (go(cond, shadowed), go(result, shadowed)))
                .collect(),
            other: other.as_ref().map(|e| Box::new(go(e, shadowed))),
        },
        TlaExpr::Unchanged(items) => {
            TlaExpr::Unchanged(items.iter().map(|i| go(i, shadowed)).collect())
        }
        // Binders shadow: the bound name is not the instantiated module's.
        TlaExpr::Forall { vars, body } | TlaExpr::Exists { vars, body } => {
            let mut inner = shadowed.clone();
            for b in vars {
                inner.insert(b.var.clone());
            }
            let vars: Vec<TlaQuantBound> = vars
                .iter()
                .map(|b| TlaQuantBound {
                    var: b.var.clone(),
                    set: b.set.as_ref().map(|s| go(s, shadowed)),
                })
                .collect();
            let body = Box::new(rewrite(body, subst, local, &inner, prefix));
            if matches!(expr, TlaExpr::Forall { .. }) {
                TlaExpr::Forall { vars, body }
            } else {
                TlaExpr::Exists { vars, body }
            }
        }
        TlaExpr::Choose { var, set, body } => {
            let mut inner = shadowed.clone();
            inner.insert(var.clone());
            TlaExpr::Choose {
                var: var.clone(),
                set: set.as_ref().map(|s| Box::new(go(s, shadowed))),
                body: Box::new(rewrite(body, subst, local, &inner, prefix)),
            }
        }
        TlaExpr::SetMap { expr: e, var, set } => {
            let mut inner = shadowed.clone();
            inner.insert(var.clone());
            TlaExpr::SetMap {
                expr: Box::new(rewrite(e, subst, local, &inner, prefix)),
                var: var.clone(),
                set: Box::new(go(set, shadowed)),
            }
        }
        TlaExpr::SetMapMulti { expr: e, bindings } => {
            let mut inner = shadowed.clone();
            for b in bindings {
                inner.insert(b.var.clone());
            }
            TlaExpr::SetMapMulti {
                expr: Box::new(rewrite(e, subst, local, &inner, prefix)),
                bindings: bindings
                    .iter()
                    .map(|b| TlaQuantBound {
                        var: b.var.clone(),
                        set: b.set.as_ref().map(|s| go(s, shadowed)),
                    })
                    .collect(),
            }
        }
        TlaExpr::SetFilter { var, set, filter } => {
            let mut inner = shadowed.clone();
            inner.insert(var.clone());
            TlaExpr::SetFilter {
                var: var.clone(),
                set: Box::new(go(set, shadowed)),
                filter: Box::new(rewrite(filter, subst, local, &inner, prefix)),
            }
        }
        TlaExpr::FnConstruct { var, domain, body } => {
            let mut inner = shadowed.clone();
            inner.insert(var.clone());
            TlaExpr::FnConstruct {
                var: var.clone(),
                domain: Box::new(go(domain, shadowed)),
                body: Box::new(rewrite(body, subst, local, &inner, prefix)),
            }
        }
        TlaExpr::FnSet { domain, range } => TlaExpr::FnSet {
            domain: Box::new(go(domain, shadowed)),
            range: Box::new(go(range, shadowed)),
        },
        TlaExpr::FnExcept { func, updates } => TlaExpr::FnExcept {
            func: Box::new(go(func, shadowed)),
            updates: updates
                .iter()
                .map(|u| crate::tla::ast::TlaExceptUpdate {
                    path: u.path.clone(),
                    value: go(&u.value, shadowed),
                })
                .collect(),
        },
        TlaExpr::Lambda { params, body } => {
            let mut inner = shadowed.clone();
            for p in params {
                inner.insert(p.clone());
            }
            TlaExpr::Lambda {
                params: params.clone(),
                body: Box::new(rewrite(body, subst, local, &inner, prefix)),
            }
        }
        other => other.clone(),
    }
}
