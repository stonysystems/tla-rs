#!/usr/bin/env python3
"""
Generate a TLC wrapper module for parameterized Init(s, c) / Next(s, s_, c) specs.

Strategy: inline the bodies of Init, each action, and each invariant with the
substitution `s.field → field` (current state), `s_.field → field'` (next
state), and `c.f → <config assignment>`.  Bounded existentials replace `Int`
/ `Seq(AbstractType)` with finite ranges from the DPOR model config.

Usage:
  ./generate_parameterized_mc_wrapper.py \
    --tla-file tests/tla/14_leader_election_small/Election.tla \
    --model-config tests/model_configs/14_leader_election_small.toml \
    --invariant-name SafetyElectingSubsetAlive \
    --out-file tests/tla/14_leader_election_small/Election_MC.tla

Output: writes the wrapper to --out-file and prints module/init/next/invariant
names to stdout (for the shell runner to consume).
"""

import argparse
import re
import sys
from pathlib import Path


def parse_operators(src):
    """Extract (name, params, body) tuples for top-level operators.

    Operator bodies are terminated by the next top-level operator or EOF.
    """
    ops = []
    # Match `Name(params) ==` or `Name ==` at line start
    pattern = re.compile(
        r"^(\w+)\s*(?:\(([^)]*)\))?\s*==\s*(.+?)(?=^\w+\s*(?:\([^)]*\))?\s*==|\Z)",
        re.MULTILINE | re.DOTALL,
    )
    for m in pattern.finditer(src):
        name = m.group(1)
        params_str = m.group(2) or ""
        body = m.group(3).strip()
        params = [p.strip() for p in params_str.split(",") if p.strip()]
        # Strip trailing `====` line and comments
        body = re.sub(r"^====+.*", "", body, flags=re.MULTILINE).strip()
        ops.append((name, params, body))
    return ops


def parse_header(src):
    mod_m = re.search(r"^----+\s*MODULE\s+(\w+)\s*----+", src, re.MULTILINE)
    module_name = mod_m.group(1) if mod_m else None
    const_m = re.search(r"^CONSTANTS?\s+(.+)$", src, re.MULTILINE)
    constants = [c.strip() for c in const_m.group(1).split(",")] if const_m else []
    return module_name, constants


def collect_state_fields(src):
    fields = set()
    for m in re.finditer(r"\b(?:s|s_)\.(\w+)", src):
        fields.add(m.group(1))
    return sorted(fields)


def substitute_state_refs(expr, state_fields, current="s", nextp="s_", consts_name="c", consts_value_map=None):
    """Replace `s.field` → `field`, `s_.field` → `field'`, `c.x` → literal (if mapped).

    `consts_value_map` is {field_name: tla_expr_string}.
    """
    # Longer identifiers first to avoid overlap issues
    fields_sorted = sorted(state_fields, key=lambda f: -len(f))

    # s_.field → field'
    for f in fields_sorted:
        expr = re.sub(rf"\b{re.escape(nextp)}\.{re.escape(f)}\b", f"{f}'", expr)
    # s.field → field
    for f in fields_sorted:
        expr = re.sub(rf"\b{re.escape(current)}\.{re.escape(f)}\b", f, expr)
    # c.x → literal (from config)
    if consts_value_map:
        for k, v in consts_value_map.items():
            expr = re.sub(rf"\b{re.escape(consts_name)}\.{re.escape(k)}\b", f"({v})", expr)
    # Unmapped c.x references: replace with a bounded placeholder
    # (we emit a warning by inserting `\* c.x `)
    return expr


def substitute_params(expr, formal_params, actual_args):
    """Replace formal parameter names with actual arg expressions (simple token match)."""
    for formal, actual in zip(formal_params, actual_args):
        # Avoid replacing inside identifiers that contain the param name
        expr = re.sub(rf"\b{re.escape(formal)}\b", f"({actual})", expr)
    return expr


def finite_domain_for(tla_domain, int_min, int_max, max_seq_len):
    """Replace unbounded TLA+ domains with finite equivalents."""
    d = tla_domain.strip()
    if d == "Int":
        return f"{int_min}..{int_max}"
    if d == "Nat":
        return f"0..{int_max}"
    if d == "BOOLEAN":
        return "BOOLEAN"
    if d.startswith("Seq("):
        # Seq(AbstractType) → bounded sequences of ints
        return f"UNION {{ [1..k -> {int_min}..{int_max}] : k \\in 0..{max_seq_len} }}"
    return d


def rewrite_exists_bindings(exists_str, fields_set, int_min, int_max, max_seq_len):
    """Rewrite `x \in Int, y \in Seq(A)` into finite bindings, renaming conflicts."""
    rename_map = {}
    parts = []
    if not exists_str:
        return "", rename_map
    for binding in re.split(r",\s*(?=\w+\s*\\in)", exists_str.strip()):
        m = re.match(r"(\w+)\s*\\in\s+(.+)", binding.strip())
        if not m:
            continue
        name, domain = m.group(1), m.group(2).strip()
        new_name = f"_e_{name}" if name in fields_set else name
        if new_name != name:
            rename_map[name] = new_name
        fd = finite_domain_for(domain, int_min, int_max, max_seq_len)
        parts.append(f"{new_name} \\in {fd}")
    return ", ".join(parts), rename_map


def parse_model_config(toml_path):
    try:
        try:
            import tomllib
        except ImportError:
            import tomli as tomllib
        with open(toml_path, "rb") as f:
            data = tomllib.load(f)
    except Exception:
        data = {}
    quant = data.get("quantifiers", {}).get("int", {})
    int_min = quant.get("min", 0)
    int_max = quant.get("max", 2)
    max_seq_len = data.get("collections", {}).get("max_seq_len", 2)
    const_assigns = data.get("constants", {}).get("assignments", {})
    return {
        "int_min": int_min,
        "int_max": int_max,
        "max_seq_len": max_seq_len,
        "const_assigns": const_assigns,
    }


def collect_enum_symbols_from_types(tla_dir):
    """Scan Types.tla (if present) for model-value-style enum symbols.

    Pattern: `Name == {Foo, Bar, Baz}` defines a set of enum symbols that
    aren't declared anywhere. These are Verus enum variants that the verus2tla
    generator left as undefined identifiers.

    Returns: set of symbol names that need CONSTANTS assignments in the .cfg.
    """
    from pathlib import Path
    enum_symbols = set()
    types_path = Path(tla_dir) / "Types.tla"
    if not types_path.exists():
        return enum_symbols
    with open(types_path) as f:
        src = f.read()
    # Find set-literal definitions: `Name == {Foo, Bar}`
    for m in re.finditer(r"^\w+\s*==\s*\{([^}]+)\}", src, re.MULTILINE):
        for sym in m.group(1).split(","):
            sym = sym.strip()
            if re.match(r"^[A-Z][a-zA-Z0-9_]*$", sym):
                enum_symbols.add(sym)
    return enum_symbols


def build_wrapper(src, module_name, config, invariant_name, tla_dir=None):
    ops = parse_operators(src)
    state_fields = collect_state_fields(src)
    fields_set = set(state_fields)
    int_min, int_max, max_seq_len = (
        config["int_min"],
        config["int_max"],
        config["max_seq_len"],
    )

    # Phase 38.19: collect enum symbols from Types.tla that need CONSTANTS
    # assignments at TLC config time.
    enum_symbols = collect_enum_symbols_from_types(tla_dir) if tla_dir else set()

    # Build consts_value_map from config.constants.assignments.
    # Also add a `nodes` → bounded int range, common in generated specs.
    consts_value_map = dict(config["const_assigns"])
    if "nodes" not in consts_value_map:
        consts_value_map["nodes"] = f"{int_min}..{int_max}"

    # Find operators by name
    op_map = {n: (p, b) for n, p, b in ops}

    # ---- Build MC_Init from Init's body ----
    if "Init" not in op_map:
        raise SystemExit("No Init operator found in source")
    init_params, init_body = op_map["Init"]
    # Substitute s.field → field, c.x → value
    mc_init_body = substitute_state_refs(
        init_body, state_fields, consts_value_map=consts_value_map
    )

    # ---- Build MC_Next by expanding each disjunct ----
    # Parse Next's body for disjuncts.
    if "Next" not in op_map:
        raise SystemExit("No Next operator found in source")
    _, next_body = op_map["Next"]

    # Params commonly used for message-emission outputs in Verus→TLA+ specs.
    # These are "output" params whose domain is an abstract Seq type that TLC
    # can't enumerate. We drop them from the existential AND drop any
    # equality conjunct that constrains them in the action body.
    DROP_PARAM_NAMES = {"sent_packets"}

    # Each disjunct: \/ [\E bindings :] ActionName(s, s_, c, args...)
    mc_next_cases = []
    disjunct_re = re.compile(
        r"\\/\s*(?:\\E\s+([^:]+?)\s*:\s*)?(\w+)\s*\(([^)]*)\)",
        re.DOTALL,
    )
    for m in disjunct_re.finditer(next_body):
        exists_block = (m.group(1) or "").strip()
        action_name = m.group(2)
        args_str = m.group(3)
        action_args = [a.strip() for a in args_str.split(",") if a.strip()]
        if action_name not in op_map:
            continue
        action_params, action_body = op_map[action_name]
        if len(action_params) < 3:
            continue  # not (s, s_, c, ...) form

        # Drop output-only parameters from the existential binders
        if exists_block:
            filtered_bindings = []
            for binding in re.split(r",\s*(?=\w+\s*\\in)", exists_block.strip()):
                bm = re.match(r"(\w+)\s*\\in", binding.strip())
                if bm and bm.group(1) in DROP_PARAM_NAMES:
                    continue
                filtered_bindings.append(binding.strip())
            exists_block = ", ".join(filtered_bindings)

        # Drop conjuncts that constrain dropped params (e.g., `sent_packets = <<...>>`)
        filtered_lines = []
        for line in action_body.splitlines():
            skip = False
            for drop_name in DROP_PARAM_NAMES:
                if re.search(rf"\b{re.escape(drop_name)}\s*=", line):
                    skip = True
                    break
            if not skip:
                filtered_lines.append(line)
        action_body = "\n".join(filtered_lines)

        # Rewrite existential bindings (finite domains + renames)
        new_exists, rename_map = rewrite_exists_bindings(
            exists_block, fields_set, int_min, int_max, max_seq_len
        )

        # Build substitution map: formal params → actual arg expressions
        # action_params[0] = s (the state record param name, usually "s")
        # action_params[1] = s_ (usually "s_")
        # action_params[2] = c (usually "c")
        # action_params[3:] = extra parameters (e.g., node, sent_packets)
        # action_args: what's passed in Next — typically "s, s_, c, node, sent_packets"
        # We want to substitute formal[3:] with action_args[3:] (with renames applied).
        actual_args = [rename_map.get(a, a) for a in action_args]
        # Order matters: rename extra-params FIRST (before state substitution
        # merges field names with binder names). Use negative-lookahead for `'`
        # so we don't rename a primed identifier (which represents a field write).
        body_sub = action_body
        for i in range(3, len(action_params)):
            if i >= len(actual_args):
                break
            formal = action_params[i]
            actual = actual_args[i]
            # Replace the binder, but not if it's:
            # (a) part of `s.<name>` or `s_.<name>` (field access) — handled by negative lookbehind
            # (b) followed by `'` (next-state field)
            body_sub = re.sub(
                rf"(?<![.\w]){re.escape(formal)}\b(?!')",
                f"({actual})",
                body_sub,
            )
        # Then substitute s/s_/c field accesses.
        body_sub = substitute_state_refs(
            body_sub,
            state_fields,
            current=action_params[0],
            nextp=action_params[1],
            consts_name=action_params[2],
            consts_value_map=consts_value_map,
        )
        # Strip existing indentation from body lines and re-indent uniformly.
        # TLA+ uses indentation-based scoping for /\ conjunctions — all
        # conjuncts of a single action must be at the SAME indent level, or
        # TLC won't bind them all to the action.
        body_lines = []
        for ln in body_sub.splitlines():
            stripped = ln.lstrip()
            if stripped:
                body_lines.append(stripped)
        # Wrap in \E if there were any existentials
        if new_exists:
            indented = "\n".join("        " + ln for ln in body_lines)
            case = f"    \\/ \\E {new_exists} :\n{indented}"
        else:
            indented = "\n".join("      " + ln for ln in body_lines)
            case = f"    \\/\n{indented}"
        mc_next_cases.append(case)

    # ---- Build MC_<Invariant> by inlining invariant's body ----
    inv_section = ""
    mapped_inv = ""
    if invariant_name and invariant_name in op_map:
        inv_params, inv_body = op_map[invariant_name]
        if len(inv_params) >= 1:
            # Invariant takes (s, c)
            inv_sub = substitute_state_refs(
                inv_body,
                state_fields,
                current=inv_params[0],
                consts_name=inv_params[1] if len(inv_params) > 1 else "c",
                consts_value_map=consts_value_map,
            )
            # Replace unbounded domains with finite ones inside the invariant body.
            inv_sub = inv_sub.replace("\\in Int", f"\\in {int_min}..{int_max}")
            inv_sub = inv_sub.replace("\\in Nat", f"\\in 0..{int_max}")
            mapped_inv = f"MC_{invariant_name}"
            inv_section = f"{mapped_inv} ==\n    {inv_sub.strip()}\n"

    # ---- Assemble the wrapper ----
    wrapper_mn = f"{module_name}_MC"
    lines = [
        f"---- MODULE {wrapper_mn} ----",
        f"\\* Auto-generated TLC wrapper for parameterized-Init/Next spec `{module_name}`.",
        f"\\* Generated by generate_parameterized_mc_wrapper.py",
        f"\\* Phase 38.19: direct inlining of Init/Next/invariant bodies.",
        "",
        "EXTENDS Integers, Sequences, FiniteSets",
        "",
    ]
    _, consts = parse_header(src)
    # Filter out constants that the wrapper handles via config
    # (we don't declare them if we substituted them in — but some specs still
    # reference `State`, `Constants`, etc. as placeholder types)
    declared_consts = [c for c in consts if c not in consts_value_map]
    # Phase 38.19: include enum symbols found in Types.tla as CONSTANTS so
    # they can be assigned model values in the TLC .cfg.
    declared_consts.extend(sorted(enum_symbols))
    if declared_consts:
        lines.append(f"CONSTANTS {', '.join(declared_consts)}")
        lines.append("")

    if state_fields:
        lines.append(f"VARIABLES {', '.join(state_fields)}")
        lines.append("")

    lines.append("\\* Inlined Init body: substitute s.field → field, c.x → literal")
    lines.append("MC_Init ==")
    # Strip existing indentation and re-indent uniformly (TLA+ /\ conjunctions
    # need consistent indent to be bound to the same predicate).
    for ln in mc_init_body.splitlines():
        stripped = ln.lstrip()
        if stripped:
            lines.append("    " + stripped)
    lines.append("")

    lines.append("\\* Inlined Next: each disjunct with s/s_ substitutions")
    lines.append("MC_Next ==")
    if mc_next_cases:
        lines.append("\n".join(mc_next_cases))
    else:
        lines.append("    FALSE  \\* no action disjuncts detected")
    lines.append("")

    if inv_section:
        lines.append("\\* Inlined invariant")
        lines.append(inv_section)

    lines.append("====")
    return wrapper_mn, mapped_inv, "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--tla-file", required=True)
    ap.add_argument("--model-config", required=True)
    ap.add_argument("--invariant-name", default="")
    ap.add_argument("--out-file", required=True)
    args = ap.parse_args()

    with open(args.tla_file) as f:
        src = f.read()
    module_name, _ = parse_header(src)
    if not module_name:
        print("error: could not parse module name", file=sys.stderr)
        return 1

    config = parse_model_config(args.model_config)
    tla_dir = str(Path(args.tla_file).parent)
    wrapper_mn, mapped_inv, content = build_wrapper(
        src, module_name, config, args.invariant_name, tla_dir=tla_dir
    )
    Path(args.out_file).write_text(content)

    # Phase 38.19: emit enum symbols found in Types.tla so the shell runner
    # can add them as CONSTANTS (model values) in the TLC .cfg.
    enum_symbols = collect_enum_symbols_from_types(tla_dir)

    print(f"module={wrapper_mn}")
    print(f"invariant={mapped_inv}")
    print(f"init=MC_Init")
    print(f"next=MC_Next")
    if enum_symbols:
        print(f"enum_symbols={','.join(sorted(enum_symbols))}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
