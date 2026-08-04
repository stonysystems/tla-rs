#!/usr/bin/env bash
# V2 strong fidelity: compare a case's `clean.tla` against its `original.tla`
# by the states they reach, projected onto the observables they share.
#
#   tests/corpus/scripts/tlc_fidelity.sh <case-dir> [tla2tools.jar]
#
# The case must carry an `observables.toml` naming the variable pairs to
# compare and the TLC constants for each side:
#
#   [clean]
#   module = "TwoPhaseClean"
#   config = """
#   CONSTANTS
#     RM = {r1, r2}
#     TM = r1
#   SPECIFICATION Spec
#   """
#   [original]
#   module = "TwoPhase"
#   config = """..."""
#   # Variables to compare, `clean = "original"`.
#   [observables]
#   rmState = "rmState"
#
# ## Why states and not a refinement mapping
#
# A refinement check (`Spec => Abstract!Spec`) is the strong TLA+ answer, but it
# needs the two specs to agree on a stuttering discipline and on every variable
# in the mapping. A rewrite deliberately deletes variables (history variables,
# views), so the mapping does not exist. Comparing the *reachable observable
# states* asks the question the rewrite actually has to answer: does the clean
# spec reach anything the original does not, and what did it stop reaching?
#
# ## Why not `VIEW`
#
# TLC's `VIEW` collapses the fingerprint, so it also stops *exploring* states
# whose view it has already seen. That under-explores, and an under-explored
# search cannot support a fidelity claim. So the full state space is dumped and
# the projection is done here.
#
# ## Reading the result
#
# - **only in clean** — the rewrite admits behaviour the original forbids. This
#   is a defect: the rewrite is not a specialisation of the original.
# - **only in original** — the rewrite lost behaviour. Often intended (a slice,
#   a dropped branch), but it must be *stated* in the case's rewrite.md.
#
# ## What this does NOT catch, and it matters
#
# Reachable *states*, not reachable *behaviours*. Deleting an action whose
# effects another action also produces leaves the state set unchanged and this
# comparison silent. That is not hypothetical: deleting `RMChooseToAbort` from
# TwoPhase's clean spec changes nothing here, because an RM still reaches
# "aborted" by receiving the TM's abort. A path was removed and the tool says
# EQUAL.
#
# So an EQUAL result means "the rewrite reaches exactly the same observable
# states", which is a real and checkable claim, and it is NOT "the rewrite is
# behaviourally equivalent". A case's rewrite.md must not report it as the
# latter. Catching a removed path needs trace comparison or a refinement check
# with a stuttering discipline, and neither is this script.
#
# Exit 0 when the observable state sets are equal, 1 when they differ, 2 on a
# setup error.
set -euo pipefail

case_dir="${1:?usage: tlc_fidelity.sh <case-dir> [tla2tools.jar]}"
case_dir="$(cd "$case_dir" && pwd)"
jar="${2:-${TLA2TOOLS_JAR:-}}"

if [ -z "$jar" ] || [ ! -f "$jar" ]; then
  echo "tla2tools.jar not found; pass it as \$2 or set TLA2TOOLS_JAR" >&2
  exit 2
fi
jar="$(cd "$(dirname "$jar")" && pwd)/$(basename "$jar")"

spec="$case_dir/observables.toml"
[ -f "$spec" ] || { echo "$case_dir: no observables.toml — the case declares nothing to compare" >&2; exit 2; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

python3 - "$case_dir" "$spec" "$jar" "$work" <<'PY'
import re, subprocess, sys, os

def read_toml(path):
    # The slice of TOML observables.toml uses: tables, key = "value",
    # a triple-quoted block, and arrays of strings.
    #
    # Hand-written because this repo's Python is 3.10, which has no `tomllib`,
    # and a `toml` package is not installed. Anything outside the slice is an
    # error rather than something silently ignored.
    spec, table, lines = {}, None, open(path).read().splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        i += 1
        if not line or line.startswith("#"):
            continue
        if line.startswith("[") and line.endswith("]"):
            table = line[1:-1]
            spec.setdefault(table, {})
            continue
        if "=" not in line or table is None:
            raise SystemExit(f"{path}: cannot read line: {line}")
        key, value = (part.strip() for part in line.split("=", 1))
        if value == '"""':
            block = []
            while i < len(lines) and lines[i].strip() != '"""':
                block.append(lines[i])
                i += 1
            i += 1
            spec[table][key] = "\n".join(block) + "\n"
        elif value.startswith('"'):
            spec[table][key] = value.strip('"')
        elif value.startswith("["):
            spec[table][key] = [
                item.strip().strip('"')
                for item in value[1:-1].split(",")
                if item.strip()
            ]
        else:
            raise SystemExit(f"{path}: unsupported value for `{key}`: {value}")
    return spec

case_dir, spec_path, jar, work = sys.argv[1:5]
spec = read_toml(spec_path)
observables = spec["observables"]

def dump_states(side, source_name):
    """Run TLC over one side and return its reachable states as dicts."""
    cfg = spec[side]
    module = cfg["module"]
    src = os.path.join(case_dir, source_name)
    if not os.path.exists(src):
        raise SystemExit(f"{case_dir}: missing {source_name}")
    run = os.path.join(work, side)
    os.makedirs(run, exist_ok=True)
    text = open(src).read()
    # TLC requires the file name to match the module name. A side may run
    # through a wrapper module instead -- `Ballot == Nat` has to be overridden
    # to something finite, and TLC only overrides a definition with another
    # definition -- in which case `source_as` says what to call the spec and
    # `module` names the wrapper, which arrives via `extra_modules`.
    open(os.path.join(run, cfg.get("source_as", module + ".tla")), "w").write(text)
    open(os.path.join(run, module + ".cfg"), "w").write(cfg["config"])
    for extra in cfg.get("extra_modules", []):
        open(os.path.join(run, extra), "w").write(
            open(os.path.join(case_dir, extra)).read()
        )

    proc = subprocess.run(
        ["java", "-XX:+UseParallelGC", "-cp", jar, "tlc2.TLC",
         "-workers", "8", "-deadlock", "-dump", "states.txt", module],
        cwd=run, capture_output=True, text=True,
    )
    dump = os.path.join(run, "states.txt.dump")
    if not os.path.exists(dump):
        sys.stderr.write(proc.stdout[-3000:])
        raise SystemExit(f"{side}: TLC produced no state dump")
    states = parse_dump(open(dump).read())
    if not states:
        sys.stderr.write(proc.stdout[-3000:])
        raise SystemExit(f"{side}: the dump parsed to no states at all")
    print(f"  {side}: {len(states)} states dumped", file=sys.stderr)
    return states

def parse_dump(text):
    # TLC's dump is "State N:" followed by conjunct lines. A value may run over
    # several lines, so a line that does not start a new conjunct continues the
    # previous one.
    states, current, var = [], None, None
    for line in text.splitlines():
        if re.match(r"^State \d+:", line):
            if current:
                states.append(current)
            current, var = {}, None
            continue
        if current is None:
            continue
        m = re.match(r"^/\\ (\w+) = (.*)$", line)
        if m:
            var = m.group(1)
            current[var] = m.group(2).strip()
        elif line.strip() and var is not None:
            current[var] += " " + line.strip()
        elif not line.strip():
            var = None
    if current:
        states.append(current)
    return states

def project(states, name_of):
    """Keep only the observables, renamed to the comparison's own names."""
    out = set()
    for state in states:
        row = []
        for shared, source_var in name_of.items():
            if source_var not in state:
                raise SystemExit(
                    f"observable `{shared}` maps to `{source_var}`, "
                    f"which is not a variable of that spec"
                )
            row.append((shared, canonical(state[source_var])))
        out.add(tuple(sorted(row)))
    return out

def canonical(value):
    """Normalise whitespace so formatting differences are not differences.

    Set and record *element order* is not normalised: TLC prints both in a
    deterministic order, and reordering by hand would risk equating values that
    differ. A spurious difference is visible; a spurious equality is not."""
    return re.sub(r"\s+", " ", value).strip()

print("running TLC on both sides", file=sys.stderr)
clean = project(dump_states("clean", "clean.tla"),
                {k: k for k in observables})
original = project(dump_states("original", "original.tla"),
                   {k: v for k, v in observables.items()})

only_clean = clean - original
only_original = original - clean

print(f"\nobservables: {', '.join(observables)}")
print(f"clean reaches    {len(clean):>8} distinct observable states")
print(f"original reaches {len(original):>8} distinct observable states")

if not only_clean and not only_original:
    print("\nEQUAL — the rewrite reaches exactly what the original reaches.")
    raise SystemExit(0)

if only_clean:
    print(f"\n{len(only_clean)} state(s) ONLY IN CLEAN — the rewrite admits "
          f"behaviour the original forbids. This is a defect.")
    for row in sorted(only_clean)[:10]:
        print("  " + "; ".join(f"{k} = {v}" for k, v in row))
    if len(only_clean) > 10:
        print(f"  ... and {len(only_clean) - 10} more")

if only_original:
    print(f"\n{len(only_original)} state(s) ONLY IN ORIGINAL — the rewrite lost "
          f"behaviour. Intended narrowing must be stated in rewrite.md.")
    for row in sorted(only_original)[:10]:
        print("  " + "; ".join(f"{k} = {v}" for k, v in row))
    if len(only_original) > 10:
        print(f"  ... and {len(only_original) - 10} more")

raise SystemExit(1)
PY
