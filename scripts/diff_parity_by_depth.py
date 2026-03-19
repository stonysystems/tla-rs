#!/usr/bin/env python3
"""Witness-first depth diff for cross-engine parity debugging (Phase 36.1.9).

Compares two parity JSONL state exports by depth, finding the earliest
depth where the normalized distinct frontiers differ. Reports witness
states at that depth with predecessor/branch provenance when available.

Turns "counts differ" into "this exact branch failed to reach / over-reached
this exact normalized state at depth N".

Input formats supported:
  - Basic parity export (--export-parity): {id, state, initial, depth}
  - Debug parity export (--export-parity-debug distinct_states.jsonl):
    {state_id, state, depth, initial, branch_label, predecessor_state_id}

Usage:
    python3 scripts/diff_parity_by_depth.py <left.jsonl> <right.jsonl>
    python3 scripts/diff_parity_by_depth.py \\
        reports/model_check/parity/source_first/twophase/states.jsonl \\
        reports/model_check/parity/tlc/twophase/states.jsonl \\
        --left-label source-first --right-label TLC

Exit codes:
    0 = state sets match at every depth
    1 = state sets diverge at some depth
    2 = error (missing file, parse error, etc.)
"""

import argparse
import json
import sys
from collections import defaultdict


def load_states_by_depth(path):
    """Load JSONL file into {depth: {canonical_state_json: entry}} mapping.

    Also returns the full {canonical_state_json: entry} dict and a has_depth flag.
    If no entries have a 'depth' field, has_depth is False and all states go to depth 0.
    """
    by_depth = defaultdict(dict)
    all_states = {}
    has_depth = False
    with open(path, 'r') as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                entry = json.loads(line)
            except json.JSONDecodeError as e:
                print(f"  Warning: skipping malformed line {line_num} in {path}: {e}",
                      file=sys.stderr)
                continue

            state_json = json.dumps(entry['state'], sort_keys=True, separators=(',', ':'))
            depth = entry.get('depth', -1)
            if depth >= 0:
                has_depth = True

            # Only record at the shallowest depth seen
            if state_json not in all_states or depth < all_states[state_json].get('depth', float('inf')):
                all_states[state_json] = entry

            by_depth[depth][state_json] = entry

    return by_depth, all_states, has_depth


def format_state_preview(entry, max_width=120):
    """Format a state entry for human-readable preview."""
    state_str = json.dumps(entry['state'], sort_keys=True, separators=(', ', ': '))
    if len(state_str) > max_width:
        state_str = state_str[:max_width - 3] + '...'
    return state_str


def format_provenance(entry):
    """Format predecessor/branch provenance if available."""
    parts = []
    branch = entry.get('branch_label')
    pred = entry.get('predecessor_state_id')
    if branch:
        parts.append(f"branch={branch}")
    if pred:
        pred_short = pred[:60] + '...' if len(str(pred)) > 60 else str(pred)
        parts.append(f"predecessor={pred_short}")
    return f" [{', '.join(parts)}]" if parts else ""


def find_first_divergent_depth(left_by_depth, right_by_depth):
    """Find the first depth where the state frontiers differ.

    Returns (depth, left_only_keys, right_only_keys) or None if identical at all depths.
    """
    all_depths = sorted(set(left_by_depth.keys()) | set(right_by_depth.keys()))

    for depth in all_depths:
        left_keys = set(left_by_depth.get(depth, {}).keys())
        right_keys = set(right_by_depth.get(depth, {}).keys())

        left_only = left_keys - right_keys
        right_only = right_keys - left_keys

        if left_only or right_only:
            return depth, left_only, right_only

    return None


def depth_summary_table(left_by_depth, right_by_depth, left_label, right_label):
    """Build a per-depth summary table."""
    all_depths = sorted(set(left_by_depth.keys()) | set(right_by_depth.keys()))
    rows = []
    for depth in all_depths:
        left_keys = set(left_by_depth.get(depth, {}).keys())
        right_keys = set(right_by_depth.get(depth, {}).keys())
        shared = len(left_keys & right_keys)
        lo = len(left_keys - right_keys)
        ro = len(right_keys - left_keys)
        rows.append({
            'depth': depth,
            'left': len(left_keys),
            'right': len(right_keys),
            'shared': shared,
            'left_only': lo,
            'right_only': ro,
        })
    return rows


def print_report(left_by_depth, right_by_depth, left_all, right_all,
                 left_label, right_label, max_witnesses,
                 left_has_depth=True, right_has_depth=True):
    """Print human-readable depth diff report."""
    total_left = len(left_all)
    total_right = len(right_all)
    all_left_keys = set(left_all.keys())
    all_right_keys = set(right_all.keys())

    print("=" * 70)
    print("Witness-First Depth Diff Report")
    print("=" * 70)
    print(f"  {left_label}: {total_left} distinct states")
    print(f"  {right_label}: {total_right} distinct states")
    if not left_has_depth:
        print(f"  NOTE: {left_label} export has no depth info (all states at depth 0)")
    if not right_has_depth:
        print(f"  NOTE: {right_label} export has no depth info (all states at depth 0)")
    both_have_depth = left_has_depth and right_has_depth
    print()

    # Per-depth table
    rows = depth_summary_table(left_by_depth, right_by_depth, left_label, right_label)
    print(f"{'Depth':>5}  {left_label:>8}  {right_label:>8}  {'Shared':>6}  "
          f"{left_label + '-only':>12}  {right_label + '-only':>12}")
    print("-" * 65)
    first_divergence_shown = False
    for r in rows:
        if not first_divergence_shown and (r['left_only'] or r['right_only']):
            marker = " <-- FIRST DIVERGENCE"
            first_divergence_shown = True
        else:
            marker = ""
        print(f"{r['depth']:>5}  {r['left']:>8}  {r['right']:>8}  {r['shared']:>6}  "
              f"{r['left_only']:>12}  {r['right_only']:>12}{marker}")
    print()

    # First divergence
    result = find_first_divergent_depth(left_by_depth, right_by_depth)
    if result is None:
        print(f"VERDICT: PARITY at every depth — "
              f"{total_left} states match across all {len(rows)} depths")
        return True

    depth, left_only, right_only = result
    print(f"First divergence at depth {depth}:")
    print(f"  {left_label}-only: {len(left_only)} states")
    print(f"  {right_label}-only: {len(right_only)} states")
    print()

    if left_only:
        print(f"  {left_label}-only witness states at depth {depth}:")
        for key in sorted(left_only)[:max_witnesses]:
            entry = left_by_depth[depth][key]
            preview = format_state_preview(entry)
            provenance = format_provenance(entry)
            print(f"    {preview}{provenance}")
        if len(left_only) > max_witnesses:
            print(f"    ... and {len(left_only) - max_witnesses} more")
        print()

    if right_only:
        print(f"  {right_label}-only witness states at depth {depth}:")
        for key in sorted(right_only)[:max_witnesses]:
            entry = right_by_depth[depth][key]
            preview = format_state_preview(entry)
            provenance = format_provenance(entry)
            print(f"    {preview}{provenance}")
        if len(right_only) > max_witnesses:
            print(f"    ... and {len(right_only) - max_witnesses} more")
        print()

    # Overall summary
    total_shared = len(all_left_keys & all_right_keys)
    total_lo = len(all_left_keys - all_right_keys)
    total_ro = len(all_right_keys - all_left_keys)
    print(f"Overall: {total_shared} shared, "
          f"{total_lo} {left_label}-only, {total_ro} {right_label}-only")
    if both_have_depth:
        print(f"VERDICT: MISMATCH — first divergence at depth {depth}")
    else:
        print(f"VERDICT: MISMATCH — depth {depth} "
              f"(depth comparison limited: one or both exports lack depth info)")
    return False


def build_json_report(left_by_depth, right_by_depth, left_all, right_all,
                      left_label, right_label, max_witnesses,
                      left_has_depth=True, right_has_depth=True):
    """Build machine-readable JSON report."""
    all_left_keys = set(left_all.keys())
    all_right_keys = set(right_all.keys())

    report = {
        'left_label': left_label,
        'right_label': right_label,
        'left_total': len(left_all),
        'right_total': len(right_all),
        'shared_total': len(all_left_keys & all_right_keys),
        'left_only_total': len(all_left_keys - all_right_keys),
        'right_only_total': len(all_right_keys - all_left_keys),
        'left_has_depth': left_has_depth,
        'right_has_depth': right_has_depth,
        'depth_table': depth_summary_table(
            left_by_depth, right_by_depth, left_label, right_label),
    }

    result = find_first_divergent_depth(left_by_depth, right_by_depth)
    if result is None:
        report['parity'] = True
        report['first_divergent_depth'] = None
    else:
        depth, left_only, right_only = result
        report['parity'] = False
        report['first_divergent_depth'] = depth
        report['left_only_at_divergence'] = len(left_only)
        report['right_only_at_divergence'] = len(right_only)

        # Witness states with provenance
        left_witnesses = []
        for key in sorted(left_only)[:max_witnesses]:
            entry = left_by_depth[depth][key]
            w = {'state': entry['state'], 'depth': depth}
            if 'branch_label' in entry and entry['branch_label']:
                w['branch_label'] = entry['branch_label']
            if 'predecessor_state_id' in entry and entry['predecessor_state_id']:
                w['predecessor_state_id'] = entry['predecessor_state_id']
            left_witnesses.append(w)

        right_witnesses = []
        for key in sorted(right_only)[:max_witnesses]:
            entry = right_by_depth[depth][key]
            w = {'state': entry['state'], 'depth': depth}
            if 'branch_label' in entry and entry['branch_label']:
                w['branch_label'] = entry['branch_label']
            if 'predecessor_state_id' in entry and entry['predecessor_state_id']:
                w['predecessor_state_id'] = entry['predecessor_state_id']
            right_witnesses.append(w)

        report['left_witnesses'] = left_witnesses
        report['right_witnesses'] = right_witnesses

    return report


def main():
    parser = argparse.ArgumentParser(
        description='Witness-first depth diff for cross-engine parity debugging')
    parser.add_argument('left', help='Left JSONL file (e.g., source-first)')
    parser.add_argument('right', help='Right JSONL file (e.g., TLC)')
    parser.add_argument('--left-label', default='left',
                        help='Label for left file in report')
    parser.add_argument('--right-label', default='right',
                        help='Label for right file in report')
    parser.add_argument('--max-witnesses', type=int, default=5,
                        help='Max witness states to show per side (default: 5)')
    parser.add_argument('--json', action='store_true',
                        help='Output machine-readable JSON report')
    args = parser.parse_args()

    try:
        left_by_depth, left_all, left_has_depth = load_states_by_depth(args.left)
        right_by_depth, right_all, right_has_depth = load_states_by_depth(args.right)
    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(2)
    except Exception as e:
        print(f"Error loading states: {e}", file=sys.stderr)
        sys.exit(2)

    if args.json:
        report = build_json_report(
            left_by_depth, right_by_depth, left_all, right_all,
            args.left_label, args.right_label, args.max_witnesses,
            left_has_depth, right_has_depth)
        print(json.dumps(report, indent=2))
        sys.exit(0 if report['parity'] else 1)

    is_parity = print_report(
        left_by_depth, right_by_depth, left_all, right_all,
        args.left_label, args.right_label, args.max_witnesses,
        left_has_depth, right_has_depth)
    sys.exit(0 if is_parity else 1)


if __name__ == '__main__':
    main()
