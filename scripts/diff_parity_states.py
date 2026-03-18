#!/usr/bin/env python3
"""Diff two parity JSONL state exports for cross-engine comparison.

Reads two JSONL files (source-first and TLC exports) produced by
Phase 36.1.3/36.1.4 and reports:
- Distinct state set comparison (shared, left-only, right-only)
- Initial state set comparison
- First witness states from each side for manual inspection

Usage:
    python3 scripts/diff_parity_states.py <left.jsonl> <right.jsonl>
    python3 scripts/diff_parity_states.py \\
        reports/model_check/parity/source_first/twophase/states.jsonl \\
        reports/model_check/parity/tlc/twophase/states.jsonl \\
        --left-label source-first --right-label TLC

Exit codes:
    0 = state sets match exactly
    1 = state sets differ
    2 = error (missing file, parse error, etc.)
"""

import argparse
import json
import sys


def load_states(path):
    """Load JSONL file into dict of {canonical_state_json: entry}."""
    states = {}
    initial_ids = set()
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

            # Use the canonical state JSON as the comparison key
            # (not the id field, which may differ between engines)
            state_json = json.dumps(entry['state'], sort_keys=True, separators=(',', ':'))
            if state_json not in states:
                states[state_json] = entry
            if entry.get('initial', False):
                initial_ids.add(state_json)

    return states, initial_ids


def format_state_preview(entry, max_width=120):
    """Format a state entry for human-readable preview."""
    state_str = json.dumps(entry['state'], sort_keys=True, separators=(', ', ': '))
    if len(state_str) > max_width:
        state_str = state_str[:max_width - 3] + '...'
    depth_info = f"depth={entry.get('depth', '?')}"
    initial_info = " [INITIAL]" if entry.get('initial', False) else ""
    return f"  {state_str}{initial_info} ({depth_info})"


def diff_state_sets(left_states, left_initial, right_states, right_initial,
                    left_label, right_label, max_witnesses=3):
    """Compare two state sets and print a diff report. Returns True if identical."""
    left_keys = set(left_states.keys())
    right_keys = set(right_states.keys())

    shared = left_keys & right_keys
    left_only = left_keys - right_keys
    right_only = right_keys - left_keys

    # Initial state comparison
    shared_initial = left_initial & right_initial
    left_only_initial = left_initial - right_initial
    right_only_initial = right_initial - left_initial

    print("=" * 70)
    print("Parity State Diff Report")
    print("=" * 70)
    print(f"  {left_label}: {len(left_states)} distinct states "
          f"({len(left_initial)} initial)")
    print(f"  {right_label}: {len(right_states)} distinct states "
          f"({len(right_initial)} initial)")
    print()

    # Overall comparison
    print(f"Distinct states:")
    print(f"  Shared:       {len(shared)}")
    print(f"  {left_label}-only: {len(left_only)}")
    print(f"  {right_label}-only: {len(right_only)}")
    print()

    print(f"Initial states:")
    print(f"  Shared:       {len(shared_initial)}")
    print(f"  {left_label}-only: {len(left_only_initial)}")
    print(f"  {right_label}-only: {len(right_only_initial)}")
    print()

    # Witness states
    if left_only:
        print(f"First {min(max_witnesses, len(left_only))} {left_label}-only witnesses:")
        for key in sorted(left_only)[:max_witnesses]:
            print(format_state_preview(left_states[key]))
        print()

    if right_only:
        print(f"First {min(max_witnesses, len(right_only))} {right_label}-only witnesses:")
        for key in sorted(right_only)[:max_witnesses]:
            print(format_state_preview(right_states[key]))
        print()

    if left_only_initial:
        print(f"{left_label}-only initial states:")
        for key in sorted(left_only_initial):
            print(format_state_preview(left_states[key]))
        print()

    if right_only_initial:
        print(f"{right_label}-only initial states:")
        for key in sorted(right_only_initial):
            print(format_state_preview(right_states[key]))
        print()

    # Verdict
    if not left_only and not right_only:
        print("VERDICT: PARITY — state sets are identical")
        if left_only_initial or right_only_initial:
            print("  (but initial state sets differ)")
        return True
    else:
        print(f"VERDICT: MISMATCH — {len(left_only)} {left_label}-only, "
              f"{len(right_only)} {right_label}-only")
        return False


def main():
    parser = argparse.ArgumentParser(
        description='Diff two parity JSONL state exports')
    parser.add_argument('left', help='Left JSONL file (e.g., source-first)')
    parser.add_argument('right', help='Right JSONL file (e.g., TLC)')
    parser.add_argument('--left-label', default='left',
                        help='Label for left file in report')
    parser.add_argument('--right-label', default='right',
                        help='Label for right file in report')
    parser.add_argument('--max-witnesses', type=int, default=3,
                        help='Max witness states to show per side')
    parser.add_argument('--json', action='store_true',
                        help='Output machine-readable JSON summary')
    args = parser.parse_args()

    try:
        left_states, left_initial = load_states(args.left)
        right_states, right_initial = load_states(args.right)
    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(2)
    except Exception as e:
        print(f"Error loading states: {e}", file=sys.stderr)
        sys.exit(2)

    if args.json:
        left_keys = set(left_states.keys())
        right_keys = set(right_states.keys())
        summary = {
            'left_count': len(left_states),
            'right_count': len(right_states),
            'shared_count': len(left_keys & right_keys),
            'left_only_count': len(left_keys - right_keys),
            'right_only_count': len(right_keys - left_keys),
            'left_initial_count': len(left_initial),
            'right_initial_count': len(right_initial),
            'parity': left_keys == right_keys,
        }
        print(json.dumps(summary, indent=2))
        sys.exit(0 if summary['parity'] else 1)

    is_parity = diff_state_sets(
        left_states, left_initial,
        right_states, right_initial,
        args.left_label, args.right_label,
        args.max_witnesses,
    )
    sys.exit(0 if is_parity else 1)


if __name__ == '__main__':
    main()
