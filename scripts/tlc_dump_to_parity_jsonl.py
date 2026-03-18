#!/usr/bin/env python3
"""Convert a TLC -dump file to parity JSONL for cross-engine comparison.

Parses TLC's state dump format, extracts the `state` variable from each
state block, normalizes it to canonical JSON matching the schema in
docs/cross-engine-state-normalization.md, deduplicates, and writes
sorted JSONL to stdout or a file.

Usage:
    python3 scripts/tlc_dump_to_parity_jsonl.py <dump_file> [--output <path>]
    python3 scripts/tlc_dump_to_parity_jsonl.py <dump_file> --protocol twophase

The --protocol flag selects protocol-specific enum normalization rules.
"""

import argparse
import json
import re
import sys
from collections import OrderedDict


# --- TLA+ value parser ---

def parse_tla_value(s):
    """Parse a TLA+ value string into a Python object."""
    s = s.strip()
    return _parse_value(s, 0)[0]


def _parse_value(s, pos):
    """Recursive TLA+ value parser. Returns (value, new_pos)."""
    s_len = len(s)
    while pos < s_len and s[pos] in ' \t\n':
        pos += 1

    if pos >= s_len:
        raise ValueError(f"Unexpected end of input")

    c = s[pos]

    # Boolean
    if s[pos:pos+4] == 'TRUE':
        return True, pos + 4
    if s[pos:pos+5] == 'FALSE':
        return False, pos + 5

    # Integer (possibly negative)
    if c == '-' or c.isdigit():
        end = pos + 1 if c == '-' else pos
        while end < s_len and s[end].isdigit():
            end += 1
        return int(s[pos:end]), end

    # String
    if c == '"':
        end = pos + 1
        while end < s_len and s[end] != '"':
            if s[end] == '\\':
                end += 1
            end += 1
        return s[pos+1:end], end + 1

    # Set: { ... }
    if c == '{':
        pos += 1
        elements = []
        while pos < s_len:
            while pos < s_len and s[pos] in ' \t\n':
                pos += 1
            if pos < s_len and s[pos] == '}':
                return ('__set__', sorted(elements, key=_sort_key)), pos + 1
            val, pos = _parse_value(s, pos)
            elements.append(val)
            while pos < s_len and s[pos] in ' \t\n':
                pos += 1
            if pos < s_len and s[pos] == ',':
                pos += 1
        raise ValueError("Unterminated set")

    # Sequence: << ... >>
    if s[pos:pos+2] == '<<':
        pos += 2
        elements = []
        while pos < s_len:
            while pos < s_len and s[pos] in ' \t\n':
                pos += 1
            if s[pos:pos+2] == '>>':
                return ('__seq__', elements), pos + 2
            val, pos = _parse_value(s, pos)
            elements.append(val)
            while pos < s_len and s[pos] in ' \t\n':
                pos += 1
            if pos < s_len and s[pos] == ',':
                pos += 1
        raise ValueError("Unterminated sequence")

    # Record: [ field |-> value, ... ]
    if c == '[':
        pos += 1
        fields = OrderedDict()
        while pos < s_len:
            while pos < s_len and s[pos] in ' \t\n':
                pos += 1
            if pos < s_len and s[pos] == ']':
                return ('__record__', fields), pos + 1
            # Parse field name
            name_start = pos
            while pos < s_len and s[pos] not in ' \t\n|':
                pos += 1
            name = s[name_start:pos].strip()
            # Skip |->
            while pos < s_len and s[pos] in ' \t\n':
                pos += 1
            if s[pos:pos+3] == '|->':
                pos += 3
            else:
                raise ValueError(f"Expected '|->' at pos {pos}, got '{s[pos:pos+5]}'")
            val, pos = _parse_value(s, pos)
            fields[name] = val
            while pos < s_len and s[pos] in ' \t\n':
                pos += 1
            if pos < s_len and s[pos] == ',':
                pos += 1
        raise ValueError("Unterminated record")

    # Parenthesized expression or TLC function: (k1 :> v1 @@ k2 :> v2)
    if c == '(':
        pos += 1
        # Parse first key
        while pos < s_len and s[pos] in ' \t\n':
            pos += 1
        if pos < s_len and s[pos] == ')':
            # Empty parens — shouldn't happen but handle gracefully
            return ('__map__', []), pos + 1
        first_val, pos = _parse_value(s, pos)
        while pos < s_len and s[pos] in ' \t\n':
            pos += 1
        # Check if this is a TLC function (k :> v @@ ...)
        if pos + 1 < s_len and s[pos:pos+2] == ':>':
            entries = []
            key = first_val
            while True:
                # Skip :>
                pos += 2
                while pos < s_len and s[pos] in ' \t\n':
                    pos += 1
                val, pos = _parse_value(s, pos)
                entries.append((key, val))
                while pos < s_len and s[pos] in ' \t\n':
                    pos += 1
                if pos < s_len and s[pos] == ')':
                    return ('__map__', sorted(entries, key=lambda e: _sort_key(e[0]))), pos + 1
                if pos + 1 < s_len and s[pos:pos+2] == '@@':
                    pos += 2
                    while pos < s_len and s[pos] in ' \t\n':
                        pos += 1
                    key, pos = _parse_value(s, pos)
                    while pos < s_len and s[pos] in ' \t\n':
                        pos += 1
                    continue
                raise ValueError(f"Expected ')' or '@@' in function at pos {pos}")
        else:
            # Simple parenthesized expression
            while pos < s_len and s[pos] in ' \t\n':
                pos += 1
            if pos < s_len and s[pos] == ')':
                return first_val, pos + 1
            raise ValueError(f"Unexpected in parens at pos {pos}")

    # Identifier (model value / constant)
    if c.isalpha() or c == '_':
        end = pos
        while end < s_len and (s[end].isalnum() or s[end] == '_'):
            end += 1
        return s[pos:end], end

    raise ValueError(f"Cannot parse at pos {pos}: '{s[pos:pos+20]}'")


def _sort_key(val):
    """Sort key for canonical ordering of set/map elements."""
    if isinstance(val, bool):
        return (0, val)
    if isinstance(val, int):
        return (1, val)
    if isinstance(val, str):
        return (2, val)
    if isinstance(val, tuple) and len(val) == 2:
        tag, data = val
        if tag == '__set__':
            return (3, tuple(_sort_key(e) for e in data))
        if tag == '__seq__':
            return (4, tuple(_sort_key(e) for e in data))
        if tag == '__record__':
            return (5, tuple((k, _sort_key(v)) for k, v in sorted(data.items())))
        if tag == '__map__':
            return (6, tuple((_sort_key(k), _sort_key(v)) for k, v in data))
    return (7, str(val))


# --- Enum tag normalization ---

# Protocol-specific tag → variant mappings
ENUM_TAG_MAPS = {
    'twophase': {
        'Init_tag': 'Init',
        'Committed_tag': 'Committed',
        'Aborted_tag': 'Aborted',
    },
    'primarybackup': {
        'Primary_tag': 'Primary',
        'Backup_tag': 'Backup',
    },
    'leaderelection': {},
    'paxos': {
        'None_tag': 'None',
        'Idle_tag': 'Idle',
        'Phase1_tag': 'Phase1',
        'Phase2_tag': 'Phase2',
        'Decided_tag': 'Decided',
    },
}


def normalize_to_json(val, tag_map):
    """Convert parsed TLA+ value to canonical JSON matching normalization schema."""
    if isinstance(val, bool):
        return val
    if isinstance(val, int):
        return val
    if isinstance(val, str):
        # Bare model value — if it matches a known tag, convert to variant object
        if val in tag_map:
            return {'_variant': tag_map[val]}
        return val
    if isinstance(val, tuple) and len(val) == 2:
        tag, data = val
        if tag == '__set__':
            return [normalize_to_json(e, tag_map) for e in data]
        if tag == '__seq__':
            return [normalize_to_json(e, tag_map) for e in data]
        if tag == '__record__':
            # Check if this is a tag-only record (enum representation)
            if list(data.keys()) == ['tag']:
                tag_val = data['tag']
                if isinstance(tag_val, str) and tag_val in tag_map:
                    return {'_variant': tag_map[tag_val]}
                return {'_variant': tag_val}
            # Regular record: sort fields alphabetically
            result = {}
            for k in sorted(data.keys()):
                result[k] = normalize_to_json(data[k], tag_map)
            return result
        if tag == '__map__':
            # TLC function: list of [key, value] pairs sorted by key
            return [[normalize_to_json(k, tag_map), normalize_to_json(v, tag_map)]
                    for k, v in data]
    return val


# --- TLC dump parser ---

def parse_tlc_dump(dump_text):
    """Parse TLC dump text into list of (state_num, var_dict) tuples."""
    states = []
    current_num = None
    current_vars = {}
    current_var = None
    current_val_lines = []

    def flush_var():
        nonlocal current_var, current_val_lines
        if current_var and current_val_lines:
            val_str = ' '.join(current_val_lines)
            current_vars[current_var] = val_str
        current_var = None
        current_val_lines = []

    def flush_state():
        nonlocal current_num, current_vars
        flush_var()
        if current_num is not None and current_vars:
            states.append((current_num, dict(current_vars)))
        current_num = None
        current_vars = {}

    for line in dump_text.split('\n'):
        # State header
        m = re.match(r'^State (\d+):', line)
        if m:
            flush_state()
            current_num = int(m.group(1))
            current_vars = {}
            continue

        # Variable assignment: /\ var = value
        m = re.match(r'^/\\ (\w+) = (.*)$', line)
        if m:
            flush_var()
            current_var = m.group(1)
            current_val_lines = [m.group(2)]
            continue

        # Continuation line
        if line.strip() and current_var:
            current_val_lines.append(line.strip())

    flush_state()
    return states


# Per-protocol fields to exclude from the projected state.
# These are wrapper-level bookkeeping that doesn't exist in the Verus spec.
EXCLUDE_FIELDS = {
    'twophase': [],
    'primarybackup': ['phase'],  # Hand-written TLC wrapper adds phase field
    'leaderelection': [],
    'paxos': [],
}


def remove_excluded_fields(state_dict, excluded):
    """Remove excluded fields from a normalized state dict."""
    if not excluded or not isinstance(state_dict, dict):
        return state_dict
    return {k: v for k, v in state_dict.items() if k not in excluded}


def process_dump(dump_text, protocol='twophase', extra_exclude=None):
    """Process TLC dump text and produce parity JSONL lines."""
    tag_map = ENUM_TAG_MAPS.get(protocol, {})
    excluded = list(EXCLUDE_FIELDS.get(protocol, []))
    if extra_exclude:
        excluded.extend(extra_exclude)
    states = parse_tlc_dump(dump_text)

    seen = {}  # canonical_json_str -> (json_obj, state_num)
    initial_state_num = None

    for state_num, var_dict in states:
        if 'state' not in var_dict:
            continue

        # Parse the state variable value
        state_val = parse_tla_value(var_dict['state'])
        normalized = normalize_to_json(state_val, tag_map)
        normalized = remove_excluded_fields(normalized, excluded)

        # Produce canonical JSON (sorted keys, minified)
        canonical_str = json.dumps(normalized, sort_keys=True, separators=(',', ':'))

        if canonical_str not in seen:
            seen[canonical_str] = (normalized, state_num)
            if initial_state_num is None:
                initial_state_num = state_num

    # Build JSONL sorted by canonical JSON string
    lines = []
    for canonical_str in sorted(seen.keys()):
        normalized, state_num = seen[canonical_str]
        entry = {
            'id': canonical_str,
            'state': normalized,
            'initial': state_num == 1,  # TLC State 1 is always initial
            'depth': -1,  # TLC dump doesn't include depth info
        }
        lines.append(json.dumps(entry, sort_keys=False))

    return lines


def main():
    parser = argparse.ArgumentParser(description='Convert TLC dump to parity JSONL')
    parser.add_argument('dump_file', help='Path to TLC dump file')
    parser.add_argument('--output', '-o', help='Output JSONL file (default: stdout)')
    parser.add_argument('--protocol', '-p', default='twophase',
                        choices=['twophase', 'primarybackup', 'leaderelection', 'paxos'],
                        help='Protocol name for enum tag normalization')
    parser.add_argument('--exclude-fields', nargs='*', default=None,
                        help='Additional state fields to exclude from projection')
    args = parser.parse_args()

    with open(args.dump_file, 'r') as f:
        dump_text = f.read()

    lines = process_dump(dump_text, args.protocol, args.exclude_fields)

    if args.output:
        with open(args.output, 'w') as f:
            for line in lines:
                f.write(line + '\n')
        print(f"Wrote {len(lines)} states to {args.output}", file=sys.stderr)
    else:
        for line in lines:
            print(line)


if __name__ == '__main__':
    main()
