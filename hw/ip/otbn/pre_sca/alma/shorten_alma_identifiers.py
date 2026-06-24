#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Shorten escaped Verilog identifiers in an .alma.v / circuit.v netlist.

Verilator maps '.' -> '__02E' (+4 chars) and '[N]' -> '__05BN__05D' (+8 chars)
when converting escaped Verilog identifiers to C++ names.  Names whose mangled
form reaches 128+ characters get hashed in VCD tracing, breaking Alma's signal
lookup.

For each escaped identifier whose C++ length exceeds the limit, this script
drops leading dot-separated segments until the remainder fits, keeping the
longest meaningful tail. If two long identifiers trim to the same tail, a
numeric suffix (_2, _3, ...) is appended to disambiguate.
"""

import argparse
import re

VERILATOR_LIMIT = 128


def _cpp_len(identifier: str) -> int:
    # Verilator mangles '.' -> '__02E' (+4 net) and '[N]' -> '__05BN__05D' (+8 net).
    n = len(identifier)
    n += 4 * identifier.count('.')
    n += 8 * len(re.findall(r'\[\d+\]', identifier))
    return n


def build_id_map(text: str) -> dict:
    """Return a mapping of long identifier -> shortened identifier (no backslashes)."""
    escaped_re = re.compile(r'\\([^ \t\n;,)(]+)')
    all_ids = set(escaped_re.findall(text))
    long_ids = sorted(i for i in all_ids if _cpp_len(i) >= VERILATOR_LIMIT)

    if not long_ids:
        return {}

    # Pre-populate 'used' with every short identifier already in the file so
    # that trimmed names never collide with pre-existing signals.
    used = {i for i in all_ids if _cpp_len(i) < VERILATOR_LIMIT}

    id_map = {}
    for ident in long_ids:
        segments = ident.split('.')
        chosen = None
        for start in range(len(segments)):
            base = '.'.join(segments[start:])
            if _cpp_len(base) >= VERILATOR_LIMIT:
                continue
            if base not in used:
                chosen = base
                break
            # base is taken; try adding a numeric suffix while still fitting
            n = 2
            while True:
                candidate = f'{base}_{n}'
                if _cpp_len(candidate) >= VERILATOR_LIMIT:
                    break  # suffix too long at this trim depth — drop more segments
                if candidate not in used:
                    chosen = candidate
                    break
                n += 1
            if chosen is not None:
                break
        if chosen is None:
            base = segments[-1][:VERILATOR_LIMIT - 1]
            if base not in used:
                chosen = base
            else:
                n = 2
                while True:
                    suffix = f'_{n}'
                    chosen = base[:VERILATOR_LIMIT - 1 - len(suffix)] + suffix
                    if chosen not in used:
                        break
                    n += 1
        id_map[ident] = chosen
        used.add(chosen)

    return id_map


def shorten_verilog(path: str) -> None:
    """Shorten escaped identifiers in a Verilog file in-place."""
    with open(path) as f:
        original = f.read()

    id_map = build_id_map(original)

    if not id_map:
        print(f'No identifiers reach {VERILATOR_LIMIT}-char limit in {path}')
        return

    escaped_re = re.compile(r'\\([^ \t\n;,)(]+)')

    def _replace(m: re.Match) -> str:
        short = id_map.get(m.group(1))
        if short is not None:
            return '\\' + short
        return m.group(0)

    shortened = escaped_re.sub(_replace, original)

    # Verify round-trip before writing: apply the inverse map and confirm we
    # recover the original exactly. This is done to make sure that the shortened
    # identifiers are unique and don't collide with any existing identifiers in the file.
    inverse = {v: k for k, v in id_map.items()}
    restored = escaped_re.sub(
        lambda m: '\\' + inverse.get(m.group(1), m.group(1)), shortened)
    if restored != original:
        orig_lines = original.splitlines()
        rest_lines = restored.splitlines()
        for i, (a, b) in enumerate(zip(orig_lines, rest_lines), 1):
            if a != b:
                raise AssertionError(
                    f'Round-trip failed at line {i}:\n'
                    f'  original: {a!r}\n'
                    f'  restored: {b!r}')
        raise AssertionError(
            f'Round-trip failed: line count mismatch '
            f'({len(orig_lines)} vs {len(rest_lines)})')

    with open(path, 'w') as f:
        f.write(shortened)
    print(f'Shortened {len(id_map)} identifiers in {path} (round-trip OK)')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('netlist', help='Verilog netlist to process in-place')
    args = parser.parse_args()

    shorten_verilog(args.netlist)


if __name__ == '__main__':
    main()
