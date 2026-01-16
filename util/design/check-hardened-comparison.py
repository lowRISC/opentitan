#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Script to check for ineffective hardened comparisons in disassembly files.

This tool searches for patterns in assembly code where a branch instruction
compares a register to itself, which often indicates that hardening
countermeasures have been optimized away incorrectly.
"""

import argparse
import re

# Possible ops defined in sw/device/lib/base/hardened.h
HARDENED_CHECK_OPS = [
    "beq",
    "bne",
    "bltu",
    "bgtu",
    "bleu",
    "bgeu",
]
OPS_RE = "|".join(map(re.escape, HARDENED_CHECK_OPS))
# Matches a branch instruction, followed by two identical registers.
# e.g. beq a0, a0, .L_HARDENED_BAD_123
INEFFECTIVE_REGEX = re.compile(rf"\s({OPS_RE})\s+([a-z0-9]+),\s*\2,")


def check_ineffective_hardening(path: str) -> bool:
    """Checks for ineffective hardened comparisons in a disassembly file.

    It searches for branch instructions where the two registers being compared
    are the same, which typically indicates a failure in hardened comparison
    logic. If such patterns are found, it groups nearby occurrences and prints
    them with surrounding context.

    Args:
        path: Path to the disassembly (.dis) file to check.

    Returns:
        True if no ineffective comparisons were found, False otherwise.
    """

    # Read the file and search for ineffective hardened comparisons.
    with open(path, "r") as f:
        lines = f.readlines()
    matches = []
    for i, line in enumerate(lines):
        m = INEFFECTIVE_REGEX.search(line)
        if m:
            matches.append(i)

    if not matches:
        return True

    # Group connected chunks
    groups = []
    if matches:
        current_group = [matches[0]]
        for i in range(1, len(matches)):
            if matches[i] - matches[i - 1] <= 10:
                current_group.append(matches[i])
            else:
                groups.append(current_group)
                current_group = [matches[i]]
        groups.append(current_group)

    print("=" * 20)
    # Print the chunks with some context
    for group in groups:
        start = max(0, min(group) - 5)
        end = min(len(lines), max(group) + 6)
        for j in range(start, end):
            prefix = ">> " if j in group else "   "
            print(f"{prefix}{lines[j].strip()}")
        print("-" * 20)
    print(f"File: {path}")
    print(f"Found {len(matches)} ineffective comparison(s) in {len(groups)} group(s).")
    print("=" * 20)
    print('')
    return False


def main():
    """Parses command line arguments and runs the hardening check on provided files.
    """
    parser = argparse.ArgumentParser(
        description="Check for ineffective hardening in disassembly files.")
    parser.add_argument("files", nargs="+", help="Disassembly files to check")
    args = parser.parse_args()

    overall_status = True
    results = []
    for path in args.files:
        status = check_ineffective_hardening(path)
        results.append((path, status))
        if not status:
            overall_status = False

    print("Summary:")
    for path, status in results:
        label = "   " if status else ">> "
        print(f"{label} {path}")

    if not overall_status:
        exit(1)


if __name__ == "__main__":
    main()
