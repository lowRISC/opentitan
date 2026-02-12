#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Checks the generated netlist for suspicious synthesis optimizations

Specifically, this script parses the netlist for suspicious patterns. These
checks do *not* replace a final manual inspection of the netlist, but help to
find problems early in the design!
"""

import sys
import re
import argparse


def hr(char: str) -> None:
    print(char * 80)


class Parser:
    # List of patterns we want to use for finding size_only constraints.
    size_only_patterns = [
        "u_size_only",
        "u_size_only_xor", "u_size_only_xnor", "u_size_only_and",
        "u_size_only_mux", "u_size_only_flop", "u_size_only_buf",
        "u_size_only_clock_gate"
    ]

    # Regex to find ".lc_en_i, ( ... )" and capture the content
    pattern_lc_in = re.compile(r'\.lc_en_i \((.*?)\)')

    # Regex to find ".mubi_i, ( ... )" and capture the content
    pattern_mubi_in = re.compile(r'\.mubi_i \((.*?)\)')

    # Regex to find "assign mubi_o[*] = " const"
    pattern_mubi_const = re.compile(r'assign\s+([^=\s]*mubi_o[^=\s]*)\s*'
                                    r'=\s*(.*?)\'b[01]+;')

    # Regex to find "assign test*_o[*] = " const"
    pattern_test_const = re.compile(r'assign\s+(test_.*_o.*?)\s*='
                                    r'\s*(.*?)\'b[01]+;')

    # tie low/high pattern
    pattern_tie_low_high = re.compile(r"\'b[01]")

    # pattern to find a module name
    pattern_module = re.compile(r'^\s*module\s+([a-zA-Z_][a-zA-Z0-9_]*)')

    # valid mubi4, mubi8, mubi12 patterns
    mubi_allowed_patterns = ["12'b100101101001", "12'b11010010110",
                             "8'b1101001", "8'b10010110",
                             "4'b110", "4'b1001"]

    # valid lc patterns
    lc_allowed_patterns = ["4'b101", "4'b1010"]

    # A count of how many instances we have seen of each of the size_only
    # patterns (ordered the same as size_only_patterns).
    size_only_count: list[int] = [0 for pat in size_only_patterns]

    # The name of the module (if known)
    module_name: str | None = None

    # Number of errors seen so far
    errors: int = 0

    # A list of module names where errors have been found
    error_modules: set[str] = set()

    def describe_module(self) -> str:
        return ('unknown module' if self.module_name is None
                else f'module {self.module_name}')

    def on_error(self,
                 linenum: int, line: str,
                 desc: str, bad_match: str | None) -> None:
        print(f"Error: {desc} in {self.describe_module()}, line {linenum}:")
        print(f"  Full line: {line.strip()}")
        if bad_match is not None:
            print(f"  Content parsed: {bad_match}")

        hr('-')

        self.errors += 1
        if self.module_name is not None:
            self.error_modules.add(self.module_name)

    def take_line(self, line_number: int, line: str) -> None:
        # Parse for module name: "module xxx(..."
        match_module = Parser.pattern_module.match(line)
        if match_module:
            self.module_name = match_module.group(1)

        # check for constant lc signals
        lc_match = Parser.pattern_lc_in.search(line)
        if lc_match:
            content = lc_match.group(1).strip()
            if Parser.pattern_tie_low_high.search(content):
                if content not in Parser.lc_allowed_patterns:
                    self.on_error(line_number, line,
                                  'invalid constant lc_en_i', content)

        # check for constant mubi_i signals
        mubi_i_match = Parser.pattern_mubi_in.search(line)
        if mubi_i_match:
            content = mubi_i_match.group(1).strip()
            if Parser.pattern_tie_low_high.search(content):
                if content not in Parser.mubi_allowed_patterns:
                    self.on_error(line_number, line,
                                  'invalid constant mubi_i', content)

        # check for constant mubi_o signals
        if Parser.pattern_mubi_const.search(line):
            self.on_error(line_number, line, 'tied low/high mubi bit', None)

        # check for constant test-outputs in prim_sdc_example
        if ((self.module_name == "prim_sdc_example" and
             Parser.pattern_test_const.search(line))):
            self.on_error(line_number, line, 'tied low/high test*_o*', None)

        # Count size_only instances
        for i, pattern in enumerate(Parser.size_only_patterns):
            if pattern in line:
                self.size_only_count[i] += 1

    def report(self) -> None:
        hr('=')
        print("Final Summary:")
        hr('-')
        print("Found the following size_only instances:")
        hr('-')

        # Print the number of specific size_only matches that we have seen
        # (with a suffix from _xor, _xnor, _only_and, ...)
        specific_count = 0
        for i, pattern in enumerate(Parser.size_only_patterns[1:], 1):
            print(f"{pattern:<30}{self.size_only_count[i]}")
            specific_count += self.size_only_count[i]

        # Each of those specific hits will also have matched u_size_only (the
        # first pattern). Subtracting specific_count from size_only_count[0]
        # gives the number of lines that are match u_size_only but don't match
        # one of the specific patterns.
        other_count = self.size_only_count[0] - specific_count
        print(f"{'others':<30}{other_count}")

        hr('-')

        # Since we know that every match for a specific case will also match
        # the first pattern, the number of lines that match equals
        # size_only_count[0]
        print(f"{'Total':<30}{self.size_only_count[0]}")
        hr('=')

        print(f"Found {self.errors} potential netlist problems "
              f"in {len(self.error_modules)} modules!")
        hr('=')


def parse_expressions(filename):
    try:
        with open(filename, 'r') as file:
            lines = list(file)
    except FileNotFoundError:
        print(f"Error: The file '{filename}' was not found.")
        return 1

    parser = Parser()
    for idx, line in enumerate(lines, 1):
        parser.take_line(idx, line)
    parser.report()

    return parser.errors


if __name__ == "__main__":

    parser = argparse.ArgumentParser(
        description = "Parses a synthesized netlist for suspicious constructs and counts all"
                      "size_only instances",
        epilog = "Note: This script does not guarantee that there are no issues in the netlist (!)"
    )

    parser.add_argument(
        "netlist_filename",
        type=str,
        help="The path to the netlist file (e.g., netlist.v) to be parsed."
    )

    args = parser.parse_args()
    hr('=')
    print("DISCLAIMER:\n"
          "This script parses a synthesized netlist for suspicious constructs.\n"
          "It does not guarantee that there are no issues in the netlist(!)")
    hr('=')
    print('\n')

    file_to_parse = args.netlist_filename
    errors = parse_expressions(file_to_parse)

    if (errors > 0):
        sys.exit(1)
    else:
        sys.exit(0)
