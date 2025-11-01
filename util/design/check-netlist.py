#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Checks the generated netlist for suspicious synthesis optimizations

    Specifically, this script parses the netlist for suspicious patterns. These checks do *not*
    replace a final manual inspection of the netlist, but help to find problems early in the design!
"""

import sys
import re


def parse_expressions(filename):
    # list of all relevant preserved instances (Adjust to the names in the used prim implementation)
    size_only_patterns = ["u_size_only", "u_size_only_xor", "u_size_only_xnor", "u_size_only_and",
                          "u_size_only_mux", "u_size_only_flop", "u_size_only_buf",
                          "u_size_only_clock_gate"]

    # Regex to find ".lc_en_i, ( ... )" and capture the content
    pattern_lc_in = re.compile(r'\.lc_en_i \((.*?)\)')
    # Regex to find ".mubi_i, ( ... )" and capture the content
    pattern_mubi_in = re.compile(r'\.mubi_i \((.*?)\)')
    # Regex to find "assign mubi_o[*] = " const"
    pattern_mubi_const = re.compile(r'assign\s+([^=\s]*mubi_o[^=\s]*)\s*=\s*(.*?)\'b[01]+;')
    # Regex to find "assign test*_o[*] = " const"
    pattern_test_const = re.compile(r'assign\s+(test_.*_o.*?)\s*=\s*(.*?)\'b[01]+;')
    # tie low/high pattern
    pattern_tie_low_high = re.compile(r"\'b[01]")
    # pattern to find a module name
    pattern_module = re.compile(r'^\s*module\s+([a-zA-Z_][a-zA-Z0-9_]*)')
    # valid mubi4, mubi8, mubi12, lc patterns
    mubi_allowed_patterns = ["12'b100101101001", "12'b11010010110", "8'b1101001", "8'b10010110",
                             "4'b110", "4'b1001"]
    lc_allowed_patterns = ["4'b101", "4'b1010"]

    errors = 0
    size_only_count = [0] * len(size_only_patterns)

    module_name = "unknown"
    error_modules = []  # List to store module names when errors are found

    try:
        with open(filename, 'r') as file:
            lines = list(file)
            for line_number, line in enumerate(lines, 1):
                # Parse for module name: "module xxx(..."
                match_module = pattern_module.match(line)
                if match_module:
                    module_name = match_module.group(1)

                # check for constant lc signals
                match = pattern_lc_in.search(line)
                if match:
                    content = match.group(1).strip()
                    if pattern_tie_low_high.search(content):
                        if content not in lc_allowed_patterns:
                            print(f"Error: Found invalid constant lc_en_i in module {module_name}"
                                  f"on line {line_number}:")
                            print(f"  Full line: {line.strip()}")
                            print(f"  Content parsed: {content}")
                            print("-" * 80)
                            errors += 1
                            if module_name not in error_modules:
                                error_modules.append(module_name)

                # check for constant mubi signals
                match = pattern_mubi_in.search(line)
                if match:
                    content = match.group(1).strip()
                    if pattern_tie_low_high.search(content):
                        if content not in mubi_allowed_patterns:
                            print(f"Error: Found invalid constant mubi_i in module {module_name}"
                                  f"on line {line_number}:")
                            print(f"  Full line: {line.strip()}")
                            print(f"  Content parsed: {content}")
                            print("-" * 80)
                            errors += 1
                            if module_name not in error_modules:
                                error_modules.append(module_name)

                # check for constant mubi signals
                match = pattern_mubi_const.search(line)
                if match:
                    print(f"Error: Found tied low/high mubi bit in module {module_name}"
                          f"on line {line_number}:")
                    print(f"  Full line: {line.strip()}")
                    print("-" * 80)
                    errors += 1
                    if module_name not in error_modules:
                        error_modules.append(module_name)

                # check for constant test-outputs in prim_sdc_example
                if (module_name == "prim_sdc_example"):
                    match = pattern_test_const.search(line)
                    if match:
                        print(f"Error: Found tied low/high test*_o* in module {module_name}"
                              f"on line {line_number}:")
                        print(f"  Full line: {line.strip()}")
                        print("-" * 80)
                        errors += 1
                        if module_name not in error_modules:
                            error_modules.append(module_name)

                # check for size_only instances
                for i in range(len(size_only_patterns)):
                    if size_only_patterns[i] in line:
                        size_only_count[i] += 1

            print("\n" + "=" * 80)
            print("Final Summary:")
            print("-" * 80)
            print("Found the following size_only instances:")
            print("-" * 80)
            for i in range(1, len(size_only_patterns)):
                print(f"{size_only_patterns[i]:<30}{size_only_count[i]}")
            other_count = size_only_count[0] - sum(size_only_count[1:len(size_only_count)])
            print(f"{'others':<30}{other_count}")
            print("-" * 80)
            print(f"{'Total':<30}{size_only_count[0]}")
            print("=" * 80)
            print(f"Found {errors} potential netlist problems in {len(error_modules)} modules!")
            print("=" * 80)

    except FileNotFoundError:
        print(f"Error: The file '{filename}' was not found.")

    return errors


if __name__ == "__main__":
    print("=" * 80)
    print("DISCLAIMER:\nThis script parses a synthesized netlist for suspicious constructs.\n"
          "It does not guarantee that there are no issues in the netlist(!)")
    print("=" * 80 + '\n\n')
    if len(sys.argv) < 2:
        print("Usage: ./check-netlist.py <netlist_filename>")
        sys.exit(2)
    file_to_parse = sys.argv[1]
    errors = parse_expressions(file_to_parse)
    if (errors > 0):
        sys.exit(1)
