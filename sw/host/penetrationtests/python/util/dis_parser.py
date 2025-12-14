# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys
import os
import re


class DisParser:
    def __init__(self, dis_file_path=None):
        self.dis_file_path = dis_file_path
        if not os.path.exists(self.dis_file_path):
            print(f"Error: File not found at path: {self.dis_file_path}")
            sys.exit(1)

    def get_function_addresses(self, function_name):
        try:
            with open(self.dis_file_path, "r") as f:
                dis_content = f.read()
        except IOError as e:
            print(f"Error reading file: {e}")
            return []

        addresses = []
        escaped_name = re.escape(function_name)
        lines = dis_content.splitlines()

        jump_line_pattern = re.compile(r"^\s*([0-9a-fA-F]{1,16}):.*?<" + escaped_name + r">")

        next_addr_pattern = re.compile(r"^\s*([0-9a-fA-F]{1,16}):")

        for i, line in enumerate(lines):
            match = jump_line_pattern.match(line)
            if match:
                jump_address = match.group(1)

                for j in range(i + 1, len(lines)):
                    next_line = lines[j]

                    if not next_line.strip():
                        continue

                    next_match = next_addr_pattern.match(next_line)

                    if next_match:
                        address_after_jump = next_match.group(1)
                        addresses.append((f"0x{jump_address}", f"0x{address_after_jump}"))
                        break

        return addresses

    def parse_next_instruction(self, pc_address):
        if pc_address.startswith("0x"):
            pc_address = pc_address[2:]

        instruction_addr_pattern = re.compile(r"^\s*([0-9a-fA-F]{1,16}):")

        found_current_address = False

        try:
            with open(self.dis_file_path, "r") as f:
                for line in f:
                    match = instruction_addr_pattern.match(line)

                    if match:
                        line_address = match.group(1)

                        if not found_current_address:
                            if line_address == pc_address:
                                found_current_address = True
                        else:
                            return f"0x{line_address}"

                if found_current_address:
                    return None
                else:
                    print(f"Error: Address 0x{pc_address} not found in disassembly.")
                    return None

        except IOError as e:
            print(f"Error reading file: {e}")
            return None

    def get_function_start_address(self, function_name):
        try:
            with open(self.dis_file_path, "r") as f:
                for line in f:
                    escaped_name = re.escape(function_name)
                    pattern = re.compile(r"^([0-9a-fA-F]{1,16})\s*<" + escaped_name + r">:")

                    match = pattern.search(line)
                    if match:
                        return f"0x{match.group(1)}"

        except IOError as e:
            print(f"Error reading file: {e}")
            return None

        return None

    def get_function_end_address(self, function_name):
        """
        Finds the address of the last 'ret' instruction in a function.
        """
        try:
            with open(self.dis_file_path, "r") as f:
                escaped_name = re.escape(function_name)
                start_pattern = re.compile(r"^[0-9a-fA-F]+\s+<" + escaped_name + r">:")
                any_func_pattern = re.compile(r"^[0-9a-fA-F]+\s+<.*>:")
                inst_pattern = re.compile(r"^\s*([0-9a-fA-F]+):\s+.*?\s+([a-zA-Z\.]+)")

                in_function = False
                function_instructions = []

                for line in f:
                    if not in_function:
                        if start_pattern.search(line):
                            in_function = True
                    else:
                        if any_func_pattern.search(line):
                            break

                        inst_match = inst_pattern.search(line)
                        if inst_match:
                            address = inst_match.group(1)
                            mnemonic = inst_match.group(2)
                            function_instructions.append((address, mnemonic))

                if not in_function:
                    print(f"Error: {function_name} not found")
                    return None

                for address, mnemonic in reversed(function_instructions):
                    if mnemonic == "ret":
                        return f"0x{address}"

                print(f"Warning: No 'ret' instruction found for {function_name}")
                return None

        except IOError as e:
            print(f"Error reading file: {e}")
            return None

    def get_marker_addresses(self, marker_name):
        return [
            self.get_function_start_address(marker_name + "_START"),
            self.get_function_start_address(marker_name + "_END"),
        ]

    def get_inlined_function_address(self, function_name):
        try:
            with open(self.dis_file_path, "r") as f:
                escaped_name = re.escape(function_name)
                marker_pattern = re.compile(r"^\s*" + escaped_name + r"\(\):")

                inst_address_pattern = re.compile(r"^\s*[\|\+\-\s]*([0-9a-fA-F]{1,16}):")

                found_marker = False
                for line in f:
                    if not found_marker:
                        if marker_pattern.search(line):
                            found_marker = True
                    else:
                        match = inst_address_pattern.search(line)
                        if match:
                            return f"0x{match.group(1)}"

        except IOError as e:
            print(f"Error reading file: {e}")
            return None

        print(f"Error: Inlined function address not found for {function_name}")
        return None
