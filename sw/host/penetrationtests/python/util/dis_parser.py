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

        jump_line_pattern = re.compile(r"^\s*([0-9a-fA-F]{8}):.*?<" + escaped_name + r">")

        next_addr_pattern = re.compile(r"^\s*([0-9a-fA-F]{8}):")

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

        instruction_addr_pattern = re.compile(r"^\s*([0-9a-fA-F]{8}):")

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
                    pattern = re.compile(r"^([0-9a-fA-F]{8})\s*<" + escaped_name + r">:")

                    match = pattern.search(line)
                    if match:
                        return f"0x{match.group(1)}"

        except IOError as e:
            print(f"Error reading file: {e}")
            return None

        return None

    def is_trigger_in_function_of_address(self, address_str):
        try:
            target_addr_int = int(address_str, 16)
        except (ValueError, TypeError):
            print(f"Error: Invalid address format: {address_str}")
            return False

        instruction_addr_pattern = re.compile(r"^\s*([0-9a-fA-F]{8}):")
        func_name_pattern = re.compile(r"^([_a-zA-Z0-9]+)\(\):$")

        function_starts = []
        pending_func_name = None
        try:
            with open(self.dis_file_path, "r") as f:
                for line in f:
                    name_match = func_name_pattern.search(line)
                    if name_match:
                        pending_func_name = name_match.group(1)
                        continue

                    if pending_func_name:
                        addr_match = instruction_addr_pattern.match(line)
                        if addr_match:
                            addr = int(addr_match.group(1), 16)
                            function_starts.append({"addr": addr, "name": pending_func_name})
                            pending_func_name = None  # Reset after finding the address
        except IOError as e:
            print(f"Error reading disassembly file: {e}")
            return False

        if not function_starts:
            print("Error: No functions found in the disassembly file.")
            return False

        function_starts.sort(key=lambda x: x["addr"])

        containing_func_start = None
        containing_func_end = float("inf")

        for i, func in enumerate(function_starts):
            if func["addr"] <= target_addr_int:
                containing_func_start = func["addr"]
                if i + 1 < len(function_starts):
                    containing_func_end = function_starts[i + 1]["addr"]
                else:
                    containing_func_end = float("inf")
            else:
                break

        if containing_func_start is None:
            print(f"Error: Could not find a function containing address {address_str}")
            return False

        try:
            with open(self.dis_file_path, "r") as f:
                for line in f:
                    addr_match = instruction_addr_pattern.match(line)
                    if not addr_match:
                        continue

                    line_addr_int = int(addr_match.group(1), 16)

                    if containing_func_start <= line_addr_int < containing_func_end:
                        if "pentest_set_trigger_high" in line or "pentest_set_trigger_low" in line:
                            return True
        except IOError as e:
            print(f"Error re-reading disassembly file: {e}")
            return False

        return False

    def get_trigger_addresses_for_function(self, function_name):
        try:
            with open(self.dis_file_path, "r") as f:
                lines = f.readlines()
        except IOError as e:
            print(f"Error reading file: {e}")
            return None

        func_def_pattern = re.compile(r"^\s*" + re.escape(function_name) + r"\(\):")
        addr_pattern = re.compile(r"^\s*([0-9a-fA-F]{8}):")

        function_start_index = -1
        for i, line in enumerate(lines):
            if func_def_pattern.match(line):
                function_start_index = i
                break

        if function_start_index == -1:
            print(f"Error: Function '{function_name}' not found in disassembly.")
            return None

        high_trigger_addr = None
        low_trigger_addr = None

        for i in range(function_start_index - 1, -1, -1):
            line = lines[i]
            if "pentest_set_trigger_high" in line:
                match = addr_pattern.match(line)
                if match:
                    high_trigger_addr = f"0x{match.group(1)}"
                    break

        for i in range(function_start_index + 1, len(lines)):
            line = lines[i]
            if "pentest_set_trigger_low" in line and line.strip().endswith("():"):
                for j in range(i, -1, -1):
                    previous = lines[j]
                    match = addr_pattern.match(previous)
                    if match:
                        low_trigger_addr = f"0x{match.group(1)}"
                        break
                if low_trigger_addr:
                    break

        if high_trigger_addr and low_trigger_addr:
            return (high_trigger_addr, low_trigger_addr)
        else:
            if not high_trigger_addr:
                print(f"Error: 'pentest_set_trigger_high' not found above '{function_name}'.")
            if not low_trigger_addr:
                print(f"Error: 'pentest_set_trigger_low' not found below '{function_name}'.")
            return None
