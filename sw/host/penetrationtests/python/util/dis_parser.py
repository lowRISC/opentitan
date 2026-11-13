# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys
import os
import re


class DisParser:
    _instances = []
    _call_return_map = {}

    def __init__(self, dis_file_path=None):
        self.dis_file_path = dis_file_path
        self._func_start_addrs = None
        self._instructions = None
        if not os.path.exists(self.dis_file_path):
            print(f"Error: File not found at path: {self.dis_file_path}")
            sys.exit(1)
        DisParser._instances.append(self)

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
        if self._instructions is None:
            self.parse_all_instructions()
        if hasattr(self, "_next_pc_map") and self._next_pc_map:
            pc_int = int(pc_address, 16) if isinstance(pc_address, str) else int(pc_address)
            nxt = self._next_pc_map.get(pc_int)
            if nxt is not None:
                return f"0x{nxt:x}"
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
        if self._func_start_addrs is not None:
            return self._func_start_addrs.get(function_name)

        escaped_name = re.escape(function_name)
        pattern = re.compile(r"^([0-9a-fA-F]{1,16})\s*<" + escaped_name + r">:")
        try:
            with open(self.dis_file_path, "r") as f:
                for line in f:
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

    def parse_all_instructions(self):
        """Parse all disassembled instructions and their source locations by PC."""
        func_header_re = re.compile(r"^([0-9a-fA-F]+)\s+<([^>]+)>:")
        src_line_re = re.compile(r"^([^\s:][^:]*\.[chS]):([0-9]+)")
        insn_line_re = re.compile(
            r"^\s*([0-9a-fA-F]+):[\s|/\-\\>,+!.*xX'=]+([0-9a-fA-F]+)\s+"
            r"([a-zA-Z0-9_.]+)(?:\s+([^;#<]*))?"
        )
        if self._instructions is not None:
            return self._instructions
        instructions = {}
        func_addrs = {}
        current_func = ""
        current_src = ""
        current_filepath = ""
        current_lineno = 0
        pending_c_line = ""
        in_src_header = False
        try:
            with open(self.dis_file_path, "r", errors="replace") as f:
                for line in f:
                    fh = func_header_re.match(line)
                    if fh:
                        current_func = fh.group(2)
                        func_addrs.setdefault(current_func, f"0x{fh.group(1)}")
                        current_src = ""
                        current_filepath = ""
                        current_lineno = 0
                        pending_c_line = ""
                        in_src_header = False
                        continue
                    sl = src_line_re.match(line.strip())
                    if sl:
                        current_filepath = sl.group(1).removeprefix("/proc/self/cwd/")
                        current_lineno = int(sl.group(2))
                        current_src = f"{os.path.basename(current_filepath)}:{current_lineno}"
                        pending_c_line = ""
                        in_src_header = True
                        continue
                    m = insn_line_re.match(line)
                    if not m:
                        s_line = line.strip()
                        if (
                            in_src_header and
                            current_lineno and
                            s_line and
                            not s_line.startswith("//") and
                            not s_line.startswith("/*") and
                            not s_line.startswith("*") and
                            not s_line.endswith("():")
                        ):
                            pending_c_line = s_line
                        continue
                    pc = int(m.group(1), 16)
                    insn_bits = int(m.group(2), 16)
                    mnemonic = m.group(3).strip()
                    operands_raw = (m.group(4) or "").strip()
                    raw_text = f"{mnemonic} {operands_raw}".strip()
                    if current_src:
                        loc = (
                            f"{current_func} ({current_src})"
                            if current_func
                            else current_src
                        )
                    else:
                        loc = current_func
                    c_comment = f"   /* {pending_c_line} */" if pending_c_line else ""
                    pending_c_line = ""
                    in_src_header = False
                    instructions[pc] = {
                        "insn_bits": insn_bits,
                        "mnemonic": mnemonic,
                        "operands": operands_raw,
                        "text": raw_text + c_comment,
                        "source_loc": loc,
                        "func": current_func,
                        "filepath": current_filepath,
                        "lineno": current_lineno,
                    }
            self._func_start_addrs = func_addrs
            self._instructions = instructions
            sorted_pcs = sorted(instructions.keys())
            self._next_pc_map = {
                sorted_pcs[i]: sorted_pcs[i + 1]
                for i in range(len(sorted_pcs) - 1)
            }
            for pc, nxt in self._next_pc_map.items():
                info = instructions[pc]
                if info["mnemonic"] in ("jal", "jalr", "c.jal", "c.jalr") and not info[
                    "operands"
                ].startswith(("t0,", "zero,", "x0,")):
                    DisParser._call_return_map[pc] = nxt
        except IOError as e:
            print(f"Error reading file: {e}")
        return instructions
