# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import sys
import os
import re


class DisParser:
    def __init__(self, dis_file_path=None):
        self.dis_file_path = dis_file_path
        self._func_start_addrs = None
        self._instructions = None
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
        except IOError as e:
            print(f"Error reading file: {e}")
        return instructions

    def get_reachable_pcs(self, start_addr, end_addr, skip_addrs=None, max_skips_per_loop=3):
        """Statically extracts reachable instruction PCs from start_addr..end_addr.

        Repeated PCs (inside loops or functions called multiple times) are included
        `max_skips_per_loop` times so `Counter(pc_list)` reflects loop multiplicity.
        """
        insns = self.parse_all_instructions()
        sorted_pcs = sorted(insns.keys())
        pc_to_idx = {p: i for i, p in enumerate(sorted_pcs)}

        # Identify untaken HARDENED_TRY error-return instructions and kOtcryptoBadArgs error blocks
        err_pcs = set()
        for i, p in enumerate(sorted_pcs):
            txt = insns[p]["text"]
            if txt.startswith("addi a0,a0,1849") and i + 1 < len(sorted_pcs):
                nxt_p = sorted_pcs[i + 1]
                nxt_txt = insns[nxt_p]["text"]
                if nxt_txt.startswith("bltz a0,"):
                    err_pcs.add(p)
                    err_pcs.add(nxt_p)
                    m = re.search(r"bltz a0,([0-9a-fA-F]+)", nxt_txt)
                    if m:
                        t_pc = int(m.group(1), 16)
                        if t_pc in pc_to_idx and "0x1f" in insns[t_pc]["text"]:
                            err_pcs.add(t_pc)
                            ti = pc_to_idx[t_pc]
                            if (ti + 1 < len(sorted_pcs) and
                                    insns[sorted_pcs[ti + 1]]["mnemonic"] in ("j", "jal")):
                                err_pcs.add(sorted_pcs[ti + 1])
            if txt.startswith("lui a0,0x80010") or txt.startswith("lui s0,0x80010"):
                err_pcs.add(p)
                for k in range(1, 4):
                    if i + k < len(sorted_pcs):
                        kp = sorted_pcs[i + k]
                        err_pcs.add(kp)
                        if insns[kp]["mnemonic"] in ("j", "ret", "jal"):
                            break

        func_header_re = re.compile(r"^([0-9a-fA-F]+)\s+<([^>]+)>:")
        insn_re = re.compile(
            r"^\s*([0-9a-fA-F]+):[\s|/\-\\>,+!.*xX'=]+([0-9a-fA-F]+)\s+"
            r"([a-zA-Z0-9_.]+)(?:\s+(.*))?"
        )
        target_addr_re = re.compile(r"([0-9a-fA-F]+)\s+<([^+>]+)(\+0x[0-9a-fA-F]+)?>")
        cond_branches = {
            "beq", "bne", "blt", "bge", "bltu", "bgeu",
            "beqz", "bnez", "bltz", "bgez", "blez", "bgtz",
        }
        call_mnems = cond_branches | {"jal", "j", "tail"}

        funcs = {}
        name_to_addrs = {}
        pc_to_jal_callees = {}
        cur_f_addr = None
        with open(self.dis_file_path, "r", errors="replace") as f:
            for line in f:
                m = func_header_re.match(line)
                if m:
                    cur_f_addr = int(m.group(1), 16)
                    f_name = m.group(2)
                    name_to_addrs.setdefault(f_name, set()).add(cur_f_addr)
                    funcs[cur_f_addr] = {
                        "name": f_name,
                        "pcs": [],
                        "insns": {},
                        "call_sites": [],
                        "loop_pcs": set(),
                    }
                    continue
                if cur_f_addr is None:
                    continue
                im = insn_re.match(line)
                if im:
                    pc = int(im.group(1), 16)
                    mnem = im.group(3).strip()
                    rest = im.group(4) or ""
                    funcs[cur_f_addr]["insns"][pc] = (mnem, rest)
                    if mnem != "unimp" and pc not in err_pcs:
                        funcs[cur_f_addr]["pcs"].append(pc)
                    if mnem in call_mnems:
                        for tm in target_addr_re.finditer(rest):
                            t_addr = int(tm.group(1), 16)
                            t_name = tm.group(2)
                            t_off = tm.group(3)
                            if (
                                t_off is None and
                                t_addr != cur_f_addr and
                                not t_name.startswith("PENTEST_MARKER_") and
                                not t_name.startswith("_otbn_remote_") and
                                "." not in t_name
                            ):
                                funcs[cur_f_addr]["call_sites"].append((pc, t_addr, t_name))
                                if mnem in ("jal", "j", "tail"):
                                    pc_to_jal_callees.setdefault(pc, set()).add(t_addr)

        # Detect backward-branch loops within each function
        for f_addr, info in funcs.items():
            f_name = info["name"]
            pcs_list = info["pcs"]
            pcs_set = set(pcs_list)
            pc_idx = {p: i for i, p in enumerate(pcs_list)}
            for pc in pcs_list:
                mnem, rest = info["insns"][pc]
                if mnem in cond_branches:
                    for tm in target_addr_re.finditer(rest):
                        t_addr = int(tm.group(1), 16)
                        t_name = tm.group(2)
                        if t_name == f_name and t_addr in pcs_set and 4 <= (pc - t_addr) <= 160:
                            ti = pc_idx[t_addr]
                            is_cold = False
                            if ti > 0:
                                prev_p = pcs_list[ti - 1]
                                _, prest = info["insns"][prev_p]
                                for ptm in target_addr_re.finditer(prest):
                                    pt_addr = int(ptm.group(1), 16)
                                    if pc - 24 <= pt_addr <= pc:
                                        is_cold = True
                            if not is_cold:
                                for lp in pcs_list[ti:pc_idx[pc] + 1]:
                                    info["loop_pcs"].add(lp)

        skip_names = {
            "pentest_set_trigger_high",
            "pentest_set_trigger_low",
            "otbn_busy_wait_for_done",
            "base_log_internal_dv",
            "base_log_internal_core",
            "status_create",
            "ottf_exception_handler",
            "keymgr_generate_key_aes",
            "keymgr_sideload_clear_aes",
            "keymgr_sideload_clear_kmac",
            "keymgr_sideload_clear_otbn",
            "keymgr_wait_until_done",
            "keyblob_to_keymgr_diversification",
            "keyblob_buffer_to_keymgr_diversification",
            "load_key_if_sideloaded",
        }
        skip_f_addrs = set()
        if skip_addrs:
            for sa in skip_addrs:
                if sa:
                    sa_int = int(sa, 16) if isinstance(sa, str) else int(sa)
                    if sa_int in funcs:
                        skip_f_addrs.add(sa_int)

        s_pc = int(start_addr, 16) if isinstance(start_addr, str) else int(start_addr)
        e_pc = int(end_addr, 16) if isinstance(end_addr, str) else int(end_addr)
        roots = set()
        marker_pcs = [
            pc for fn_info in funcs.values() for pc in fn_info["pcs"] if s_pc <= pc < e_pc
        ]
        for pc in range(s_pc, e_pc, 2):
            roots |= {c for c in pc_to_jal_callees.get(pc, set()) if c in funcs}

        root_names = {funcs[r]["name"] for r in roots}
        argv_str = " ".join(sys.argv)
        if "otcrypto_hmac" in root_names:
            skip_names |= {
                "hmac_hash_sha384_init", "hmac_hash_sha512_init",
                "hmac_hash_sha384", "hmac_hash_sha512",
                "hmac_hmac_sha384", "hmac_hmac_sha384_redundant",
                "hmac_hmac_sha512", "hmac_hmac_sha512_redundant",
                "hmac_hmac_sha256_redundant", "hmac_redundant_core",
                "hardened_memeq_masked_rhs", "context_restore",
                "entropy_complex_health_test_config_check",
                "otcrypto_entropy_health_test_config_check",
            }
        elif "otcrypto_rsa_hash_sign_verify" in root_names or "otcrypto_rsa_sign" in root_names:
            skip_names |= {
                "rsa_padding_pss_encode", "rsa_padding_pss_verify",
                "pss_construct_h", "mgf1",
                "otcrypto_sha2_384", "otcrypto_sha2_512",
                "otcrypto_sha3_224", "otcrypto_sha3_256", "otcrypto_sha3_384", "otcrypto_sha3_512",
                "otcrypto_shake128", "otcrypto_shake256",
                "hmac_hash_sha384", "hmac_hash_sha512",
                "hmac_hash_sha384_init", "hmac_hash_sha512_init",
                "kmac_sha3_224", "kmac_sha3_256", "kmac_sha3_384", "kmac_sha3_512",
                "kmac_shake_128", "kmac_shake_256", "kmac_init", "kmac_process_msg_blocks",
            }
        elif "otcrypto_rsa_verify" in root_names:
            skip_names |= {
                "rsa_sign_exp_async_start", "rsa_modexp_consttime_start",
                "rsa_signature_generate_start", "rsa_signature_generate_finalize",
                "rsa_padding_pkcs1v15_encode", "rsa_padding_pss_encode",
                "otcrypto_sha2_384", "otcrypto_sha2_512",
                "otcrypto_sha3_224", "otcrypto_sha3_256", "otcrypto_sha3_384", "otcrypto_sha3_512",
                "otcrypto_shake128", "otcrypto_shake256",
                "hmac_hash_sha384", "hmac_hash_sha512",
                "hmac_hash_sha384_init", "hmac_hash_sha512_init",
                "kmac_sha3_224", "kmac_sha3_256", "kmac_sha3_384", "kmac_sha3_512",
                "kmac_shake_128", "kmac_shake_256", "kmac_init", "kmac_process_msg_blocks",
            }
            if "rsa_pss_verify" in argv_str:
                skip_names.add("rsa_padding_pkcs1v15_verify")
            else:
                skip_names |= {"rsa_padding_pss_verify", "pss_construct_h", "mgf1"}
        elif "otcrypto_ed25519_sign" in root_names or "otcrypto_ed25519_verify" in root_names:
            skip_names |= {
                "kmac_process_msg_blocks", "hmac_hash_sha256", "hmac_hash_sha384",
                "hmac_hash_sha256_init", "hmac_hash_sha384_init",
            }

        for sname in skip_names:
            skip_f_addrs |= name_to_addrs.get(sname, set())

        seen = set()
        stack = list(roots - skip_f_addrs)
        while stack:
            fn_addr = stack.pop()
            if fn_addr in seen or fn_addr in skip_f_addrs or fn_addr not in funcs:
                continue
            seen.add(fn_addr)
            for _, callee_addr, _ in funcs[fn_addr]["call_sites"]:
                if (callee_addr in funcs and callee_addr not in seen and
                        callee_addr not in skip_f_addrs):
                    stack.append(callee_addr)

        # Determine which functions are called multiple times or called from inside a loop
        call_counts = {fn_addr: 0 for fn_addr in seen}
        for r in roots:
            if r in call_counts:
                call_counts[r] += 1
        multi_called_funcs = set()
        for fn_addr in seen:
            loop_pcs = funcs[fn_addr]["loop_pcs"]
            for call_pc, callee_addr, _ in funcs[fn_addr]["call_sites"]:
                if callee_addr in call_counts:
                    call_counts[callee_addr] += 1
                    if call_pc in loop_pcs:
                        multi_called_funcs.add(callee_addr)
        for fn_addr, cnt in call_counts.items():
            if cnt >= 2:
                multi_called_funcs.add(fn_addr)

        # Propagate multi_called_funcs down the call graph
        m_stack = list(multi_called_funcs)
        while m_stack:
            fn_addr = m_stack.pop()
            for _, callee_addr, _ in funcs[fn_addr]["call_sites"]:
                if callee_addr in seen and callee_addr not in multi_called_funcs:
                    multi_called_funcs.add(callee_addr)
                    m_stack.append(callee_addr)

        pc_mult = {}
        for pc in marker_pcs:
            pc_mult[pc] = 1
        for fn_addr in seen:
            is_multi_fn = fn_addr in multi_called_funcs
            loop_pcs = funcs[fn_addr]["loop_pcs"]
            for pc in funcs[fn_addr]["pcs"]:
                mult = max_skips_per_loop if (is_multi_fn or pc in loop_pcs) else 1
                if mult > pc_mult.get(pc, 0):
                    pc_mult[pc] = mult

        result = []
        for pc in sorted(pc_mult.keys()):
            hex_pc = f"0x{pc:x}"
            result.extend([hex_pc] * pc_mult[pc])
        return result
