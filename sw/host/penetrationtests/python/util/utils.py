# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import hashlib
import json
import os
import random
import re
import struct
import sys


def compare_json_data(
    actual_data: dict, expected_data: dict, ignored_keys: set
) -> bool:
    expected_comparable_keys = set(expected_data.keys()) - ignored_keys
    actual_comparable_keys = set(actual_data.keys()) - ignored_keys

    assert expected_comparable_keys == actual_comparable_keys

    for key in expected_comparable_keys:
        assert expected_data[key] == actual_data[key], (
            f"Found {actual_data[key]} but expected {expected_data[key]} under the key: {key}"
        )


def to_signed32(n_unsigned):
    n_unsigned = n_unsigned & 0xFFFFFFFF
    if n_unsigned >= 0x80000000:
        return n_unsigned - 0x100000000
    return n_unsigned


def bytes_to_words(byte_array):
    if not isinstance(byte_array, (bytes, bytearray)):
        raise TypeError("Input must be a bytes object or bytearray.")

    word_list = []
    for i in range(0, len(byte_array), 4):
        chunk = byte_array[i: i + 4]
        word = struct.unpack(">I", chunk)[0]
        word_list.append(word)
    return word_list


def words_to_bytes(dword_array):
    if not isinstance(dword_array, list):
        raise TypeError("Input must be a list of 32-bit integers.")

    byte_list = bytearray()
    for dword in dword_array:
        if not isinstance(dword, int) or not (0 <= dword <= 0xFFFFFFFF):
            raise ValueError(
                "Each element in the array must be a 32-bit integer (0 to 0xFFFFFFFF)."
            )
        byte_list.extend(struct.pack(">I", dword))
    return bytes(byte_list)


def array_to_int(data_array):
    result = 0
    for i, val in enumerate(data_array):
        result |= (val & 0xFFFFFFFF) << (i * 32)
    return result


def int_to_array(large_int):
    data_array = [0] * 8
    for i in range(8):
        data_array[i] = (large_int >> (i * 32)) & 0xFFFFFFFF
    return data_array


def pad_with_zeros(array, length):
    padded_arr = list(array)
    zeros_to_add = max(0, length - len(padded_arr))
    padded_arr.extend([0] * zeros_to_add)
    return padded_arr


def is_majority_zeros(array, total_length=None):
    if total_length is None:
        total_length = len(array)
    if total_length <= 0 or total_length > len(array):
        return False

    array = array[:total_length]
    zero_count = array.count(0)

    return zero_count > (total_length / 2)


def is_partial_collision(out1, out2, match_threshold_ratio=0.75, valid_len=None):
    """
    Checks if two outputs share a significant number of identical bytes.
    Useful for catching FI vulnerabilities where a skipped instruction
    causes a partial state collision rather than an exact match.
    """
    if out1 is None or out2 is None or len(out1) == 0:
        return False

    if valid_len is not None:
        out1 = out1[:valid_len]
        out2 = out2[:valid_len]

    if len(out1) != len(out2):
        return False

    matching_bytes = sum(1 for a, b in zip(out1, out2) if a == b)
    match_ratio = matching_bytes / len(out1)

    return match_ratio >= match_threshold_ratio


def add_test_selection_args(parser: argparse.ArgumentParser):
    """Adds test selection and listing arguments to the argument parser."""
    parser.add_argument(
        "--test",
        "--test_name",
        "--test-name",
        type=str,
        default=None,
        help="Name of the specific test method to run (e.g. test_p384_verify or p384_verify)",
    )
    parser.add_argument(
        "--list-tests",
        "--list",
        dest="list_tests",
        action="store_true",
        default=False,
        help="List all available tests in this suite and exit",
    )
    parser.add_argument(
        "--num-skips",
        type=int,
        default=0,
        help="Number of random instruction skips to perform (0 for exhaustive)",
    )
    parser.add_argument(
        "--dump-json",
        action="store_true",
        default=False,
        help="Dump FI campaign results and metadata to JSON",
    )


def resolve_test_name(requested_name: str, available_tests: list):
    """Resolves a user-provided test name against a list of available test methods.

    Supports:
    - Exact test method name (e.g. 'test_p384_verify')
    - Short name without 'test_' prefix (e.g. 'p384_verify')
    - Qualified name (e.g. 'AsymCryptolibFiSim.test_p384_verify')
    - Case-insensitive matching
    - Unique substring matching

    Returns the resolved test method name, or None if no match or ambiguous.
    """
    if not requested_name:
        return None
    req = requested_name.strip()
    if "." in req:
        req = req.split(".")[-1]
    if req in available_tests:
        return req
    if f"test_{req}" in available_tests:
        return f"test_{req}"

    # Case-insensitive exact or short match
    exact_ci = [
        t
        for t in available_tests
        if t.lower() == req.lower() or
        (t.startswith("test_") and t[5:].lower() == req.lower())
    ]
    if len(exact_ci) == 1:
        return exact_ci[0]

    # Substring match
    sub = [t for t in available_tests if req.lower() in t.lower()]
    if len(sub) == 1:
        return sub[0]

    return None


def get_selected_test_argv(
    test_class,
    requested_name=None,
    config_args=None,
    list_tests=False,
):
    """Resolves unittest argv for running all tests or a single test.

    Args:
        test_class: The unittest.TestCase subclass.
        requested_name: Optional test name passed via --test flag.
        config_args: Optional list of remaining unparsed CLI args. If a positional
                     arg in config_args matches a test, it is consumed and removed.
        list_tests: Whether --list-tests was requested.

    Returns:
        List[str] suitable to pass as argv to unittest.main(argv=...).
    """
    # Collect available test methods preserving class definition order
    available_tests = [
        m
        for m in test_class.__dict__.keys()
        if m.startswith("test_") and callable(getattr(test_class, m))
    ]
    for m in dir(test_class):
        if (
            m.startswith("test_") and
            callable(getattr(test_class, m)) and
            m not in available_tests
        ):
            available_tests.append(m)

    if list_tests:
        print(f"Available tests in {test_class.__name__}:")
        for t in available_tests:
            short_name = t[5:] if t.startswith("test_") else t
            print(f"  - {t}  (or {short_name})")
        sys.exit(0)

    # Check if a positional argument in config_args specifies a test
    if not requested_name and config_args is not None:
        for arg in list(config_args):
            if arg.startswith("-"):
                continue
            resolved = resolve_test_name(arg, available_tests)
            if resolved:
                requested_name = resolved
                config_args.remove(arg)
                break

    if requested_name:
        matched = resolve_test_name(requested_name, available_tests)
        if not matched:
            print(f"Error: Unknown or ambiguous test '{requested_name}'.")
            print(f"Available tests in {test_class.__name__}:")
            for t in available_tests:
                short_name = t[5:] if t.startswith("test_") else t
                print(f"  - {t}  (or {short_name})")
            sys.exit(1)

        print(
            f"[TEST SELECTION] Running single test: {test_class.__name__}.{matched}\n",
            flush=True,
        )
        return [sys.argv[0], f"{test_class.__name__}.{matched}"]

    return [sys.argv[0]]


class _StdoutSpy:
    def __init__(self, stream, campaign):
        self._stream = stream
        self._campaign = campaign
        self._buf = ""

    def write(self, data):
        res = self._stream.write(data)
        self._buf += data
        while "\n" in self._buf:
            line, self._buf = self._buf.split("\n", 1)
            self._campaign.observe_line(line)
        return res

    def flush(self):
        return self._stream.flush()

    def __getattr__(self, name):
        return getattr(self._stream, name)


class _FICampaign:
    def __init__(self, pc_count_dict, max_skips_per_loop, num_skips=0):
        self.pc_count_dict = pc_count_dict
        self.max_skips_per_loop = max_skips_per_loop
        self.num_skips = num_skips
        self.plan = []
        if num_skips and num_skips > 0:
            all_pcs = list(pc_count_dict.keys())
            random.shuffle(all_pcs)
            for pc in all_pcs:
                max_occ = min(max(max_skips_per_loop, 3), pc_count_dict[pc])
                self.plan.append((pc, [random.randrange(max_occ)]))
        else:
            for pc, count in pc_count_dict.items():
                self.plan.append((pc, list(range(min(max_skips_per_loop, count)))))

        self.current_point = None
        self._current_hit = False
        self._partial_hits = 0
        self.attempts = 0
        self.executed_points = []
        self.results = {}
        self.outcomes = {}
        self.orig_stdout = sys.stdout
        sys.stdout = _StdoutSpy(sys.stdout, self)

    def mark_hit(self):
        if self.current_point is not None and not self._current_hit:
            self._current_hit = True
            pc_int, occ = self.current_point
            self.executed_points.append((pc_int, occ))
            self.results.setdefault(pc_int, {})[occ] = False
            self.outcomes.setdefault((pc_int, occ), "No fault")

    def record_partial(self, hits):
        if hits and hits > 0:
            self._partial_hits = hits

    def items(self):
        for pc, occs in self.plan:
            if (self.num_skips and self.num_skips > 0 and
                    len(self.executed_points) >= self.num_skips):
                break
            yield pc, self._iter_occs(pc, occs)

    def _iter_occs(self, pc, occs):
        pc_int = int(pc, 16)
        for occ in occs:
            if (self.num_skips and self.num_skips > 0 and
                    len(self.executed_points) >= self.num_skips):
                break
            self.attempts += 1
            self.current_point = (pc_int, occ)
            self._current_hit = False
            self._partial_hits = 0
            if not (self.num_skips and self.num_skips > 0):
                self.mark_hit()
            yield occ
            if (
                self.num_skips and
                self.num_skips > 0 and
                not self._current_hit and
                self._partial_hits > 0
            ):
                self.pc_count_dict[pc] = self._partial_hits
                max_fb = min(max(self.max_skips_per_loop, 3), self._partial_hits)
                fallback_occ = random.randrange(max_fb)
                self.attempts += 1
                self.current_point = (pc_int, fallback_occ)
                self._current_hit = False
                self._partial_hits = 0
                yield fallback_occ

    def observe_line(self, line):
        if self.current_point is None or not self._current_hit:
            return
        pc_int, occ = self.current_point
        if "Successful FI attack!" in line:
            self.results.setdefault(pc_int, {})[occ] = True
            self.outcomes[(pc_int, occ)] = "Successful corruption (FI attack)"
        elif self.outcomes.get((pc_int, occ)) != "Successful corruption (FI attack)":
            if "Crash detected" in line:
                self.outcomes[(pc_int, occ)] = "Caught (crash)"
            elif "Target did not respond" in line:
                self.outcomes[(pc_int, occ)] = "Caught (timeout)"


_active_campaign = None


def mark_skip_hit():
    if _active_campaign is not None:
        _active_campaign.mark_hit()


def record_partial_hits(hits):
    if _active_campaign is not None:
        _active_campaign.record_partial(hits)


def select_fi_skips(pc_count_dict, max_skips_per_loop, num_skips=0):
    """Selects (PC, occurrence) pairs for an FI campaign (exhaustive or Monte-Carlo)."""
    global _active_campaign
    _active_campaign = _FICampaign(pc_count_dict, max_skips_per_loop, num_skips)
    return _active_campaign


def finish_fi_campaign(dis_parser, successful_faults, args, elf_path=None):
    """Prints Panopticon FI campaign summary and optionally dumps fi_results.json."""
    global _active_campaign
    campaign = _active_campaign
    _active_campaign = None
    if campaign is None:
        return
    if isinstance(sys.stdout, _StdoutSpy):
        sys.stdout = campaign.orig_stdout

    if elf_path is None and dis_parser is not None:
        elf_path = re.sub(r"\.dis$", ".elf", dis_parser.dis_file_path)

    elf_sha256 = ""
    elf_bin_name = "unknown"
    if elf_path and os.path.exists(elf_path):
        with open(elf_path, "rb") as ef:
            elf_sha256 = hashlib.sha256(ef.read()).hexdigest()
        elf_bin_name = os.path.splitext(os.path.basename(elf_path))[0]

    insns = dis_parser.parse_all_instructions() if dis_parser else {}
    pc_counts = {int(pc, 16): count for pc, count in campaign.pc_count_dict.items()}
    touched_funcs = {
        insns[pc]["func"]
        for pc in pc_counts
        if pc in insns and insns[pc].get("func")
    }
    dwarf_map = {}
    for pc, info in insns.items():
        if (
            pc in pc_counts or
            info.get("func") in touched_funcs
        ) and info.get("filepath"):
            dwarf_map[pc] = (info["filepath"], info["lineno"])

    print(f"ELF Binary: {elf_bin_name}")
    print(f"ELF SHA256: {elf_sha256}")
    if getattr(args, "dump_json", False):
        print("Extracting DWARF info from ELF")
        for pc in sorted(dwarf_map.keys()):
            filepath, lineno = dwarf_map[pc]
            fname = os.path.basename(filepath)
            disasm = insns[pc]["text"] if pc in insns else ""
            print(f"DWARF | 0x{pc:08x} | {fname}:{lineno} | {disasm}")

    baseline_insn_count = sum(pc_counts.values())
    total_attack_points = sum(
        min(campaign.max_skips_per_loop, c) for c in pc_counts.values()
    )
    total_attacks = len(campaign.executed_points)
    print(f"Baseline instruction count: {baseline_insn_count}")
    print(f"Total attack points: {total_attack_points}")
    print(f"--- Starting fault simulation ({total_attacks} attacks) ---")

    for idx, (pc, occ) in enumerate(campaign.executed_points, 1):
        dwarf_str = "unknown_src"
        if pc in dwarf_map:
            filepath, lineno = dwarf_map[pc]
            dwarf_str = f"{os.path.basename(filepath)}:{lineno}"
        outcome = campaign.outcomes.get((pc, occ), "No fault")
        print(
            f"[{idx:4}/{total_attacks}] "
            f"PC {hex(pc):<10} [{dwarf_str:<30}] (occ {occ}): {outcome}"
        )

    print(
        f"Campaign Complete. Successful Attacks: {successful_faults}",
        flush=True,
    )

    if getattr(args, "dump_json", False):
        out_dir = os.environ.get("TEST_UNDECLARED_OUTPUTS_DIR", ".")
        with open(os.path.join(out_dir, "fi_results.json"), "w") as f:
            json.dump(
                {
                    "target": os.environ.get("TEST_TARGET", ""),
                    "elf": elf_path or "",
                    "elf_sha256": elf_sha256,
                    "dwarf_map": dwarf_map,
                    "pc_counts": pc_counts,
                    "results": campaign.results,
                },
                f,
            )
