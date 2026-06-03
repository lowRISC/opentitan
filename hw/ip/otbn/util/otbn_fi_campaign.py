# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import concurrent.futures
import multiprocessing
import argparse
import sys
import tempfile
import os
import json
import random
from collections import Counter
from elftools.elf.elffile import ELFFile

from sim.standalonesim import StandaloneSim
from sim.load_elf import load_elf
from sim.state import FsmState
from typing import Any, Dict, Iterable, List, Optional, TextIO, Tuple


class FISim(StandaloneSim):
    def __init__(
        self, fi_skip_pc: Optional[int] = None, fi_skip_occurrence: int = 0
    ) -> None:
        super().__init__()
        self.fi_skip_pc = fi_skip_pc
        self.fi_skip_occurrence = fi_skip_occurrence
        self.pc_hit_counts: Dict[int, int] = {}

    def run(
        self,
        verbose: bool,
        dump_file: Optional[TextIO] = None,
        trace_file: Optional[TextIO] = None,
        max_insns: Optional[int] = None,
    ) -> int:
        insn_count = 0
        self.state.complete_init_sec_wipe()
        while True:
            if max_insns is not None and insn_count >= max_insns:
                raise TimeoutError("Maximum instruction limit reached")
            if self.state.ext_regs.read("RND_REQ", True):
                self.state.wsrs.RND.set_unsigned(random.getrandbits(256), False, False)
            if not self.state.wsrs.URND.running:
                seed = [random.getrandbits(64) for _ in range(4)]
                self.state.wsrs.URND.set_seed(seed)

            current_pc = self.state.pc

            if trace_file is not None:
                trace_file.write(f"0x{current_pc:08x}\n")

            if current_pc == self.fi_skip_pc:
                hits = self.pc_hit_counts.get(current_pc, 0)
                if hits == self.fi_skip_occurrence:
                    target_insn = self.program[current_pc // 4]
                    orig_execute = target_insn.execute

                    def nop_execute(*args: Any, **kwargs: Any) -> None:
                        pass

                    setattr(target_insn, "execute", nop_execute)
                    self.step(verbose)
                    setattr(target_insn, "execute", orig_execute)

                    self.pc_hit_counts[current_pc] = hits + 1
                    insn_count += 1
                    continue

                self.pc_hit_counts[current_pc] = hits + 1

            self.step(verbose)
            insn_count += 1

            if self.state.get_fsm_state() in [FsmState.IDLE, FsmState.LOCKED]:
                if dump_file is not None:
                    self.dump_regs(dump_file)
                break

        return insn_count


def parse_dmem_bytes(
    dmem_data: bytes, offsets: Dict[str, int], sizes: Dict[str, int]
) -> Dict[str, int]:
    results = {}
    for sym, addr in offsets.items():
        size = sizes[sym]
        num_words = size // 4
        val_bytes = bytearray()
        for i in range(num_words):
            word_idx = (addr // 4) + i
            off_5 = word_idx * 5
            word_data = dmem_data[off_5 + 1: off_5 + 5]
            val_bytes.extend(word_data)
        results[sym] = int.from_bytes(val_bytes, byteorder="little")
    return results


# We go at most twice in a loop in order to shorten the test
MAX_PC_DEPTH = 2


def get_symbol_offsets(
    elf_path: str, target_symbols: Iterable[str]
) -> Dict[str, int]:
    """Finds the byte offsets of the target variables in DMEM."""
    offsets = {}
    with open(elf_path, "rb") as f:
        elffile = ELFFile(f)
        symtab = elffile.get_section_by_name(".symtab")
        for sym in symtab.iter_symbols():
            if sym.name in target_symbols:
                offsets[sym.name] = sym["st_value"]
    return offsets


def parse_dmem(
    dmem_dump_path: str, offsets: Dict[str, int], sizes: Dict[str, int]
) -> Dict[str, int]:
    """Reads specific variables from the raw DMEM dump."""
    results = {}

    with open(dmem_dump_path, "rb") as f:
        dmem_data = f.read()

    for sym, addr in offsets.items():
        size = sizes[sym]
        num_words = size // 4

        val_bytes = bytearray()

        # Read the memory word-by-word
        for i in range(num_words):
            word_idx = (addr // 4) + i
            off_5 = word_idx * 5

            # Format: [ECC Byte] [Data0] [Data1] [Data2] [Data3]
            # We skip index 0, and grab indices 1, 2, 3, and 4.
            word_data = dmem_data[off_5 + 1: off_5 + 5]
            val_bytes.extend(word_data)

        # Convert the reassembled raw bytes to a Little-Endian integer
        results[sym] = int.from_bytes(val_bytes, byteorder="little")

    return results


def run_test_and_get_dmem(
    elf_path: str,
    offsets: Dict[str, int],
    sizes: Dict[str, int],
    dmem_json: Optional[str] = None,
    trace_file: Optional[str] = None,
    skip_pc: Optional[int] = None,
    skip_occurrence: int = 0,
    max_insns: Optional[int] = None,
) -> Dict[str, Any]:
    """Runs the simulator and returns the parsed DMEM values."""
    sim = FISim(fi_skip_pc=skip_pc, fi_skip_occurrence=skip_occurrence)
    exp_end_addr = load_elf(sim, elf_path)

    key0 = int((str("deadbeef") * 12), 16)
    key1 = int((str("baadf00d") * 12), 16)
    sim.state.wsrs.set_sideload_keys(key0, key1)

    if dmem_json:
        with open(dmem_json, "r") as f:
            dmem_batch_data = json.load(f)
        if dmem_batch_data:
            parsed_dmem = {k: bytes.fromhex(v) for k, v in dmem_batch_data[0].items()}
            sim.load_dmem_vars(parsed_dmem)

    sim.state.ext_regs.commit()
    sim.start(collect_stats=False)

    trace_f = None
    if trace_file:
        trace_f = open(trace_file, "w")

    try:
        insn_count = sim.run(verbose=False, trace_file=trace_f, max_insns=max_insns)
    except TimeoutError:
        return {"status": "TIMEOUT"}
    except Exception:
        import traceback
        traceback.print_exc()
        return {"status": "ERROR"}
    finally:
        if trace_f:
            trace_f.close()

    if exp_end_addr is not None and sim.state.pc != exp_end_addr:
        return {"status": "ERROR"}

    dmem_data = sim.dump_data()
    regs = parse_dmem_bytes(dmem_data, offsets, sizes)
    return {"status": "SUCCESS", "regs": regs, "insn_count": insn_count}


def attack_worker(
    task: Tuple[
        int,
        int,
        str,
        str,
        bool,
        Dict[str, int],
        Dict[str, int],
        str,
        str,
        int,
    ]
) -> Tuple[
    int, int, Optional[Dict[str, Any]], Optional[Dict[str, Any]]
]:
    random.seed()
    (
        pc,
        occ,
        elf_path,
        attack_mode,
        fixed_instruction_count,
        offsets,
        sizes,
        dmem_a_path,
        dmem_b_path,
        baseline_insn_count,
    ) = task
    res_a = None
    res_b = None

    max_insns = baseline_insn_count * 2 if baseline_insn_count else None

    if attack_mode in ["collision", "corruption"]:
        res_a = run_test_and_get_dmem(
            elf_path=elf_path,
            offsets=offsets,
            sizes=sizes,
            dmem_json=dmem_a_path,
            skip_pc=pc,
            skip_occurrence=occ,
            max_insns=max_insns,
        )

        if res_a["status"] != "SUCCESS" and attack_mode == "collision":
            return pc, occ, res_a, None

    if attack_mode in ["collision", "bypass"]:
        res_b = run_test_and_get_dmem(
            elf_path=elf_path,
            offsets=offsets,
            sizes=sizes,
            dmem_json=dmem_b_path,
            skip_pc=pc,
            skip_occurrence=occ,
            max_insns=max_insns,
        )

    return pc, occ, res_a, res_b


def build_pc_to_line_map(elf_path: str) -> Dict[int, Tuple[str, int]]:
    """Extracts DWARF line info to map PCs to source code lines."""
    pc_map = {}
    with open(elf_path, "rb") as f:
        elffile = ELFFile(f)
        if not elffile.has_dwarf_info():
            return pc_map
        dwarfinfo = elffile.get_dwarf_info()
        for cu in dwarfinfo.iter_CUs():
            line_program = dwarfinfo.line_program_for_CU(cu)
            if line_program is None:
                continue
            for entry in line_program.get_entries():
                if entry.state is None or entry.state.file == 0:
                    continue
                file_entry = line_program["file_entry"][entry.state.file - 1]
                pc_map[entry.state.address] = (
                    file_entry.name.decode("utf-8"),
                    entry.state.line,
                )
    return pc_map


def parse_trace_for_pcs(trace_file: str) -> List[int]:
    pc_list = []
    with open(trace_file, "r") as f:
        for line in f:
            if line.strip().startswith("0x"):
                try:
                    pc_str = line.strip().split()[0]
                    pc_str = pc_str.replace(":", "")
                    pc_list.append(int(pc_str, 16))
                except ValueError:
                    pass
    return pc_list


def annotate_trace_file(
    trace_path: str, dwarf_map: Dict[int, Tuple[str, int]]
) -> None:
    """Rewrites the trace file to include DWARF source code mapping."""
    with open(trace_path, "r") as f:
        lines = f.readlines()

    with open(trace_path, "w") as f:
        for line in lines:
            if line.strip().startswith("0x"):
                try:
                    # Extract just the PC hex string
                    pc_str = line.strip().split(":")[0].split()[0]
                    pc = int(pc_str, 16)

                    # If we have DWARF info, append it as a comment
                    if pc in dwarf_map:
                        filepath, lineno = dwarf_map[pc]
                        filename = os.path.basename(filepath)
                        line = line.rstrip() + f"    // [{filename}:{lineno}]\n"
                except Exception:
                    pass
            f.write(line)


def generate_boolean_shares(
    secret: int, share_size: int, modulus: Optional[int] = None
) -> Tuple[int, int]:
    r = random.getrandbits(share_size * 8)
    return secret ^ r, r


def generate_additive_shares(
    secret: int, share_size: int, modulus: Optional[int] = None
) -> Tuple[int, int]:
    if modulus is None:
        raise ValueError("Modulus required for additive sharing")
    r = random.randrange(0, modulus)
    return (secret - r) % modulus, r


def generate_scalar_blind_shares(
    secret: int, share_size: int, modulus: Optional[int] = None
) -> Tuple[int, int]:
    if modulus is None:
        raise ValueError("Modulus required for scalar blinding")
    blind_bits = (share_size * 8) - modulus.bit_length()
    if blind_bits <= 0:
        raise ValueError("Error in blinding bits size")
    r0 = random.getrandbits(blind_bits)
    r1 = random.getrandbits(blind_bits)
    return secret + (r0 * modulus), r1 * modulus


SHARE_GENERATORS = {
    "boolean": generate_boolean_shares,
    "additive": generate_additive_shares,
    "scalar_blind": generate_scalar_blind_shares,
}


def generate_shares(
    mode: str, secret: int, share_size: int, modulus: Optional[int] = None
) -> Tuple[int, int]:
    local_generators = {
        "boolean": generate_boolean_shares,
        "additive": generate_additive_shares,
        "scalar_blind": generate_scalar_blind_shares,
    }

    generator = None
    for k, v in local_generators.items():
        if k == mode:
            generator = v
            break
    if generator is None:
        raise ValueError(f"Unknown mode: {mode}")
    return generator(secret, share_size, modulus)


def create_dmem_override(
    secrets_cfg: List[Dict[str, Any]], out_path: str
) -> None:
    trace_dict = {}
    for sec in secrets_cfg:
        if sec["mode"] == "unmasked" or len(sec["symbols"]) == 1:
            trace_dict[sec["symbols"][0]] = (
                sec["secret"].to_bytes(sec["size"], "little").hex()
            )
        else:
            share0, share1 = generate_shares(
                sec["mode"], sec["secret"], sec["size"], sec["modulus"]
            )
            trace_dict[sec["symbols"][0]] = share0.to_bytes(sec["size"], "little").hex()
            trace_dict[sec["symbols"][1]] = share1.to_bytes(sec["size"], "little").hex()

    with open(out_path, "w") as f:
        json.dump([trace_dict], f)


def unmask_value(
    regs: Dict[str, int],
    col_sym: str,
    mode: str,
    size: int,
    modulus_str: Optional[str] = None,
) -> int:
    syms = col_sym.split(",")
    modulus = int(modulus_str, 16) if modulus_str else None

    if mode == "unmasked":
        assert len(syms) == 1
        return regs[syms[0]]

    if mode == "boolean":
        if len(syms) == 1:
            val = regs[syms[0]]
            share_size_bits = (size * 8) // 2
            mask = (1 << share_size_bits) - 1
            share0 = val & mask
            share1 = val >> share_size_bits
            return share0 ^ share1
        elif len(syms) == 2:
            return regs[syms[0]] ^ regs[syms[1]]
        else:
            raise ValueError("Boolean unmasking supports 1 or 2 symbols")

    if mode == "additive":
        if modulus is None:
            raise ValueError("Modulus required for additive unmasking")
        if len(syms) == 1:
            val = regs[syms[0]]
            share_size_bits = (size * 8) // 2
            share0 = val & ((1 << share_size_bits) - 1)
            share1 = val >> share_size_bits
            return (share0 + share1) % modulus
        elif len(syms) == 2:
            return (regs[syms[0]] + regs[syms[1]]) % modulus
        else:
            raise ValueError("Additive unmasking supports 1 or 2 symbols")

    raise ValueError(f"Unknown mode: {mode}")


def main() -> int:
    parser = argparse.ArgumentParser(description="OTBN FI Campaign")
    parser.add_argument("simulator")
    parser.add_argument("--elf", required=True)
    parser.add_argument(
        "--attack-mode",
        choices=["collision", "corruption", "bypass"],
        default="collision",
    )
    parser.add_argument("--ok-sym", required=True, help="Symbol name for OK flag")
    parser.add_argument(
        "--ok-size", type=int, required=True, help="Size in bytes of OK flag"
    )
    parser.add_argument(
        "--ok-val", required=True, help="Expected OK value (e.g. 0x739)"
    )
    parser.add_argument("--col-sym", required=True, help="Symbol for collision check")
    parser.add_argument(
        "--col-size", type=int, required=True, help="Size in bytes of collision target"
    )
    parser.add_argument(
        "--col-threshold",
        type=float,
        default=1.0,
        help="Partial collision threshold (e.g., 0.75 for 75%)",
    )
    parser.add_argument(
        "--col-mode",
        choices=["unmasked", "boolean", "additive"],
        default="unmasked",
        help="Masking mode for collision target",
    )
    parser.add_argument(
        "--col-modulus",
        help="Modulus for additive unmasking (hex string)",
    )
    parser.add_argument(
        "--fixed-instruction-count",
        action="store_true",
        help="Enforce strict cycle/instruction counting",
    )
    parser.add_argument(
        "--target-a-secret",
        action="append",
        default=[],
        help="Format: sym[s]:mode:size:hex[:mod]",
    )
    parser.add_argument(
        "--target-b-secret",
        action="append",
        default=[],
        help="Format: sym[s]:mode:size:hex[:mod]",
    )
    args = parser.parse_args()

    def parse_secret_args(arg_list: List[str]) -> List[Dict[str, Any]]:
        secrets = []
        for item in arg_list:
            parts = item.split(":")
            modulus = int(parts[4], 16) if len(parts) > 4 and parts[4] else None
            secrets.append(
                {
                    "symbols": parts[0].split(","),
                    "mode": parts[1],
                    "size": int(parts[2]),
                    "secret": int(parts[3], 16),
                    "modulus": modulus,
                }
            )
        return secrets

    target_a_secrets = parse_secret_args(args.target_a_secret)
    target_b_secrets = parse_secret_args(args.target_b_secret)

    ok_val_int = int(args.ok_val, 16)
    sizes = {args.ok_sym: args.ok_size}
    col_syms = args.col_sym.split(",")
    for sym in col_syms:
        sizes[sym] = args.col_size

    col_mode = args.col_mode
    if len(col_syms) == 1 and col_mode in ["boolean", "additive"]:
        unmasked_size = args.col_size // 2
    else:
        unmasked_size = args.col_size

    offsets = get_symbol_offsets(args.elf, sizes.keys())

    print("Extracting DWARF info from ELF")
    dwarf_map = build_pc_to_line_map(args.elf)

    shm_dir = "/dev/shm" if os.path.exists("/dev/shm") else None
    dmem_a_fd, dmem_a_path = tempfile.mkstemp(dir=shm_dir, suffix=".json")
    os.close(dmem_a_fd)
    dmem_b_fd, dmem_b_path = tempfile.mkstemp(dir=shm_dir, suffix=".json")
    os.close(dmem_b_fd)

    create_dmem_override(target_a_secrets, dmem_a_path)
    create_dmem_override(target_b_secrets, dmem_b_path)

    try:
        baseline_collision_val = None

        print("--- Generating Baseline (Target A) ---")
        trace_file_a = "golden_trace_a.log"
        absolute_trace_path = os.path.abspath(trace_file_a)
        print(f"Trace file path: {absolute_trace_path}")

        res_a = run_test_and_get_dmem(
            args.elf,
            offsets,
            sizes,
            dmem_json=dmem_a_path,
            trace_file=trace_file_a,
        )
        if args.attack_mode in ["collision", "corruption"]:
            if res_a["status"] != "SUCCESS" or res_a["regs"][args.ok_sym] != ok_val_int:
                print(
                    "ERROR: Target A did not return the expected OK value on a normal run."
                )
                return 1

        annotate_trace_file(trace_file_a, dwarf_map)
        baseline_collision_val = 0
        if res_a["status"] == "SUCCESS":
            baseline_collision_val = unmask_value(
                res_a["regs"],
                args.col_sym,
                args.col_mode,
                args.col_size,
                args.col_modulus,
            )
        baseline_insn_count = len(parse_trace_for_pcs(trace_file_a))

        print(
            f"Baseline collision target ({args.col_sym}): {hex(baseline_collision_val)}"
        )
        print(f"Baseline instruction count: {baseline_insn_count}")

        if args.attack_mode in ["collision", "bypass"]:
            print("--- Generating Trace (Target B) ---")
            trace_file = "golden_trace_b.log"
            absolute_trace_path = os.path.abspath(trace_file)
            print(f"Trace file path: {absolute_trace_path}")

            res_b = run_test_and_get_dmem(
                args.elf,
                offsets,
                sizes,
                dmem_json=dmem_b_path,
                trace_file=trace_file,
            )

            if args.attack_mode == "collision":
                if (
                    res_b["status"] != "SUCCESS" or
                    res_b["regs"][args.ok_sym] != ok_val_int
                ):
                    print(
                        "ERROR: Target B did not return the expected OK value on a normal run."
                    )
                    return 1
            elif args.attack_mode == "bypass":
                if (
                    res_b["status"] == "SUCCESS" and
                    res_b["regs"][args.ok_sym] == ok_val_int
                ):
                    print("ERROR: In bypass mode, target B must fail. It returned ok.")
                    return 1

            annotate_trace_file(trace_file, dwarf_map)

        pc_counts = Counter(parse_trace_for_pcs(trace_file_a))
        attack_queue = [
            (
                pc,
                occ,
                args.elf,
                args.attack_mode,
                args.fixed_instruction_count,
                offsets,
                sizes,
                dmem_a_path,
                dmem_b_path,
                baseline_insn_count,
            )
            for pc, total in pc_counts.items()
            for occ in range(min(MAX_PC_DEPTH, total))
        ]
        total_attacks = len(attack_queue)
        completed_attacks = 0
        successful_attacks = 0

        max_workers = max(1, multiprocessing.cpu_count() - 2)
        print(
            f"--- Starting fault simulation ({total_attacks} attacks, {max_workers} processes) ---"
        )

        with concurrent.futures.ProcessPoolExecutor(
            max_workers=max_workers
        ) as executor:
            future_to_task = {
                executor.submit(attack_worker, task): task for task in attack_queue
            }

            for future in concurrent.futures.as_completed(future_to_task):
                completed_attacks += 1
                try:
                    pc, occ, fault_res_a, fault_res_b = future.result()
                except Exception as e:
                    print(f"Thread crashed unexpectedly: {e}", flush=True)
                    continue

                dwarf_str = "unknown_src"
                if pc in dwarf_map:
                    filepath, lineno = dwarf_map[pc]
                    filename = os.path.basename(filepath)
                    dwarf_str = f"{filename}:{lineno}"

                progress = (
                    f"[{completed_attacks:4}/{total_attacks}] "
                    f"PC {hex(pc):<6} [{dwarf_str:<30}] (occ {occ}):"
                )

                if args.attack_mode == "collision":
                    if fault_res_a["status"] == "TIMEOUT" or (
                        fault_res_b and fault_res_b["status"] == "TIMEOUT"
                    ):
                        print(f"{progress} Caught (timeout)", flush=True)
                        continue

                    if fault_res_a["status"] != "SUCCESS" or (
                        fault_res_b and fault_res_b["status"] != "SUCCESS"
                    ):
                        print(f"{progress} Caught (crash)", flush=True)
                        continue

                    regs_a = fault_res_a["regs"]
                    regs_b = fault_res_b["regs"]

                    if args.fixed_instruction_count:
                        if fault_res_a["insn_count"] not in [
                            baseline_insn_count,
                            baseline_insn_count - 1,
                        ] or fault_res_b["insn_count"] not in [
                            baseline_insn_count,
                            baseline_insn_count - 1,
                        ]:
                            print(
                                f"{progress} Caught (instr. count mismatch)", flush=True
                            )
                            continue

                    if (
                        regs_a[args.ok_sym] == ok_val_int and
                        regs_b[args.ok_sym] == ok_val_int
                    ):
                        val_a = unmask_value(
                            regs_a,
                            args.col_sym,
                            args.col_mode,
                            args.col_size,
                            args.col_modulus,
                        )
                        val_b = unmask_value(
                            regs_b,
                            args.col_sym,
                            args.col_mode,
                            args.col_size,
                            args.col_modulus,
                        )

                        total_bits = unmasked_size * 8
                        xor_val = val_a ^ val_b
                        mismatched_bits = bin(xor_val).count("1")
                        matched_bits = total_bits - mismatched_bits
                        match_ratio = matched_bits / total_bits

                        if match_ratio >= args.col_threshold:
                            print(
                                f"\n{progress} Collision found ({match_ratio * 100:.1f}% match)\n"
                                f"    val_a: {hex(val_a)}\n"
                                f"    val_b: {hex(val_b)}\n",
                                flush=True,
                            )
                            successful_attacks += 1
                        else:
                            print(
                                f"{progress} No collision ({match_ratio * 100:.1f}% match)",
                                flush=True,
                            )
                    else:
                        print(f"{progress} Not ok status", flush=True)

                elif args.attack_mode == "corruption":
                    if fault_res_a["status"] == "TIMEOUT":
                        print(f"{progress} Caught (timeout)", flush=True)
                        continue
                    if fault_res_a["status"] != "SUCCESS":
                        print(f"{progress} Caught (crash)", flush=True)
                        continue

                    regs_a = fault_res_a["regs"]
                    if args.fixed_instruction_count:
                        if fault_res_a["insn_count"] not in [
                            baseline_insn_count,
                            baseline_insn_count - 1,
                        ]:
                            print(
                                f"{progress} Caught (instr. count mismatch)", flush=True
                            )
                            continue

                    if regs_a[args.ok_sym] == ok_val_int:
                        val_a = unmask_value(
                            regs_a,
                            args.col_sym,
                            args.col_mode,
                            args.col_size,
                            args.col_modulus,
                        )
                        total_bits = unmasked_size * 8
                        xor_val = val_a ^ baseline_collision_val
                        match_ratio = (
                            total_bits - bin(xor_val).count("1")
                        ) / total_bits

                        if match_ratio < args.col_threshold:
                            print(
                                f"\n{progress} Successful corruption \n"
                                f"    golden:  {hex(baseline_collision_val)}\n"
                                f"    faulted: {hex(val_a)}\n",
                                flush=True,
                            )
                            successful_attacks += 1
                        else:
                            print(f"{progress} No corruption", flush=True)
                    else:
                        print(f"{progress} Not ok status", flush=True)

                elif args.attack_mode == "bypass":
                    if fault_res_b["status"] == "TIMEOUT":
                        print(f"{progress} Caught (timeout)", flush=True)
                        continue
                    if fault_res_b["status"] != "SUCCESS":
                        print(f"{progress} Caught (crash)", flush=True)
                        continue

                    regs_b = fault_res_b["regs"]
                    if args.fixed_instruction_count:
                        if fault_res_b["insn_count"] not in [
                            baseline_insn_count,
                            baseline_insn_count - 1,
                        ]:
                            print(
                                f"{progress} Caught (instr. count mismatch)", flush=True
                            )
                            continue

                    if regs_b[args.ok_sym] == ok_val_int:
                        print(
                            f"\n{progress} Successful bypass\n",
                            flush=True,
                        )
                        successful_attacks += 1
                    else:
                        print(f"{progress} No bypass", flush=True)

        print(
            f"Campaign Complete. Successful Attacks: {successful_attacks}", flush=True
        )
        return 0 if successful_attacks == 0 else 1

    finally:
        if os.path.exists(dmem_a_path):
            os.remove(dmem_a_path)
        if os.path.exists(dmem_b_path):
            os.remove(dmem_b_path)


if __name__ == "__main__":
    sys.exit(main())
