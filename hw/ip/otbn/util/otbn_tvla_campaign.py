# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys
import os
import random
import math
import tempfile
import concurrent.futures
import multiprocessing
from collections import defaultdict, Counter
from elftools.elf.elffile import ELFFile

from sim.standalonesim import StandaloneSim
from sim.load_elf import load_elf
from sim.state import FsmState
from sim.isa import OTBNInsn
from sim.trace import Trace
from typing import Any, Dict, List, Optional, TextIO, Tuple


# Precompute butterfly masks and byte offsets for 128x256 bit-matrix transpose.
_TRANSPOSE_MASKS: List[Tuple[int, int]] = []
for _k in range(7):
    _shift = (1 << (_k + 8)) - (1 << _k)
    _m = sum(
        1 << _a
        for _a in range(32768)
        if not (_a & (1 << _k)) and (_a & (1 << (_k + 8)))
    )
    _TRANSPOSE_MASKS.append((_m >> _shift, _shift))

_TRANSPOSE_OFFSETS: List[int] = [
    (((i & 0x7F) << 1) | (i >> 7)) * 16 for i in range(256)
]


def transpose_128x256(vals: List[int]) -> List[int]:
    """Transposes up to 128 256-bit integers into 256 N-bit integer bit-slices."""
    x = int.from_bytes(b"".join(v.to_bytes(32, "little") for v in vals), "little")
    for m_shifted, shift in _TRANSPOSE_MASKS:
        d = ((x >> shift) ^ x) & m_shifted
        x ^= d | (d << shift)
    out = x.to_bytes(4096, "little")
    return [int.from_bytes(out[off: off + 16], "little") for off in _TRANSPOSE_OFFSETS]


class TVLASim(StandaloneSim):
    def __init__(self, trace_hw_file: Optional[TextIO] = None) -> None:
        super().__init__()
        self.trace_hw_file = trace_hw_file
        self.port_pairs: Dict[Tuple[int, int, str], Tuple[List[int], List[int]]] = (
            defaultdict(lambda: ([], []))
        )
        if self.trace_hw_file is not None:
            self._tvla_init()

    def _record_pair(self, pc: int, occ: int, tag: str, a: int, b: int) -> None:
        pair = self.port_pairs[(pc, occ, tag)]
        pair[0].append(a)
        pair[1].append(b)

    def _on_retire(self, verbose: bool, insn: OTBNInsn) -> List[Trace]:
        if self.trace_hw_file is not None:
            self._tvla_pending_wdrs = list(self.state.wdrs._pending_writes)
        return super()._on_retire(verbose, insn)

    def _on_stall(self, verbose: bool, fetch_next: bool) -> List[Trace]:
        if self.trace_hw_file is not None:
            self._tvla_pending_wdrs = list(self.state.wdrs._pending_writes)
        return super()._on_stall(verbose, fetch_next)

    def run_batch(
        self,
        verbose: bool,
        batch_size: int,
        dmem_batch_data: Optional[List[Dict[str, bytes]]] = None,
    ) -> int:
        insn_count = 0
        initial_pc = self.state.pc
        snapshot_dmem = self.state.dmem.dump_le_words()

        for trace_idx in range(batch_size):
            if trace_idx > 0:
                if self.trace_hw_file:
                    self.trace_hw_file.write("===\n")
                self.state.dmem.load_le_words(
                    snapshot_dmem, has_validity=True, word_offset=0
                )
                for i in range(32):
                    self.state.gprs.get_reg(i).write_unsigned(0)
                    self.state.wdrs.get_reg(i).write_unsigned(0)
                self.state.gprs.commit()
                self.state.wdrs.commit()
                self.state.wsrs.ACC.write_unsigned(0)
                self.state.csrs.flags[0].write_unsigned(0)
                self.state.csrs.flags[1].write_unsigned(0)
                self.state.pc = initial_pc

            self.state.wsrs.URND.on_start()
            for _ in range(6):
                self.state.wsrs.URND.set_seed(random.getrandbits(32))
                self.state.wsrs.URND.step()
                self.state.wsrs.URND.commit()
            self.state.wsrs.URND.reseed_done = True
            self.state.commit(sim_stalled=True)
            self._tvla_init()

            urnd_seed_count = 0
            self.state.wfi_enabled = True
            self.state.wfi_auto_resume = True

            if dmem_batch_data:
                sim_dmem_vars = dmem_batch_data[trace_idx]
                self.load_dmem_vars(sim_dmem_vars)

            self.state.ext_regs.commit()
            self.start(collect_stats=False)
            self.state.complete_init_sec_wipe()

            while True:
                if self.state.ext_regs.read("RND_REQ", True):
                    self.state.wsrs.RND.set_unsigned(
                        random.getrandbits(256), False, False
                    )
                if self.state.wsrs.URND.requesting:
                    self.state.wsrs.URND.set_seed(random.getrandbits(32))
                    urnd_seed_count = (urnd_seed_count + 1) % 6
                    if urnd_seed_count == 0:
                        self.state.wsrs.URND.reseed_done = True

                current_pc = self.state.pc

                tvla_hits = 0
                if self.trace_hw_file is not None:
                    tvla_hits = self._tvla_hits.get(current_pc, 0)
                    self._tvla_pre_step(current_pc)

                self.step(verbose)
                insn_count += 1

                if self.trace_hw_file is not None:
                    self._tvla_post_step(current_pc, self.trace_hw_file)
                    self._tvla_hits[current_pc] = tvla_hits + 1

                if self.state.get_fsm_state() in [FsmState.IDLE, FsmState.LOCKED]:
                    break

        return insn_count

    def _tvla_init(self) -> None:
        self._tvla_hits: Dict[int, int] = {}
        self._tvla_pending_wdrs: List[int] = []
        self._tvla_latches: Dict[str, int] = {
            "fg0": 0,
            "fg1": 0,
            "in_wide": 0,
            "in_gp": 0,
        }
        self._tvla_in_wide_a: Optional[int] = None
        self._tvla_in_wide_b: Optional[int] = None
        self._tvla_out_wide: Optional[int] = None

    def _tvla_pre_step(self, current_pc: int) -> None:
        self._tvla_wdrs_before = self.state.wdrs.peek_unsigned_values()
        self._tvla_gprs_before = self.state.gprs.peek_unsigned_values()
        self._tvla_acc_before = self.state.wsrs.ACC.read_unsigned()

        wrs1_idx, wrs2_idx = None, None
        grs1_idx, grs2_idx = None, None
        try:
            insn_obj = self.program[current_pc // 4]
            op_vals = insn_obj.op_vals
            mnemonic = insn_obj.insn.mnemonic
            if "wrs1" in op_vals:
                wrs1_idx = op_vals["wrs1"]
            elif "wrs" in op_vals:
                wrs1_idx = op_vals["wrs"]
            elif mnemonic == "bn.movr" and "grs" in op_vals:
                wrs1_idx = self._tvla_gprs_before[op_vals["grs"]] & 0x1F
            if "wrs2" in op_vals:
                wrs2_idx = op_vals["wrs2"]

            gpr_sources = []
            if "grs1" in op_vals:
                gpr_sources.append(op_vals["grs1"])
            elif "grs" in op_vals:
                gpr_sources.append(op_vals["grs"])
            if "grs2" in op_vals:
                gpr_sources.append(op_vals["grs2"])
            if "grd" in op_vals and mnemonic in ("bn.lid", "bn.movr"):
                gpr_sources.append(op_vals["grd"])

            if len(gpr_sources) > 0:
                grs1_idx = gpr_sources[0]
            if len(gpr_sources) > 1:
                grs2_idx = gpr_sources[1]
        except Exception:
            pass

        self._tvla_in_hw, self._tvla_in_hd = 0, 0
        self._tvla_curr_wrs = (wrs1_idx, wrs2_idx)

        occ = self._tvla_hits.get(current_pc, 0)
        if wrs1_idx is not None or wrs2_idx is not None:
            val1 = self._tvla_wdrs_before[wrs1_idx] if wrs1_idx is not None else 0
            val2 = self._tvla_wdrs_before[wrs2_idx] if wrs2_idx is not None else 0
            val = (val1 << 256) | val2
            self._tvla_in_hw = bin(val).count("1")
            self._tvla_in_hd = bin(self._tvla_latches["in_wide"] ^ val).count("1")
            self._tvla_latches["in_wide"] = val
            if wrs1_idx is not None and wrs2_idx is not None:
                self._record_pair(current_pc, occ, "XBit", val1, val2)
            if wrs1_idx is not None and self._tvla_in_wide_a is not None:
                self._record_pair(
                    current_pc, occ, "XBit-InA", self._tvla_in_wide_a, val1
                )
            if wrs2_idx is not None and self._tvla_in_wide_b is not None:
                self._record_pair(
                    current_pc, occ, "XBit-InB", self._tvla_in_wide_b, val2
                )
            if wrs1_idx is not None:
                self._tvla_in_wide_a = val1
            if wrs2_idx is not None:
                self._tvla_in_wide_b = val2
        elif grs1_idx is not None or grs2_idx is not None:
            val1 = self._tvla_gprs_before[grs1_idx] if grs1_idx is not None else 0
            val2 = self._tvla_gprs_before[grs2_idx] if grs2_idx is not None else 0
            val = (val1 << 32) | val2
            self._tvla_in_hw = bin(val).count("1")
            self._tvla_in_hd = bin(self._tvla_latches["in_gp"] ^ val).count("1")
            self._tvla_latches["in_gp"] = val
            if grs1_idx is not None and grs2_idx is not None:
                self._record_pair(current_pc, occ, "XBit", val1, val2)

    def _tvla_post_step(self, current_pc: int, trace_hw_file: TextIO) -> None:
        wdrs_after = self.state.wdrs.peek_unsigned_values()
        acc_after = self.state.wsrs.ACC.read_unsigned()
        fg0_after = self.state.csrs.flags[0].read_unsigned()
        fg1_after = self.state.csrs.flags[1].read_unsigned()
        occ = self._tvla_hits.get(current_pc, 0)

        curr_alu_out = None
        out_hd = 0
        if self._tvla_pending_wdrs:
            idx = sorted(self._tvla_pending_wdrs)[0]
            curr_alu_out = wdrs_after[idx]
            wdr_before = self._tvla_wdrs_before[idx]
            out_hd = bin(wdr_before ^ curr_alu_out).count("1")
            if idx not in self._tvla_curr_wrs:
                self._record_pair(
                    current_pc, occ, "XBit-Ovr", wdr_before, curr_alu_out
                )
            if self._tvla_out_wide is not None:
                self._record_pair(
                    current_pc, occ, "XBit-Out", self._tvla_out_wide, curr_alu_out
                )
            self._tvla_out_wide = curr_alu_out
        elif self._tvla_acc_before != acc_after:
            curr_alu_out = acc_after
            out_hd = bin(self._tvla_acc_before ^ acc_after).count("1")

        out_hw = bin(curr_alu_out).count("1") if curr_alu_out is not None else 0

        fg0_hw = bin(fg0_after).count("1")
        fg0_hd = bin(self._tvla_latches["fg0"] ^ fg0_after).count("1")
        fg1_hw = bin(fg1_after).count("1")
        fg1_hd = bin(self._tvla_latches["fg1"] ^ fg1_after).count("1")

        trace_hw_file.write(
            f"{current_pc:#x} {out_hw} {out_hd} {fg0_hw} {fg0_hd} "
            f"{fg1_hw} {fg1_hd} {self._tvla_in_hw} {self._tvla_in_hd}\n"
        )

        self._tvla_latches["fg0"] = fg0_after
        self._tvla_latches["fg1"] = fg1_after


NUM_MODELS = 8

MODEL_NAMES = {
    0: "Out HW",
    1: "Out HD",
    2: "fg0 HW",
    3: "fg0 HD",
    4: "fg1 HW",
    5: "fg1 HD",
    6: "In HW",
    7: "In HD",
}


class TVLAAccumulator:
    def __init__(self) -> None:
        self.counts = defaultdict(lambda: defaultdict(lambda: [0, 0]))
        self.sums = defaultdict(
            lambda: defaultdict(lambda: [[0.0] * NUM_MODELS, [0.0] * NUM_MODELS])
        )
        self.sum_sqs = defaultdict(
            lambda: defaultdict(lambda: [[0.0] * NUM_MODELS, [0.0] * NUM_MODELS])
        )
        self.port_tags = defaultdict(lambda: defaultdict(set))
        self.port_bit_counts = defaultdict(lambda: [0, 0])
        self.port_slices_a = defaultdict(lambda: [[0] * 256, [0] * 256])
        self.port_slices_b = defaultdict(lambda: [[0] * 256, [0] * 256])

    def add_trace_hws(
        self, pc: int, occ: int, set_idx: int, hws: List[int]
    ) -> None:
        self.counts[pc][occ][set_idx] += 1
        for i in range(NUM_MODELS):
            hw = hws[i]
            self.sums[pc][occ][set_idx][i] += hw
            self.sum_sqs[pc][occ][set_idx][i] += hw**2

    def add_port_slices(
        self,
        pc: int,
        occ: int,
        tag: str,
        set_idx: int,
        count: int,
        sa: List[int],
        sb: List[int],
    ) -> None:
        key = (pc, occ, tag)
        self.port_tags[pc][occ].add(tag)
        shift = self.port_bit_counts[key][set_idx]
        dst_a = self.port_slices_a[key][set_idx]
        dst_b = self.port_slices_b[key][set_idx]
        for i in range(256):
            if sa[i]:
                dst_a[i] |= sa[i] << shift
            if sb[i]:
                dst_b[i] |= sb[i] << shift
        self.port_bit_counts[key][set_idx] = shift + count

    def compute_t_test(self, pc: int, occ: int, model_idx: int) -> float:
        n0 = self.counts[pc][occ][0]
        n1 = self.counts[pc][occ][1]

        if n0 < 2 or n1 < 2:
            return 0.0

        sum0 = self.sums[pc][occ][0][model_idx]
        sum1 = self.sums[pc][occ][1][model_idx]
        sq0 = self.sum_sqs[pc][occ][0][model_idx]
        sq1 = self.sum_sqs[pc][occ][1][model_idx]

        mean0 = sum0 / n0
        mean1 = sum1 / n1

        var0 = (sq0 - (sum0**2) / n0) / (n0 - 1)
        var1 = (sq1 - (sum1**2) / n1) / (n1 - 1)

        if var0 == 0 and var1 == 0:
            return 0.0

        t_stat = (mean0 - mean1) / math.sqrt((var0 / n0) + (var1 / n1))
        return t_stat

    def compute_cross_bit_t_test(
        self, pc: int, occ: int, tag: str = "XBit"
    ) -> Tuple[float, int, int]:
        """Computes max 1st-order t-stat across all 256x256 (Port A, Port B) bit pairs."""
        key = (pc, occ, tag)
        if key not in self.port_bit_counts:
            return 0.0, -1, -1

        n0, n1 = self.port_bit_counts[key]
        if n0 < 2 or n1 < 2:
            return 0.0, -1, -1

        af, ar = self.port_slices_a[key]
        bf, br = self.port_slices_b[key]
        mask0, mask1 = (1 << n0) - 1, (1 << n1) - 1

        active_a = [
            i
            for i in range(256)
            if not ((af[i] == 0 and ar[i] == 0) or (af[i] == mask0 and ar[i] == mask1))
        ]
        active_b = [
            j
            for j in range(256)
            if not ((bf[j] == 0 and br[j] == 0) or (bf[j] == mask0 and br[j] == mask1))
        ]
        if not active_a or not active_b:
            return 0.0, -1, -1

        mean0 = [c / n0 for c in range(n0 + 1)]
        mean1 = [c / n1 for c in range(n1 + 1)]
        se0 = [((c - (c * c) / n0) / (n0 - 1)) / n0 for c in range(n0 + 1)]
        se1 = [((c - (c * c) / n1) / (n1 - 1)) / n1 for c in range(n1 + 1)]

        best_abs_t, best_t, best_i, best_j = 0.0, 0.0, -1, -1
        min_diff = int(0.5 * math.sqrt(n0)) if n0 == n1 else 0

        for i in active_a:
            afi, ari = af[i], ar[i]
            for j in active_b:
                cf = (afi ^ bf[j]).bit_count()
                cr = (ari ^ br[j]).bit_count()
                if -min_diff <= (cf - cr) <= min_diff:
                    continue
                denom = se0[cf] + se1[cr]
                if denom > 0.0:
                    t_val = (mean0[cf] - mean1[cr]) / math.sqrt(denom)
                    if abs(t_val) > best_abs_t:
                        best_abs_t, best_t, best_i, best_j = abs(t_val), t_val, i, j

        return best_t, best_i, best_j


def build_pc_to_line_map(elf_path: str) -> Dict[int, Tuple[str, int]]:
    """Extracts DWARF line info to map PCs to source code lines."""
    pc_map = {}
    try:
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
    except Exception as e:
        print(f"Failed to extract DWARF info: {e}")
    return pc_map


def annotate_trace_file(
    trace_path: str, dwarf_map: Dict[int, Tuple[str, int]]
) -> None:
    """Rewrites the trace file to include headers, aligned columns, and source mapping."""
    with open(trace_path, "r") as f:
        lines = f.readlines()

    header1 = (
        "PC     | Out HW | Out HD | fg0 HW | fg0 HD | fg1 HW | fg1 HD | "
        "In HW  | In HD  | Source\n"
    )
    header2 = (
        "-------|--------|--------|--------|--------|--------|--------|"
        "--------|--------|--------------------------\n"
    )

    with open(trace_path, "w") as f:
        f.write(header1)
        f.write(header2)

        for line in lines:
            if line.strip().startswith("0x"):
                try:
                    parts = line.strip().split()
                    pc_str = parts[0]
                    pc = int(pc_str, 16)
                    m = [int(x) for x in parts[1:9]]

                    dwarf_str = ""
                    if pc in dwarf_map:
                        filepath, lineno = dwarf_map[pc]
                        filename = os.path.basename(filepath)
                        dwarf_str = f"// [{filename}:{lineno}]"

                    formatted = (
                        f"{pc_str:<6} | {m[0]:>6} | {m[1]:>6} | {m[2]:>6} | {m[3]:>6} | "
                        f"{m[4]:>6} | {m[5]:>6} | {m[6]:>6} | {m[7]:>6} | {dwarf_str}\n"
                    )
                    f.write(formatted)
                except Exception:
                    pass


def generate_shares(
    mode: str, secret: int, share_size: int, modulus: Optional[int] = None
) -> Tuple[int, Optional[int]]:
    """Generates shares based on the selected cryptographic masking mode."""
    if mode == "boolean":
        # share0 ^ share1 = secret
        r = random.getrandbits(share_size * 8)
        share0 = secret ^ r
        share1 = r
        return share0, share1

    elif mode == "additive":
        # (share0 + share1) mod n = secret
        if modulus is None:
            raise ValueError("Modulus required for additive sharing")
        r = random.randrange(0, modulus)
        share0 = (secret - r) % modulus
        share1 = r
        return share0, share1

    elif mode == "subtractive":
        # (share0 - share1) mod n = secret
        if modulus is None:
            raise ValueError("Modulus required for subtractive sharing")
        r = random.randrange(0, modulus)
        share0 = (secret + r) % modulus
        share1 = r
        return share0, share1

    elif mode == "scalar_blind":
        # ECC specific: share0 = secret + r0*n, share1 = r1*n
        if modulus is None:
            raise ValueError("Modulus required for scalar blinding")
        blind_bits = (share_size * 8) - modulus.bit_length()
        if blind_bits <= 0:
            raise ValueError("Error in blinding bits size")
        r0 = random.getrandbits(blind_bits)
        r1 = random.getrandbits(blind_bits)
        share0 = secret + (r0 * modulus)
        share1 = r1 * modulus
        return share0, share1

    elif mode in ["const", "enum"]:
        return secret, None

    raise ValueError(f"Unknown mode: {mode}")


def run_experiment(
    task: Tuple[str, str, int, int, int, Dict[str, Any]]
) -> Tuple[
    int,
    int,
    Dict[Tuple[int, int], List[Any]],
    Dict[Tuple[int, int, str], Tuple[int, List[int], List[int]]],
]:
    """Runs a batched simulation."""
    _, elf_path, set_idx, batch_num, batch_size, cfg = task
    random.seed()

    # Write to RAM
    shm_dir = "/dev/shm" if os.path.exists("/dev/shm") else None

    trace_hw = tempfile.NamedTemporaryFile(dir=shm_dir, mode="w+", delete=False)
    trace_path = trace_hw.name

    local_stats = {}
    local_port_slices: Dict[Tuple[int, int, str], Tuple[int, List[int], List[int]]] = {}

    try:
        batch_dmem = []
        is_random_set = set_idx == 1

        for _ in range(batch_size):
            trace_dict = {}

            # Target shares (fixed vs random / enum state 0 vs state 1)
            for tvla in cfg["tvla_secrets"]:
                if is_random_set:
                    if tvla["mode"] == "enum":
                        current_secret = tvla["alt_secret"]
                    else:
                        bit_len = tvla["size"] * 8
                        current_secret = random.getrandbits(bit_len)
                        if tvla["modulus"]:
                            current_secret = current_secret % tvla["modulus"]
                else:
                    current_secret = tvla["secret"]

                share0, share1 = generate_shares(
                    tvla["mode"], current_secret, tvla["size"], tvla["modulus"]
                )
                trace_dict[tvla["symbols"][0]] = share0.to_bytes(
                    tvla["size"], "little"
                ).hex()
                if share1 is not None and len(tvla["symbols"]) > 1:
                    trace_dict[tvla["symbols"][1]] = share1.to_bytes(
                        tvla["size"], "little"
                    ).hex()

            # Fixed background (value is always the same)
            for bg in cfg["fixed_bg_secrets"]:
                bg_share0, bg_share1 = generate_shares(
                    bg["mode"], bg["secret"], bg["size"], bg["modulus"]
                )
                trace_dict[bg["symbols"][0]] = bg_share0.to_bytes(
                    bg["size"], "little"
                ).hex()
                if bg_share1 is not None and len(bg["symbols"]) > 1:
                    trace_dict[bg["symbols"][1]] = bg_share1.to_bytes(
                        bg["size"], "little"
                    ).hex()

            # Random background (value is randomized on every trace)
            for bg in cfg["random_bg_secrets"]:
                if bg["mode"] == "enum":
                    rnd_sec = random.choice([bg["secret"], bg["alt_secret"]])
                else:
                    bit_len = bg["size"] * 8
                    rnd_sec = random.getrandbits(bit_len)
                    if bg["modulus"]:
                        rnd_sec = rnd_sec % bg["modulus"]

                bg_share0, bg_share1 = generate_shares(
                    bg["mode"], rnd_sec, bg["size"], bg["modulus"]
                )
                trace_dict[bg["symbols"][0]] = bg_share0.to_bytes(
                    bg["size"], "little"
                ).hex()
                if bg_share1 is not None and len(bg["symbols"]) > 1:
                    trace_dict[bg["symbols"][1]] = bg_share1.to_bytes(
                        bg["size"], "little"
                    ).hex()

            batch_dmem.append(trace_dict)

        parsed_batch_dmem = []
        for dmem_dict in batch_dmem:
            parsed_dict = {k: bytes.fromhex(v) for k, v in dmem_dict.items()}
            parsed_batch_dmem.append(parsed_dict)

        sim = TVLASim(trace_hw_file=trace_hw)
        load_elf(sim, elf_path)

        key0 = int((str("deadbeef") * 16), 16)
        key1 = int((str("baadf00d") * 16), 16)
        sim.state.wsrs.set_sideload_keys(key0, key1)

        sim.run_batch(
            verbose=False, batch_size=batch_size, dmem_batch_data=parsed_batch_dmem
        )

        for key, (vals_a, vals_b) in sim.port_pairs.items():
            if any(vals_a) and any(vals_b) and (key[2] == "XBit" or vals_a != vals_b):
                local_port_slices[key] = (
                    len(vals_a),
                    transpose_128x256(vals_a),
                    transpose_128x256(vals_b),
                )

        trace_hw.flush()
        trace_hw.seek(0)

        pc_counts = Counter()
        for line in trace_hw:
            # Check if the state is cleared
            if line.startswith("==="):
                pc_counts.clear()
                continue

            parts = line.strip().split()
            if not parts:
                continue

            pc = int(parts[0], 16)
            hws = [int(x) for x in parts[1:]]

            occ = pc_counts[pc]

            if (pc, occ) not in local_stats:
                # [count, sums_array, sum_sqs_array]
                local_stats[(pc, occ)] = [0, [0.0] * NUM_MODELS, [0.0] * NUM_MODELS]

            stats = local_stats[(pc, occ)]
            stats[0] += 1
            for i in range(NUM_MODELS):
                stats[1][i] += hws[i]
                stats[2][i] += hws[i] ** 2

            pc_counts[pc] += 1

        if not local_stats:
            print(f"\nBatch {batch_num} produced an empty trace file.", flush=True)

    except Exception as e:
        print(f"\nBatch {batch_num} python exception: {e}", flush=True)
    finally:
        trace_hw.close()
        if os.path.exists(trace_path):
            os.remove(trace_path)

    return batch_num, set_idx, local_stats, local_port_slices


def generate_reference_trace(
    simulator_path: str,
    elf_path: str,
    dwarf_map: Dict[int, Tuple[str, int]],
    cfg: Dict[str, Any],
) -> None:
    """Generates a single annotated trace file for manual inspection."""
    # simulator_path is ignored
    print("--- Generating Annotated Reference Trace ---", flush=True)
    out_dir = os.environ.get("TEST_UNDECLARED_OUTPUTS_DIR", ".")
    ref_trace_path = os.path.join(out_dir, "tvla_reference_trace.log")

    trace_dict = {}

    # Generate target shares
    for tvla in cfg["tvla_secrets"]:
        share0, share1 = generate_shares(
            tvla["mode"], tvla["secret"], tvla["size"], tvla["modulus"]
        )
        trace_dict[tvla["symbols"][0]] = share0.to_bytes(tvla["size"], "little").hex()
        if share1 is not None and len(tvla["symbols"]) > 1:
            trace_dict[tvla["symbols"][1]] = share1.to_bytes(tvla["size"], "little").hex()

    # Generate fixed background shares
    for bg in cfg["fixed_bg_secrets"]:
        bg_share0, bg_share1 = generate_shares(
            bg["mode"], bg["secret"], bg["size"], bg["modulus"]
        )
        trace_dict[bg["symbols"][0]] = bg_share0.to_bytes(bg["size"], "little").hex()
        if bg_share1 is not None and len(bg["symbols"]) > 1:
            trace_dict[bg["symbols"][1]] = bg_share1.to_bytes(bg["size"], "little").hex()

    # Generate random background shares
    for bg in cfg["random_bg_secrets"]:
        bit_len = bg["size"] * 8
        rnd_sec = random.getrandbits(bit_len)
        if bg["modulus"]:
            rnd_sec = rnd_sec % bg["modulus"]

        bg_share0, bg_share1 = generate_shares(
            bg["mode"], rnd_sec, bg["size"], bg["modulus"]
        )
        trace_dict[bg["symbols"][0]] = bg_share0.to_bytes(bg["size"], "little").hex()
        if bg_share1 is not None and len(bg["symbols"]) > 1:
            trace_dict[bg["symbols"][1]] = bg_share1.to_bytes(bg["size"], "little").hex()

    parsed_dmem = {k: bytes.fromhex(v) for k, v in trace_dict.items()}

    with open(ref_trace_path, "w") as ref_trace_file:
        sim = TVLASim(trace_hw_file=ref_trace_file)
        load_elf(sim, elf_path)

        key0 = int((str("deadbeef") * 16), 16)
        key1 = int((str("baadf00d") * 16), 16)
        sim.state.wsrs.set_sideload_keys(key0, key1)

        sim.run_batch(verbose=False, batch_size=1, dmem_batch_data=[parsed_dmem])

    annotate_trace_file(ref_trace_path, dwarf_map)

    abs_path = os.path.abspath(ref_trace_path)
    if "/sandbox/" in abs_path and "/execroot/" in abs_path:
        final_path = (
            abs_path[: abs_path.find("/sandbox/")] +
            abs_path[abs_path.find("/execroot/"):]
        )
    else:
        final_path = abs_path

    print(f"Reference trace file path: {final_path}\n", flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description="OTBN TVLA Side-Channel Assessment")
    parser.add_argument("simulator", help="Path to otbnsim executable")
    parser.add_argument("--elf", required=True, help="Target ELF file")
    parser.add_argument(
        "--num-experiments", type=int, default=1000, help="Total runs (split 50/50)"
    )
    parser.add_argument(
        "--t-threshold", type=float, default=6.0, help="T-Test leakage threshold"
    )
    parser.add_argument(
        "--tvla-secret",
        action="append",
        required=True,
        help="Format: sym0,sym1:mode:size:hex_secret[:hex_modulus]",
    )
    parser.add_argument(
        "--fixed-bg-secret",
        action="append",
        default=[],
        help="Format: sym0,sym1:mode:size:hex_secret[:hex_modulus]",
    )
    parser.add_argument(
        "--random-bg-secret",
        action="append",
        default=[],
        help="Format: sym0,sym1:mode:size:hex_secret[:hex_modulus]",
    )

    args = parser.parse_args()

    def parse_secret_args(arg_list: List[str]) -> List[Dict[str, Any]]:
        secrets = []
        for item in arg_list:
            parts = item.split(":")
            mode = parts[1]
            size = int(parts[2])
            secret = int(parts[3], 16)
            alt_secret = (
                int(parts[4], 16)
                if len(parts) > 4 and parts[4] and mode == "enum"
                else None
            )
            modulus = (
                int(parts[4], 16)
                if len(parts) > 4 and parts[4] and mode != "enum"
                else None
            )
            secrets.append(
                {
                    "symbols": parts[0].split(","),
                    "mode": mode,
                    "size": size,
                    "secret": secret,
                    "alt_secret": alt_secret,
                    "modulus": modulus,
                }
            )
        return secrets

    gen_config = {
        "tvla_secrets": parse_secret_args(args.tvla_secret),
        "fixed_bg_secrets": parse_secret_args(args.fixed_bg_secret),
        "random_bg_secrets": parse_secret_args(args.random_bg_secret),
    }

    # Extract DWARF map
    dwarf_map = build_pc_to_line_map(args.elf)

    # Generate the reference trace
    generate_reference_trace(args.simulator, args.elf, dwarf_map, gen_config)

    accumulator = TVLAAccumulator()
    max_threads = max(1, multiprocessing.cpu_count() - 2)

    BATCH_SIZE = 100
    num_fixed_batches = (args.num_experiments // 2) // BATCH_SIZE
    num_random_batches = (args.num_experiments // 2) // BATCH_SIZE

    print(
        f"--- Starting Batched TVLA ({args.num_experiments} traces on {max_threads} cores) ---",
        flush=True,
    )

    batches = [0] * num_fixed_batches + [1] * num_random_batches
    random.shuffle(batches)

    tasks = [
        (args.simulator, args.elf, set_idx, i, BATCH_SIZE, gen_config)
        for i, set_idx in enumerate(batches)
    ]

    completed_traces = 0

    with concurrent.futures.ProcessPoolExecutor(max_workers=max_threads) as executor:
        future_to_task = {executor.submit(run_experiment, task): task for task in tasks}

        for future in concurrent.futures.as_completed(future_to_task):
            completed_traces += BATCH_SIZE
            print(
                f"Completed {completed_traces}/{args.num_experiments} traces",
                flush=True,
            )

            try:
                batch_num, set_idx, local_stats, local_port_slices = future.result()

                for (pc, occ), (count, sums, sqs) in local_stats.items():
                    accumulator.counts[pc][occ][set_idx] += count
                    for i in range(NUM_MODELS):
                        accumulator.sums[pc][occ][set_idx][i] += sums[i]
                        accumulator.sum_sqs[pc][occ][set_idx][i] += sqs[i]

                for (pc, occ, tag), (p_cnt, sa, sb) in local_port_slices.items():
                    accumulator.add_port_slices(
                        pc, occ, tag, set_idx, p_cnt, sa, sb
                    )

            except Exception as e:
                print(f"Process crashed: {e}", flush=True)

    print("\n--- Analyzing T-Test Statistics ---", flush=True)

    n0, n1 = 0, 0

    if accumulator.counts:
        first_pc = sorted(accumulator.counts.keys())[0]
        n0 = accumulator.counts[first_pc][0][0]
        n1 = accumulator.counts[first_pc][0][1]
        print(
            f"Engine loaded {n0} fixed traces and {n1} random traces.",
            flush=True,
        )

    leakages_found = 0
    max_t_score = 0.0

    for pc in sorted(accumulator.counts.keys()):
        for occ in accumulator.counts[pc].keys():
            models = [
                (
                    MODEL_NAMES.get(model_idx, f"M{model_idx}"),
                    accumulator.compute_t_test(pc, occ, model_idx),
                )
                for model_idx in range(NUM_MODELS)
            ]
            for tag in sorted(accumulator.port_tags[pc][occ]):
                xbit_t, bit_a, bit_b = accumulator.compute_cross_bit_t_test(
                    pc, occ, tag
                )
                models.append((f"{tag}({bit_a},{bit_b})", xbit_t))

            for model_name, t_val in models:
                abs_t = abs(t_val)

                if abs_t > max_t_score:
                    max_t_score = abs_t

                if abs_t > args.t_threshold:
                    dwarf_str = "Unknown source"
                    if pc in dwarf_map:
                        filepath, lineno = dwarf_map[pc]
                        dwarf_str = f"{os.path.basename(filepath)}:{lineno}"

                    print(
                        f"Leakage | PC: {hex(pc):<6} | Occ: {occ} | "
                        f"Model: {model_name:<16} | t-value: {t_val:>7.2f} | "
                        f"Source: {dwarf_str}",
                        flush=True,
                    )
                    leakages_found += 1

    print(
        f"\nThe maximum absolute t-value across all PCs and models was: {max_t_score:.2f}",
        flush=True,
    )

    print(
        f"\nCampaign complete. Total leakages > {args.t_threshold}: {leakages_found}",
        flush=True,
    )
    return 0 if leakages_found == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
