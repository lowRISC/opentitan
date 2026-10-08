# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Ibex Register File (RF) TVLA leakage assessment framework via GDB.

This module captures the 32-bit register file at every executed PC across Fixed-vs-Random
(FvsR) trace sets using GDB step tracing, feeds Hamming Weight (HW) and Hamming
Distance (HD) leakage models into the general ``TVLA`` accumulator in
``sw.host.penetrationtests.python.util.tvla``, and maps leaking PCs back to
C/assembly source lines using ``.dis`` disassembly files.
"""

import atexit
from collections import defaultdict
from contextlib import contextmanager
from dataclasses import dataclass, field
import json
import logging
import math
import multiprocessing
from multiprocessing.connection import Connection, wait as mp_wait
import os
import random
import re
import shutil
import signal
import struct
import tempfile
import time
import traceback
from typing import Any, Dict, Iterable, List, Optional, Set, Tuple

from sw.host.penetrationtests.python.util import common_library
from sw.host.penetrationtests.python.util import qemu as qemu_mod
from sw.host.penetrationtests.python.util.dis_parser import DisParser
from sw.host.penetrationtests.python.util.gdb_controller import GDBController
from sw.host.penetrationtests.python.util.qemu import (
    get_qemu_monitor,
    is_qemu_available,
)
from sw.host.penetrationtests.python.util.targets import Target, TargetConfig
from sw.host.penetrationtests.python.util.tvla import (
    TVLA,
    hamming_distance,
    hamming_weight,
)

logger = logging.getLogger(__name__)

# RISC-V ABI names for x0..x31.
RISCV_ABI_NAMES: Tuple[str, ...] = (
    "zero",
    "ra",
    "sp",
    "gp",
    "tp",
    "t0",
    "t1",
    "t2",
    "s0",
    "s1",
    "a0",
    "a1",
    "a2",
    "a3",
    "a4",
    "a5",
    "a6",
    "a7",
    "s2",
    "s3",
    "s4",
    "s5",
    "s6",
    "s7",
    "s8",
    "s9",
    "s10",
    "s11",
    "t3",
    "t4",
    "t5",
    "t6",
)


def reg_label(reg_idx: int) -> str:
    """Return a human-readable ``xN(abi)`` register label for ``0 <= reg_idx < 32``."""
    if 0 <= reg_idx < len(RISCV_ABI_NAMES):
        return f"x{reg_idx}({RISCV_ABI_NAMES[reg_idx]})"
    return f"x{reg_idx}"


def resolve_firmware_artifact(firmware_path: str, ext: str) -> str:
    """Locate the companion ``.dis`` or ``.elf`` artifact for a firmware binary.

    Works with both FPGA binaries (``*.img``, ``*.bin``) and QEMU signed binaries
    (``*.rv32imcb.test_key_0.signed.bin``).
    """
    if not ext.startswith("."):
        ext = "." + ext

    # Direct suffix strip for FPGA (.img/.bin) and QEMU (.rv32imcb.*.signed.bin).
    stripped = re.sub(
        r"(\.rv32[a-z0-9_]+)?(\.[^./]+)?(\.signed)?\.(bin|img|elf|dis)$",
        "",
        firmware_path,
    )
    candidate = stripped + ext
    if os.path.exists(candidate):
        return candidate

    # Fallback: search the directory for a matching artifact.
    directory = os.path.dirname(os.path.abspath(firmware_path))
    base_prefix = os.path.basename(stripped).split(".")[0]
    if os.path.isdir(directory):
        matches = [
            os.path.join(directory, f)
            for f in sorted(os.listdir(directory))
            if f.endswith(ext) and "rom_with_fake_keys" not in f or f.startswith(base_prefix)
        ]
        exact = [
            m
            for m in matches
            if os.path.basename(m).startswith(base_prefix) and m.endswith(ext)
        ]
        if exact:
            return exact[0]
        any_ext = [
            os.path.join(directory, f)
            for f in sorted(os.listdir(directory))
            if f.endswith(ext)
        ]
        if any_ext:
            return any_ext[0]

    raise FileNotFoundError(
        f"Could not find '{ext}' companion file for firmware '{firmware_path}' "
        f"(tried '{candidate}')."
    )


@dataclass(frozen=True)
class DecodedInstruction:
    """Parsed RISC-V assembly instruction with hardware-decoded operand registers."""

    pc: int
    insn_bits: int
    mnemonic: str
    operands_str: str
    raw_text: str
    source_loc: str = ""
    rd: Optional[int] = None
    rs1: Optional[int] = None
    rs2: Optional[int] = None


def decode_rv32imcb_regs(
    insn: int,
) -> Tuple[Optional[int], Optional[int], Optional[int]]:
    """Decode ``(rd, rs1, rs2)`` register indices directly from an RV32IMCB instruction word.

    Matches the register-file read/write port enables in ``ibex_compressed_decoder.sv``
    and ``ibex_decoder.sv`` without relying on ``objdump`` mnemonic strings or
    pseudo-instruction text.
    """
    # 1. 16-bit RVC compressed instructions (ibex_compressed_decoder.sv).
    if (insn & 0x3) != 0x3:
        quad = insn & 0x3
        funct3 = (insn >> 13) & 0x7

        if quad == 0b00:
            rd_p = ((insn >> 2) & 0x7) + 8
            rs1_p = ((insn >> 7) & 0x7) + 8
            if funct3 == 0b000:  # c.addi4spn -> addi rd', x2, imm
                return rd_p, 2, None
            if funct3 == 0b010:  # c.lw -> lw rd', imm(rs1')
                return rd_p, rs1_p, None
            if funct3 == 0b110:  # c.sw -> sw rs2', imm(rs1')
                return None, rs1_p, rd_p
            return None, None, None

        if quad == 0b01:
            rd_5 = (insn >> 7) & 0x1f
            rd_p = ((insn >> 7) & 0x7) + 8
            rs2_p = ((insn >> 2) & 0x7) + 8
            if funct3 == 0b000:  # c.addi / c.nop -> addi rd, rd, nzimm
                return rd_5, rd_5, None
            if funct3 == 0b001:  # c.jal -> jal x1, imm
                return 1, None, None
            if funct3 == 0b101:  # c.j -> jal x0, imm
                return 0, None, None
            if funct3 == 0b010:  # c.li -> addi rd, x0, nzimm
                return rd_5, 0, None
            if funct3 == 0b011:  # c.addi16sp / c.lui
                if rd_5 == 2:
                    return 2, 2, None
                return rd_5, None, None
            if funct3 == 0b100:
                funct2 = (insn >> 10) & 0x3
                if funct2 in (0b00, 0b01, 0b10):  # c.srli / c.srai / c.andi
                    return rd_p, rd_p, None
                return rd_p, rd_p, rs2_p  # c.sub / c.xor / c.or / c.and
            if funct3 in (0b110, 0b111):  # c.beqz / c.bnez -> beq/bne rs1', x0, imm
                return None, rd_p, 0
            return None, None, None

        if quad == 0b10:
            rd_5 = (insn >> 7) & 0x1f
            rs2_5 = (insn >> 2) & 0x1f
            if funct3 == 0b000:  # c.slli -> slli rd, rd, shamt
                return rd_5, rd_5, None
            if funct3 == 0b010:  # c.lwsp -> lw rd, imm(x2)
                return rd_5, 2, None
            if funct3 == 0b100:
                bit12 = (insn >> 12) & 0x1
                if bit12 == 0:
                    if rs2_5 != 0:  # c.mv -> add rd, x0, rs2
                        return rd_5, 0, rs2_5
                    return 0, rd_5, None  # c.jr -> jalr x0, rs1, 0
                if rs2_5 != 0:  # c.add -> add rd, rd, rs2
                    return rd_5, rd_5, rs2_5
                if rd_5 == 0:  # c.ebreak
                    return None, None, None
                return 1, rd_5, None  # c.jalr -> jalr x1, rs1, 0
            if funct3 == 0b110:  # c.swsp -> sw rs2, imm(x2)
                return None, 2, rs2_5
            return None, None, None

    # 2. 32-bit RV32IMCB instructions (ibex_decoder.sv).
    opcode = insn & 0x7f
    rd = (insn >> 7) & 0x1f
    funct3 = (insn >> 12) & 0x7
    rs1 = (insn >> 15) & 0x1f
    rs2 = (insn >> 20) & 0x1f

    if opcode in (0x37, 0x17, 0x6f):  # LUI, AUIPC, JAL
        return rd, None, None
    if opcode in (0x67, 0x03, 0x13):  # JALR, LOAD, OP-IMM
        return rd, rs1, None
    if opcode in (0x63, 0x23):  # BRANCH, STORE
        return None, rs1, rs2
    if opcode == 0x33:  # OP (register-register I/M/B)
        return rd, rs1, rs2
    if opcode == 0x73:  # SYSTEM
        if funct3 == 0:  # ecall, ebreak, mret, dret, wfi
            return None, None, None
        if (funct3 & 0x4) == 0:  # csrrw, csrrs, csrrc
            return rd, rs1, None
        return rd, None, None  # csrrwi, csrrsi, csrrci

    return None, None, None


def decode_dis_instructions(
    dis_parser: DisParser,
) -> Dict[int, DecodedInstruction]:
    """Decode all instructions from ``DisParser.parse_all_instructions()``."""
    decoded: Dict[int, DecodedInstruction] = {}
    for pc, info in dis_parser.parse_all_instructions().items():
        insn_bits = info["insn_bits"]
        rd, rs1, rs2 = decode_rv32imcb_regs(insn_bits)
        decoded[pc] = DecodedInstruction(
            pc=pc,
            insn_bits=insn_bits,
            mnemonic=info["mnemonic"],
            operands_str=info["operands"],
            raw_text=info["text"],
            source_loc=info["source_loc"],
            rd=rd,
            rs1=rs1,
            rs2=rs2,
        )
    return decoded


@dataclass
class LeakEntry:
    """Single statistically significant Ibex RF TVLA leakage point."""

    pc: int
    occ: int
    model: str
    t_stat: float
    mean_fixed: float
    mean_random: float
    count_fixed: int
    count_random: int
    instruction: str = ""
    source_loc: str = ""


class IbexRFTraceEvaluator:
    """Evaluates Ibex RF leakage models per PC and feeds them into the general ``TVLA`` class."""

    def __init__(
        self,
        instructions: Optional[Dict[int, DecodedInstruction]] = None,
        threshold: float = 7.0,
        max_pc_depth: Optional[int] = 2,
    ):
        self.instructions = instructions or {}
        self.tvla = TVLA(threshold=threshold)
        self.max_pc_depth = max_pc_depth
        self.sites: Set[Tuple[int, int]] = set()
        self.unique_pcs: Set[int] = set()

    @property
    def trace_counts(self) -> List[int]:
        return self.tvla.trace_counts

    def merge(self, other: "IbexRFTraceEvaluator") -> None:
        """Merge accumulated trace statistics from ``other`` into ``self``."""
        self.tvla.merge(other.tvla)
        self.sites.update(other.sites)
        self.unique_pcs.update(other.unique_pcs)

    def add_trace(
        self, group: int, trace: List[Tuple[int, Tuple[int, ...]]]
    ) -> None:
        """Add one execution trace of ``(pc, (x1, ..., x31))`` snapshots.

        Args:
            group: ``0`` for Fixed dataset, ``1`` for Random dataset.
            trace: Sequence of ``(pc, regs_x1_to_x31)`` captured BEFORE each instruction
                at ``pc`` executes (with an optional trailing ``TRACE_END`` state).
        """
        if group not in (0, 1) or not trace:
            return
        self.tvla.record_trace(group)

        occ_counter: Dict[int, int] = defaultdict(int)
        prev_rs1_val = 0
        prev_rs2_val = 0
        prev_rd_val = 0

        # If trace has N elements and the last element is TRACE_END, trace[:-1] are the
        # executed instructions and trace[i + 1] holds the post-execution register state.
        num_steps = len(trace) - 1 if len(trace) > 1 else len(trace)

        for idx in range(num_steps):
            pc, regs = trace[idx]
            next_regs = trace[idx + 1][1] if (idx + 1) < len(trace) else regs
            occ = occ_counter[pc]
            occ_counter[pc] = occ + 1
            self.unique_pcs.add(pc)
            record_site = (
                self.max_pc_depth is None or occ < self.max_pc_depth
            )

            if record_site:
                self.sites.add((pc, occ))

                # 1 & 2. Per-register Hamming Weight and Hamming Distance vectors (x1..x31).
                self.tvla.add_vector(
                    (pc, occ, "RF_HW"),
                    group,
                    [hamming_weight(next_regs[r_i]) for r_i in range(31)],
                )
                self.tvla.add_vector(
                    (pc, occ, "RF_HD"),
                    group,
                    [
                        hamming_distance(regs[r_i], next_regs[r_i])
                        for r_i in range(31)
                    ],
                )

            # 3. Instruction-aware models (matching otbn_tvla_campaign.py).
            insn = self.instructions.get(pc)
            if insn is None:
                continue

            curr_rs1_val: Optional[int] = None
            curr_rs2_val: Optional[int] = None

            if insn.rs1 is not None:
                curr_rs1_val = 0 if insn.rs1 == 0 else regs[insn.rs1 - 1]
                if record_site:
                    rlabel = reg_label(insn.rs1)
                    self.tvla.add_sample(
                        (pc, occ, f"HW_RS1({rlabel})"),
                        group,
                        hamming_weight(curr_rs1_val),
                    )
                    self.tvla.add_sample(
                        (pc, occ, f"HD_RS1({rlabel})"),
                        group,
                        hamming_distance(curr_rs1_val, prev_rs1_val),
                    )
                prev_rs1_val = curr_rs1_val

            if insn.rs2 is not None:
                curr_rs2_val = 0 if insn.rs2 == 0 else regs[insn.rs2 - 1]
                if record_site:
                    rlabel = reg_label(insn.rs2)
                    self.tvla.add_sample(
                        (pc, occ, f"HW_RS2({rlabel})"),
                        group,
                        hamming_weight(curr_rs2_val),
                    )
                    self.tvla.add_sample(
                        (pc, occ, f"HD_RS2({rlabel})"),
                        group,
                        hamming_distance(curr_rs2_val, prev_rs2_val),
                    )
                prev_rs2_val = curr_rs2_val

            if (
                record_site and
                curr_rs1_val is not None and
                curr_rs2_val is not None
            ):
                self.tvla.add_sample(
                    (pc, occ, "HD_RS1_RS2"),
                    group,
                    hamming_distance(curr_rs1_val, curr_rs2_val),
                )

            if insn.rd is not None and insn.rd != 0:
                old_rd = regs[insn.rd - 1]
                new_rd = next_regs[insn.rd - 1]
                if record_site:
                    rlabel = reg_label(insn.rd)
                    self.tvla.add_sample(
                        (pc, occ, f"HW_RD({rlabel})"),
                        group,
                        hamming_weight(new_rd),
                    )
                    self.tvla.add_sample(
                        (pc, occ, f"HD_RD({rlabel})"),
                        group,
                        hamming_distance(old_rd, new_rd),
                    )
                    self.tvla.add_sample(
                        (pc, occ, f"HD_RD_WR({rlabel})"),
                        group,
                        hamming_distance(new_rd, prev_rd_val),
                    )
                prev_rd_val = new_rd

    def compute_all_results(
        self,
        pc_to_line: Optional[Dict[int, str]] = None,
        include_rf_vectors: bool = True,
        include_insn_models: bool = True,
    ) -> List[LeakEntry]:
        """Compute Welch's t-statistics for all recorded ``(pc, occ, model)`` sites."""
        results: List[LeakEntry] = []
        pc_to_line = pc_to_line or {}

        for res in self.tvla.compute_all(nonzero_only=True):
            key = res.key
            if not isinstance(key, tuple):
                continue
            if len(key) == 4:
                if not include_rf_vectors:
                    continue
                pc, occ, vec_type, r_i = key
                model_name = f"{vec_type}({reg_label(r_i + 1)})"
            elif len(key) == 3:
                if not include_insn_models:
                    continue
                pc, occ, model_name = key
            else:
                continue

            insn = self.instructions.get(pc)
            insn_text = insn.raw_text if insn is not None else ""
            src_loc = pc_to_line.get(pc) or (
                insn.source_loc if insn is not None else ""
            )

            results.append(
                LeakEntry(
                    pc=pc,
                    occ=occ,
                    model=model_name,
                    t_stat=res.t_stat,
                    mean_fixed=res.mean_fixed,
                    mean_random=res.mean_random,
                    count_fixed=res.count_fixed,
                    count_random=res.count_random,
                    instruction=insn_text,
                    source_loc=src_loc,
                )
            )

        results.sort(key=lambda e: (e.pc, e.occ, e.model))
        return results

    def get_leaks(
        self,
        threshold: float = 7.0,
        pc_to_line: Optional[Dict[int, str]] = None,
        include_rf_vectors: bool = True,
        include_insn_models: bool = True,
    ) -> List[LeakEntry]:
        """Return all leakage entries where ``|t_stat| > threshold``."""
        all_entries = self.compute_all_results(
            pc_to_line=pc_to_line,
            include_rf_vectors=include_rf_vectors,
            include_insn_models=include_insn_models,
        )
        return [e for e in all_entries if abs(e.t_stat) > threshold]


_RF_TRACE_RE = re.compile(
    r"RF_TRACE(?:_END)?:\s+([0-9a-fA-F]+)((?:\s+[0-9a-fA-F]+){31})"
)


@dataclass
class TraceWindow:
    """Resolved ``(start_address, end_address)`` for GDB register-file tracing."""

    name: str
    start_address: str
    end_address: str
    skip_addresses: List[str] = field(default_factory=list)


@dataclass
class _RecordedTx:
    """Recorded uJSON transaction for parallel worker replay."""

    writes: List[bytes]
    num_responses: int = 1
    groups: List[int] = field(default_factory=list)
    is_trace: bool = False


def _write_paced(write_fn: Any, data: bytes) -> None:
    """Write ``data`` to UART at <=8 KB/s (16 B / 2 ms) so UART RX FIFO never overflows."""
    for i in range(0, len(data), 16):
        write_fn(data[i: i + 16])
        time.sleep(0.002)


def _read_response_direct(
    tgt: Target, init_timeout: int = 0, max_tries: int = 250
) -> str:
    """Read a ``RESP_OK:`` or ``RESP_ERR:`` line from ``tgt`` without tripping 1s timeout."""
    if init_timeout:
        time.sleep(init_timeout)
    idle_timeout = max(0.5 * max(max_tries, 1), 60.0)
    deadline = time.time() + idle_timeout
    com = getattr(tgt, "com_interface", None) or getattr(tgt, "com", None)
    orig_timeout = getattr(com, "timeout", None)
    if orig_timeout is not None:
        com.timeout = 0.02
    try:
        while time.time() < deadline:
            if getattr(getattr(com, "_qemu", None), "_faulted", False):
                break
            if getattr(com, "in_waiting", 1) > 0:
                raw = tgt.readline()
                if raw:
                    line = raw.decode("utf-8", errors="replace").strip()
                    if "RESP_OK:" in line:
                        return line.split("RESP_OK:")[1].split(" CRC:")[0]
                    if "RESP_ERR:" in line:
                        return line.split("RESP_ERR:")[1].split(" CRC:")[0]
            else:
                time.sleep(0.001)
    finally:
        if orig_timeout is not None and com is not None:
            com.timeout = orig_timeout
    return ""


def _advance_prng_for_tx(rng: random.Random, tx: _RecordedTx) -> None:
    """Advance ``rng`` to match firmware ``prng.c`` calls for one batch FvsR transaction."""
    if len(tx.writes) < 3:
        return
    try:
        subcmd = json.loads(tx.writes[1].decode("utf-8"))
        payload = json.loads(tx.writes[-1].decode("utf-8"))
    except Exception:
        return
    if not isinstance(subcmd, str) or not isinstance(payload, dict):
        return
    n_it = int(payload.get("num_iterations", 1))
    if subcmd.endswith("FvsrPlaintext"):
        d_len = int(payload["data_len"])
        sample_fixed = 1
        for _ in range(n_it):
            if sample_fixed == 0:
                for _ in range(d_len):
                    rng.randint(0, 255)
            sample_fixed = rng.randint(0, 255) & 0x1
    elif subcmd.endswith("BaseMulFvsr"):
        s_len = len(payload["scalar"])
        sample_fixed = 1
        for _ in range(n_it):
            if sample_fixed == 0:
                for _ in range(s_len):
                    rng.randint(0, 255)
            sample_fixed = rng.randint(0, 255) & 0x1
    elif subcmd.endswith("FvsrKey"):
        k_len = int(payload["key_len"])
        d_len = int(payload["data_len"])
        sample_fixed = 1
        for _ in range(n_it):
            if sample_fixed == 0:
                for _ in range(k_len):
                    rng.randint(0, 255)
            for _ in range(d_len):
                rng.randint(0, 255)
            sample_fixed = rng.randint(0, 255) & 0x1
    elif subcmd == "DrbgGenerateBatch":
        n_len = int(payload["nonce_len"])
        for _ in range(n_it):
            for _ in range(n_len):
                rng.randint(0, 255)


def _parallel_worker_process(
    send_conn: Connection,
    worker_idx: int,
    gdb_bin_path: str,
    firmware_path: str,
    elf_path: str,
    dis_path: str,
    threshold: float,
    max_pc_depth: Optional[int],
    window: TraceWindow,
    setup_txs: List[_RecordedTx],
    prng_state: Optional[Tuple[Tuple[int, ...], int]],
    shard_txs: List[_RecordedTx],
    base_otp_path: str,
    base_flash_path: str,
    predecoded: Tuple[DisParser, Dict[int, DecodedInstruction]],
) -> None:
    """Forked worker process that runs its shard in an isolated QEMU + GDB instance."""
    atexit._clear()

    def _sigterm_handler(signum: int, frame: Any) -> None:
        raise KeyboardInterrupt("Worker terminated")

    signal.signal(signal.SIGTERM, _sigterm_handler)

    worker_tmpdir = tempfile.mkdtemp(prefix=f"tvla_w{worker_idx}_")
    q_inst: Optional[qemu_mod.Qemu] = None
    worker_campaign: Optional["GDBTVLACampaign"] = None
    try:
        otp_path = os.path.join(worker_tmpdir, "otp.mut.raw")
        otp_orig_path = os.path.join(worker_tmpdir, "otp.orig.raw")
        flash_path = os.path.join(worker_tmpdir, "flash.mut.bin")
        flash_orig_path = os.path.join(worker_tmpdir, "flash.orig.bin")
        spiflash_path = os.path.join(worker_tmpdir, "spiflash.bin")

        shutil.copyfile(base_otp_path, otp_path)
        shutil.copyfile(base_otp_path, otp_orig_path)
        os.chmod(otp_path, 0o644)
        os.chmod(otp_orig_path, 0o644)

        shutil.copyfile(base_flash_path, flash_path)
        shutil.copyfile(base_flash_path, flash_orig_path)
        os.chmod(flash_path, 0o644)
        os.chmod(flash_orig_path, 0o644)

        with open(spiflash_path, "wb") as f_spi:
            f_spi.truncate(32 * 1024 * 1024)
        os.chmod(spiflash_path, 0o644)

        os.environ["QEMU_OTP"] = otp_path
        os.environ["QEMU_FLASH"] = flash_path
        os.environ["QEMU_SPIFLASH"] = spiflash_path
        os.environ["QEMU_PIDFILE"] = os.path.join(worker_tmpdir, "qemu.pid")
        os.environ["QEMU_LOG"] = os.path.join(worker_tmpdir, "qemu.log")
        os.environ["QEMU_MONITOR"] = os.path.join(worker_tmpdir, "qemu-monitor")
        os.environ["QEMU_GPIO"] = os.path.join(worker_tmpdir, "qemu-gpio.sock")
        os.environ["QEMU_GDB"] = os.path.join(worker_tmpdir, "qemu-gdb.sock")
        os.environ["QEMU_RV_DM_JTAG"] = os.path.join(
            worker_tmpdir, "qemu-jtag.sock"
        )
        os.environ["QEMU_LC_JTAG"] = os.path.join(
            worker_tmpdir, "qemu-jtag-lc-ctrl.sock"
        )
        qemu_mod._shared_monitor = None

        q_inst = qemu_mod.Qemu(fw_bin=firmware_path)
        q_inst.otp_orig_file = otp_orig_path
        q_inst.flash_orig_file = flash_orig_path
        q_inst._restart_qemu()

        worker_target = Target.__new__(Target)
        worker_target.target_cfg = TargetConfig(
            target_type="chip",
            interface_type="qemu",
            fw_bin=firmware_path,
        )
        worker_target.target = q_inst
        worker_target.com_interface = q_inst.init_communication(
            None, Target.baudrate
        )
        worker_target.initialize_target(print_output=False)
        q_inst.monitor._pc_tracing = True

        # Replay setup transactions (Init / SeedPrng).
        for tx in setup_txs:
            for w_chunk in tx.writes:
                _write_paced(worker_target.write, w_chunk)
            for _ in range(tx.num_responses):
                _read_response_direct(worker_target)

        worker_campaign = GDBTVLACampaign(
            target=worker_target,
            gdb_bin_path=gdb_bin_path,
            firmware_path=firmware_path,
            elf_path=elf_path,
            dis_path=dis_path,
            threshold=threshold,
            max_pc_depth=max_pc_depth,
            workers=1,
            _predecoded=predecoded,
            _initial_prng_state=prng_state,
        )

        last_resp = ""
        with worker_campaign.hook(worker_target, _window=window):
            for tx in shard_txs:
                worker_campaign.expect_groups(tx.groups)
                for w_chunk in tx.writes:
                    worker_target.write(w_chunk)
                for _ in range(tx.num_responses):
                    last_resp = worker_target.read_response()
                    if not last_resp:
                        raise RuntimeError(
                            f"Worker {worker_idx} timed out or faulted waiting for response."
                        )

        expected_traces = sum(len(tx.groups) for tx in shard_txs)
        acc = worker_campaign.accumulator
        actual_traces = sum(acc.trace_counts)
        if expected_traces > 0 and actual_traces != expected_traces:
            raise RuntimeError(
                f"Worker {worker_idx} captured {actual_traces}/{expected_traces} traces."
            )
        send_conn.send(
            (True, (acc.tvla, acc.sites, acc.unique_pcs, last_resp))
        )
    except BaseException:
        try:
            send_conn.send((False, traceback.format_exc()))
        except Exception:
            pass
    finally:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        try:
            send_conn.close()
        except Exception:
            pass
        if worker_campaign is not None:
            try:
                worker_campaign.close_gdb()
            except Exception:
                pass
        if q_inst is not None:
            try:
                if q_inst.serial:
                    q_inst.serial.close()
            except Exception:
                pass
            try:
                q_inst.monitor.close()
                q_inst.monitor.close_gpio()
            except Exception:
                pass
            try:
                q_inst._kill_qemu_pid()
            except Exception:
                pass
        shutil.rmtree(worker_tmpdir, ignore_errors=True)
        os._exit(0)


class GDBTVLACampaign:
    """Orchestrates GDB-based Register File TVLA trace capture and leakage analysis.

    Supports two usage styles:
    1. **Batch hook mode** (passing the Fixed=0 / Random=1 group schedule):
       ```python
       with campaign.hook(target, groups=groups):
           sca_sym_cryptolib_functions.char_aes_fvsr_plaintext(target, ...)
       leaks = campaign.get_leaks()
       ```
    2. **Explicit trace window / single-trace mode** (custom function or marker):
       ```python
       with campaign.hook(target, marker="PENTEST_MARKER_AES"):
           for group in (0, 1):
               campaign.expect_group(group)
               symfi.handle_aes(data[group], ...)
               target.read_response()
       ```
    """

    def __init__(
        self,
        target: Target,
        gdb_bin_path: str,
        firmware_path: str,
        gdb_port: int = 3333,
        elf_path: Optional[str] = None,
        dis_path: Optional[str] = None,
        threshold: float = 7.0,
        max_pc_depth: Optional[int] = 2,
        workers: int = 1,
        _predecoded: Optional[
            Tuple[DisParser, Dict[int, DecodedInstruction]]
        ] = None,
        _initial_prng_state: Optional[Tuple[Tuple[int, ...], int]] = None,
    ):
        self.target = target
        self.gdb_bin_path = gdb_bin_path
        self.firmware_path = firmware_path
        self.gdb_port = gdb_port
        self.elf_path = elf_path or resolve_firmware_artifact(firmware_path, ".elf")
        self.dis_path = dis_path or resolve_firmware_artifact(firmware_path, ".dis")
        self.threshold = threshold
        self.max_pc_depth = max_pc_depth
        if workers <= 0:
            workers = max(1, (os.cpu_count() or 2) // 2)
        self.workers = workers
        self._initial_prng_state = _initial_prng_state

        if _predecoded is not None:
            self.dis_parser, self.instructions = _predecoded
        else:
            self.dis_parser = DisParser(self.dis_path)
            self.instructions = decode_dis_instructions(self.dis_parser)
        self.accumulator = IbexRFTraceEvaluator(
            instructions=self.instructions,
            threshold=self.threshold,
            max_pc_depth=self.max_pc_depth,
        )

        self.gdb: Optional[GDBController] = None
        self._active_window: Optional[TraceWindow] = None
        self._gdb_buffer = ""
        self._gdb_scan_pos = 0
        self._pending_groups: List[int] = []

    def reset_stats(self) -> None:
        """Clear accumulated TVLA traces and pending groups."""
        self.accumulator = IbexRFTraceEvaluator(
            instructions=self.instructions,
            threshold=self.threshold,
            max_pc_depth=self.max_pc_depth,
        )
        self._pending_groups.clear()

    def expect_group(self, group: int) -> None:
        """Queue a single TVLA group label (``0``=Fixed, ``1``=Random) for the next trace."""
        if group not in (0, 1):
            raise ValueError(f"TVLA group must be 0 (Fixed) or 1 (Random), got {group}")
        self._pending_groups.append(group)

    def expect_groups(self, groups: Iterable[int]) -> None:
        """Queue a sequence of TVLA group labels (``0``=Fixed, ``1``=Random)."""
        for g in groups:
            self.expect_group(g)

    def resolve_trace_window(
        self,
        function: Optional[str] = None,
        marker: Optional[str] = None,
        start_address: Optional[str] = None,
        end_address: Optional[str] = None,
        skip_functions: Optional[Iterable[str]] = None,
    ) -> TraceWindow:
        """Determine the ``(start_address, end_address)`` trace window from ``.dis``."""
        if start_address is not None and end_address is not None:
            return TraceWindow(
                name=f"addr:{start_address}..{end_address}",
                start_address=start_address,
                end_address=end_address,
                skip_addresses=self._default_skip_addresses(
                    extra_functions=skip_functions
                ),
            )

        if marker is not None:
            start_addr, end_addr = self.dis_parser.get_marker_addresses(marker)
            return TraceWindow(
                name=f"marker:{marker}",
                start_address=start_addr,
                end_address=end_addr,
                skip_addresses=self._default_skip_addresses(
                    extra_functions=skip_functions
                ),
            )

        if function is not None:
            start_addr = self.dis_parser.get_function_start_address(function)
            if not start_addr:
                raise ValueError(f"Function '{function}' not found in {self.dis_path}")
            end_addr = (
                self.dis_parser.get_function_end_address(function) or "$trace_end_pc"
            )
            return TraceWindow(
                name=f"func:{function}",
                start_address=start_addr,
                end_address=end_addr,
                skip_addresses=self._default_skip_addresses(
                    exclude={function}, extra_functions=skip_functions
                ),
            )

        # Default SCA trigger window: `pentest_set_trigger_high` to `pentest_set_trigger_low`.
        start_addr = self.dis_parser.get_function_start_address(
            "pentest_set_trigger_high"
        )
        end_addr = self.dis_parser.get_function_start_address("pentest_set_trigger_low")
        return TraceWindow(
            name="trigger:pentest_set_trigger_high..pentest_set_trigger_low",
            start_address=start_addr,
            end_address=end_addr,
            skip_addresses=self._default_skip_addresses(
                extra_functions=skip_functions
            ),
        )

    def _default_skip_addresses(
        self,
        exclude: Optional[set] = None,
        extra_functions: Optional[Iterable[str]] = None,
    ) -> List[str]:
        exclude = exclude or set()
        skip: List[str] = []
        fn_list = [
            "pentest_call_and_sleep",
            "otbn_busy_wait_for_done",
            "pentest_otbn_busy_wait_for_done",
            "otbn_load_app",
            "otbn_dmem_sec_wipe",
            "otbn_imem_sec_wipe",
            "stateful_health_check",
            "run_kats",
            "ibex_rnd32_read",
            "hardened_memshred_random_word",
            "random_order_random_word",
        ]
        if extra_functions:
            fn_list.extend(extra_functions)
        for fn in fn_list:
            if fn in exclude:
                continue
            addr = self.dis_parser.get_function_start_address(fn)
            if addr and addr not in skip:
                skip.append(addr)
        return skip

    def ensure_gdb_armed(self, window: TraceWindow) -> None:
        """Connect GDB (if needed), install ``rf_traceloop`` at ``window``, and resume CPU."""
        if self.gdb is not None and self._active_window == window:
            return

        if (
            self.gdb is None or
            self.gdb.gdb_process is None or
            self.gdb.gdb_process.poll() is not None
        ):
            if not is_qemu_available():
                ocd_proc = getattr(
                    getattr(self.target, "target", None), "openocd_process", None
                )
                if ocd_proc is None or ocd_proc.poll() is not None:
                    self.target.start_openocd()
            else:
                self.target.start_openocd()
            self.gdb = GDBController(
                gdb_path=self.gdb_bin_path,
                gdb_port=self.gdb_port,
                elf_file=self.elf_path,
            )
            if not is_qemu_available():
                try:
                    self.gdb.send_command("monitor adapter speed 10000", timeout=2.0)
                    self.gdb.send_command("monitor poll_period 1", timeout=2.0)
                except Exception:
                    pass
        else:
            self.gdb.cleanup_skip()

        self._gdb_buffer = ""
        self._gdb_scan_pos = 0
        self._setup_rf_trace_in_gdb(window)
        if self._initial_prng_state is not None:
            mt_words, mti_val = self._initial_prng_state
            self._initial_prng_state = None
            with tempfile.NamedTemporaryFile(
                prefix="tvla_mt_", suffix=".bin", delete=False
            ) as f_mt:
                f_mt.write(struct.pack("<624I", *mt_words))
                mt_path = f_mt.name
            try:
                self.gdb.send_command(
                    "set $mt_addr = (unsigned int)&'prng.c'::mt",
                    timeout=2.0,
                    check_response=True,
                )
                self.gdb.send_command(
                    f"restore {mt_path} binary $mt_addr",
                    timeout=2.0,
                    check_response=True,
                )
                self.gdb.send_command(
                    f"set 'prng.c'::mti = {mti_val}",
                    timeout=2.0,
                    check_response=True,
                )
            finally:
                try:
                    os.unlink(mt_path)
                except OSError:
                    pass
        self._active_window = window
        self.gdb.send_command("c", check_response=False)
        deadline = time.time() + 2.0
        while time.time() < deadline:
            self._drain_gdb_output()
            if "Continuing." in self._gdb_buffer:
                idx = self._gdb_buffer.find("Continuing.")
                self._gdb_buffer = self._gdb_buffer[
                    idx + len("Continuing."):
                ].lstrip("\r\n")
                self._gdb_scan_pos = 0
                break
            time.sleep(0.002)
        if is_qemu_available():
            while time.time() < deadline:
                if get_qemu_monitor().is_running():
                    break
                time.sleep(0.005)
            time.sleep(0.005)

    def _setup_rf_trace_in_gdb(self, window: TraceWindow) -> None:
        assert self.gdb is not None
        reg_fmt = " ".join(["%x"] * 32)
        reg_args = ", ".join(["$pc"] + [f"$x{i}" for i in range(1, 32)])

        skip_block = ""
        if window.skip_addresses:
            cond = " || ".join(f"($pc == {addr})" for addr in window.skip_addresses)
            skip_block = f"""
        if ({cond})
            tbreak *$ra
            c
        end"""

        # If the breakpoint is on `pentest_set_trigger_high`, step silently out of
        # `pentest_set_trigger_high` (and its tail-called `dif_gpio_write`) back to `$ra`
        # before emitting `RF_TRACE` lines so GPIO MMIO instructions are excluded.
        trigger_prologue = ""
        if window.name.startswith("trigger:"):
            trigger_prologue = """
    set $trig_ret_pc = $ra
    set $trig_steps = 0
    while ($pc != $trig_ret_pc) && ($trig_steps < 64)
        stepi
        set $trig_steps = $trig_steps + 1
    end"""

        exc_addr = (
            self.dis_parser.get_function_start_address("handler_exception") or
            self.dis_parser.get_function_start_address("ottf_exception_handler")
        )
        idle_addr = self.dis_parser.get_function_start_address("ujson_getc")
        while_cond = f"($pc != {window.end_address})"
        if exc_addr:
            while_cond += f" && ($pc != {exc_addr})"
        if idle_addr:
            while_cond += f" && ($pc != {idle_addr})"

        gdb_script = f"""
set print frame-info short-location
set print frame-arguments none
define rf_traceloop
    set $trace_end_pc = $ra{trigger_prologue}
    while {while_cond}
        printf "\\nRF_TRACE: {reg_fmt}\\n", {reg_args}
        stepi{skip_block}
    end
    printf "\\nRF_TRACE_END: {reg_fmt}\\n", {reg_args}
end

b *({window.start_address})
commands
    silent
    printf "\\nRF_TRACE_START\\n"
    rf_traceloop
end
"""
        self.gdb.send_command(gdb_script.strip(), timeout=5.0, check_response=True)
        if is_qemu_available():
            try:
                self.gdb.send_command(
                    "maintenance packet Qqemu.sstep=0x3",
                    timeout=2.0,
                    check_response=True,
                )
            except Exception:
                pass
            get_qemu_monitor()._pc_tracing = True

    def close_gdb(self) -> None:
        """Detach and close the GDB process if active."""
        if self.gdb is not None:
            self.gdb.cleanup_skip()
            try:
                self.gdb.send_command("detach", check_response=False)
            except Exception:
                pass
            self.gdb.close_gdb()
            self.gdb = None
            self._active_window = None
            self._gdb_buffer = ""
            self._gdb_scan_pos = 0

    def _drain_gdb_output(self) -> None:
        """Non-blockingly drain all available output via ``GDBController.read_output``."""
        if self.gdb is None:
            return
        while True:
            chunk = self.gdb.read_output(print_errors=False, timeout=0.0)
            if not chunk:
                break
            self._gdb_buffer += chunk

    def _poll_and_consume_gdb_traces(self, pending_groups: List[int]) -> int:
        """Read GDB output, parse any completed ``RF_TRACE_END`` segments, and resume."""
        if self.gdb is None:
            return 0
        self._drain_gdb_output()

        consumed = 0
        while True:
            search_from = max(0, self._gdb_scan_pos - 16)
            end_pos = self._gdb_buffer.find("RF_TRACE_END:", search_from)
            if end_pos == -1:
                self._gdb_scan_pos = len(self._gdb_buffer)
                break
            nl_pos = self._gdb_buffer.find("\n", end_pos)
            if nl_pos == -1:
                self._gdb_scan_pos = end_pos
                break
            prompt_pos = self._gdb_buffer.find("(gdb)", nl_pos)
            if prompt_pos == -1:
                self._gdb_scan_pos = end_pos
                break

            segment_chunk = self._gdb_buffer[: nl_pos + 1]
            self._gdb_buffer = self._gdb_buffer[prompt_pos + len("(gdb)"):]
            self._gdb_scan_pos = 0

            # Resume GDB now that it has returned to the (gdb) prompt.
            self.gdb.send_command("c", check_response=False)

            if "RF_TRACE_START" in segment_chunk:
                segment_chunk = segment_chunk.split("RF_TRACE_START", 1)[1]

            trace: List[Tuple[int, Tuple[int, ...]]] = []
            for m in _RF_TRACE_RE.finditer(segment_chunk):
                pc = int(m.group(1), 16)
                regs = tuple(int(x, 16) for x in m.group(2).split())
                trace.append((pc, regs))

            group = pending_groups.pop(0) if pending_groups else 0
            if trace:
                self.accumulator.add_trace(group, trace)
                consumed += 1

        return consumed

    def _dispatch_parallel_transactions(
        self, window: TraceWindow, tx_list: List[_RecordedTx]
    ) -> str:
        """Shard recorded trace transactions across parallel QEMU + GDB workers."""
        setup_txs = [tx for tx in tx_list if not tx.is_trace]
        trace_txs = [tx for tx in tx_list if tx.is_trace]
        if not trace_txs:
            return '{"status": 0}'

        has_init = any(
            len(tx.writes) >= 2 and tx.writes[1] == b'"Init"'
            for tx in setup_txs
        )
        if (
            not has_init and
            trace_txs[0].writes and
            trace_txs[0].writes[0]
            in (b'"CryptoLibScaSym"', b'"CryptoLibScaAsym"')
        ):
            init_tx = _RecordedTx(
                writes=[
                    trace_txs[0].writes[0],
                    b'"Init"',
                    json.dumps(common_library.default_core_config).encode(
                        "ascii"
                    ),
                    json.dumps(common_library.default_sensor_config).encode(
                        "ascii"
                    ),
                ],
                num_responses=6,
                groups=[],
                is_trace=False,
            )
            setup_txs = [init_tx] + setup_txs

        prng_seed_val: Optional[int] = None
        for tx in setup_txs:
            if (
                len(tx.writes) >= 3 and
                tx.writes[0] == b'"PrngSca"' and
                tx.writes[1] == b'"SeedPrng"'
            ):
                try:
                    seed_arr = json.loads(tx.writes[2].decode("utf-8"))["seed"]
                    prng_seed_val = int.from_bytes(
                        bytes(seed_arr[:4]), "little"
                    )
                except Exception:
                    pass

        num_txs = len(trace_txs)
        num_workers = min(self.workers, num_txs)
        base_chunk, rem = divmod(num_txs, num_workers)
        slices: List[Tuple[int, int]] = []
        start = 0
        for w_idx in range(num_workers):
            end = start + base_chunk + (1 if w_idx < rem else 0)
            slices.append((start, end))
            start = end

        base_otp = (
            "otp_img.orig.raw"
            if os.path.exists("otp_img.orig.raw")
            else os.environ.get("QEMU_OTP", "otp_img.mut.raw")
        )
        base_flash = (
            "flash_img.orig.bin"
            if os.path.exists("flash_img.orig.bin")
            else os.environ.get("QEMU_FLASH", "flash_img.mut.bin")
        )
        base_otp_abs = os.path.abspath(base_otp)
        base_flash_abs = os.path.abspath(base_flash)

        ctx = multiprocessing.get_context("fork")
        procs: List[multiprocessing.Process] = []
        conn_to_idx: Dict[Connection, int] = {}
        results: Dict[int, Tuple[bool, Any]] = {}
        predecoded = (self.dis_parser, self.instructions)

        try:
            for w_idx, (s_w, e_w) in enumerate(slices):
                recv_conn, send_conn = ctx.Pipe(duplex=False)
                prng_state: Optional[Tuple[Tuple[int, ...], int]] = None
                if prng_seed_val is not None and s_w > 0:
                    w_rng = random.Random(prng_seed_val)
                    for p_tx in trace_txs[:s_w]:
                        _advance_prng_for_tx(w_rng, p_tx)
                    raw_st = w_rng.getstate()[1]
                    prng_state = (raw_st[:624], int(raw_st[624]))
                shard_txs = trace_txs[s_w:e_w]
                proc = ctx.Process(
                    target=_parallel_worker_process,
                    args=(
                        send_conn,
                        w_idx,
                        self.gdb_bin_path,
                        self.firmware_path,
                        self.elf_path,
                        self.dis_path,
                        self.threshold,
                        self.max_pc_depth,
                        window,
                        setup_txs,
                        prng_state,
                        shard_txs,
                        base_otp_abs,
                        base_flash_abs,
                        predecoded,
                    ),
                )
                proc.start()
                send_conn.close()
                procs.append(proc)
                conn_to_idx[recv_conn] = w_idx

            while conn_to_idx:
                for ready in mp_wait(list(conn_to_idx.keys())):
                    if not isinstance(ready, Connection):
                        continue
                    w_idx = conn_to_idx.pop(ready)
                    try:
                        results[w_idx] = ready.recv()
                    except EOFError:
                        results[w_idx] = (
                            False,
                            f"Worker {w_idx} exited unexpectedly without sending result.",
                        )
                    finally:
                        ready.close()
        finally:
            all_received = len(results) == len(procs)
            for proc in procs:
                if all_received:
                    proc.join(timeout=5.0)
                if proc.is_alive():
                    proc.terminate()
                    proc.join(timeout=2.0)

        final_resp = '{"status": 0}'
        for w_idx in range(num_workers):
            ok, payload = results.get(
                w_idx, (False, f"Missing result from worker {w_idx}")
            )
            if not ok:
                raise RuntimeError(
                    f"TVLA parallel worker {w_idx} failed:\n{payload}"
                )
            tvla_part, sites_part, pcs_part, w_resp = payload
            self.accumulator.tvla.merge(tvla_part)
            self.accumulator.sites.update(sites_part)
            self.accumulator.unique_pcs.update(pcs_part)
            if w_resp:
                final_resp = w_resp
        return final_resp

    @contextmanager
    def _hook_parallel(
        self,
        tgt: Target,
        window: TraceWindow,
        groups: Optional[Iterable[int]] = None,
        group: Optional[int] = None,
    ):
        """Record transactions in memory, then trace in parallel QEMU + GDB workers."""
        orig_write = tgt.write
        orig_read_response = tgt.read_response
        orig_reset_target = tgt.reset_target
        self.close_gdb()
        if is_qemu_available():
            get_qemu_monitor()._pc_tracing = True

        upfront_groups: List[int] = []
        if group is not None:
            upfront_groups.append(group)
        if groups is not None:
            upfront_groups.extend(groups)
        had_upfront_groups = bool(upfront_groups)
        self._pending_groups.clear()

        pending_writes: List[bytes] = []
        tx_list: List[_RecordedTx] = []
        dispatched = False

        def recording_write(data: bytes) -> None:
            pending_writes.append(bytes(data))

        def recording_read_response(
            init_timeout: int = 0, max_tries: int = 250
        ) -> str:
            nonlocal dispatched
            if not pending_writes:
                if tx_list and not tx_list[-1].is_trace:
                    tx_list[-1].num_responses += 1
                return '{"status": 0}'

            while (
                len(pending_writes) > 3 and pending_writes[0] == b'"PrngSca"'
            ):
                tx_list.append(
                    _RecordedTx(
                        writes=list(pending_writes[:3]),
                        num_responses=0,
                        groups=[],
                        is_trace=False,
                    )
                )
                del pending_writes[:3]

            if len(pending_writes) >= 2 and pending_writes[1] == b'"Init"':
                tx_list.append(
                    _RecordedTx(
                        writes=list(pending_writes),
                        num_responses=1,
                        groups=[],
                        is_trace=False,
                    )
                )
                pending_writes.clear()
                return '{"status": 0}'

            if self._pending_groups:
                tx_groups = list(self._pending_groups)
                self._pending_groups.clear()
            elif upfront_groups:
                n_it = 1
                try:
                    payload = json.loads(pending_writes[-1].decode("utf-8"))
                    if (
                        isinstance(payload, dict) and
                        "num_iterations" in payload
                    ):
                        n_it = int(payload["num_iterations"])
                except Exception:
                    pass
                tx_groups = upfront_groups[:n_it]
                del upfront_groups[:n_it]
            else:
                tx_groups = []

            tx_list.append(
                _RecordedTx(
                    writes=list(pending_writes),
                    num_responses=1,
                    groups=tx_groups,
                    is_trace=True,
                )
            )
            pending_writes.clear()

            if had_upfront_groups and not upfront_groups and not dispatched:
                dispatched = True
                return self._dispatch_parallel_transactions(window, tx_list)
            return '{"status": 0}'

        tgt.write = recording_write  # type: ignore[method-assign]
        tgt.read_response = recording_read_response  # type: ignore[method-assign]
        try:
            yield self
            tgt.write = orig_write  # type: ignore[method-assign]
            tgt.read_response = orig_read_response  # type: ignore[method-assign]
            tgt.reset_target = orig_reset_target  # type: ignore[method-assign]
            if not dispatched:
                dispatched = True
                self._dispatch_parallel_transactions(window, tx_list)
        finally:
            tgt.write = orig_write  # type: ignore[method-assign]
            tgt.read_response = orig_read_response  # type: ignore[method-assign]
            tgt.reset_target = orig_reset_target  # type: ignore[method-assign]

    @contextmanager
    def hook(
        self,
        target: Optional[Target] = None,
        groups: Optional[Iterable[int]] = None,
        group: Optional[int] = None,
        function: Optional[str] = None,
        marker: Optional[str] = None,
        start_address: Optional[str] = None,
        end_address: Optional[str] = None,
        skip_functions: Optional[Iterable[str]] = None,
        _window: Optional[TraceWindow] = None,
    ):
        """Context manager that arms GDB at the trace window and captures RF traces.

        Args:
            target: Target instance (defaults to ``self.target``).
            groups: Optional sequence of TVLA group labels (``0``=Fixed, ``1``=Random)
                for batch operations.
            group: Optional single TVLA group label (``0`` or ``1``) for a single trace.
            function: Optional C/assembly function name to trace instead of the default
                ``pentest_set_trigger_high``..``pentest_set_trigger_low`` window.
            marker: Optional ``PENTEST_MARKER_LABEL(...)`` name to trace.
            start_address: Optional explicit start address hex string.
            end_address: Optional explicit end address hex string.
            skip_functions: Optional iterable of function names to fast-skip via
                ``tbreak *$ra`` during instruction stepping.
        """
        tgt = target or self.target
        window = _window or self.resolve_trace_window(
            function=function,
            marker=marker,
            start_address=start_address,
            end_address=end_address,
            skip_functions=skip_functions,
        )

        if self.workers > 1 and is_qemu_available():
            with self._hook_parallel(
                tgt=tgt, window=window, groups=groups, group=group
            ):
                yield self
            return

        orig_write = tgt.write
        orig_read_response = tgt.read_response
        orig_reset_target = tgt.reset_target

        self._pending_groups.clear()
        if group is not None:
            self.expect_group(group)
        if groups is not None:
            self.expect_groups(groups)

        self.ensure_gdb_armed(window)

        def hooked_reset_target(*args: Any, **kwargs: Any) -> Any:
            self.close_gdb()
            try:
                tgt.close_openocd()
            except Exception:
                pass
            return orig_reset_target(*args, **kwargs)

        def hooked_write(data: bytes) -> None:
            if self.gdb is None:
                self.ensure_gdb_armed(window)
            if self.gdb is not None:
                _write_paced(orig_write, data)
            else:
                orig_write(data)

        def hooked_read_response(
            init_timeout: int = 0, max_tries: int = 250
        ) -> str:
            if self.gdb is None:
                return orig_read_response(
                    init_timeout=init_timeout, max_tries=max_tries
                )

            if init_timeout:
                time.sleep(init_timeout)
            idle_timeout = max(0.5 * max(max_tries, 1), 120.0)
            deadline = time.time() + idle_timeout
            com = getattr(tgt, "com_interface", None) or getattr(tgt, "com", None)
            orig_timeout = getattr(com, "timeout", None)
            if orig_timeout is not None:
                com.timeout = 0.02
            prev_buf_len = len(self._gdb_buffer)
            try:
                while time.time() < deadline:
                    consumed = self._poll_and_consume_gdb_traces(self._pending_groups)
                    cur_buf_len = len(self._gdb_buffer)
                    if consumed > 0 or cur_buf_len != prev_buf_len:
                        deadline = time.time() + idle_timeout
                        prev_buf_len = cur_buf_len
                    if getattr(getattr(com, "_qemu", None), "_faulted", False):
                        break
                    if getattr(com, "in_waiting", 1) > 0:
                        raw = tgt.readline()
                        if raw:
                            line = raw.decode("utf-8", errors="replace").strip()
                            if "RESP_OK:" in line:
                                self._poll_and_consume_gdb_traces(self._pending_groups)
                                return line.split("RESP_OK:")[1].split(" CRC:")[0]
                            if "RESP_ERR:" in line:
                                self._poll_and_consume_gdb_traces(self._pending_groups)
                                return line.split("RESP_ERR:")[1].split(" CRC:")[0]
                    else:
                        time.sleep(0.001)
            finally:
                if orig_timeout is not None and com is not None:
                    com.timeout = orig_timeout
            return ""

        tgt.write = hooked_write  # type: ignore[method-assign]
        tgt.read_response = hooked_read_response  # type: ignore[method-assign]
        tgt.reset_target = hooked_reset_target  # type: ignore[method-assign]
        try:
            yield self
        finally:
            tgt.write = orig_write  # type: ignore[method-assign]
            tgt.read_response = orig_read_response  # type: ignore[method-assign]
            tgt.reset_target = orig_reset_target  # type: ignore[method-assign]
            self.close_gdb()

    def get_leaks(
        self,
        threshold: Optional[float] = None,
        include_rf_vectors: bool = True,
        include_insn_models: bool = True,
    ) -> List[LeakEntry]:
        """Return all TVLA leakage entries exceeding ``threshold`` (default ``self.threshold``)."""
        thresh = self.threshold if threshold is None else threshold
        return self.accumulator.get_leaks(
            threshold=thresh,
            include_rf_vectors=include_rf_vectors,
            include_insn_models=include_insn_models,
        )

    def format_report(
        self,
        threshold: Optional[float] = None,
        max_entries: int = 40,
        include_rf_vectors: bool = True,
        include_insn_models: bool = True,
    ) -> str:
        """Format a human-readable TVLA report modeled after ``otbn_tvla_campaign.py``."""
        thresh = self.threshold if threshold is None else threshold
        all_results = self.accumulator.compute_all_results(
            include_rf_vectors=include_rf_vectors,
            include_insn_models=include_insn_models,
        )
        leaks = [e for e in all_results if abs(e.t_stat) > thresh]
        n0, n1 = self.accumulator.trace_counts
        lines = [
            "=" * 100,
            f"IBEX RF TVLA REPORT (Fixed={n0} traces, Random={n1} traces, "
            f"UniquePCs={len(self.accumulator.unique_pcs)}, "
            f"Sites={len(self.accumulator.sites)}, "
            f"MaxPCDepth={self.max_pc_depth}, Threshold=|t|>{thresh})",
            "=" * 100,
        ]
        if not leaks:
            top_any = sorted(all_results, key=lambda e: abs(e.t_stat), reverse=True)[:5]
            top_str = ", ".join(
                f"0x{e.pc:x}:{e.model}={e.t_stat:+.2f}"
                f"(F={e.mean_fixed:.1f}/R={e.mean_random:.1f},"
                f"n={e.count_fixed}/{e.count_random})"
                for e in top_any
            )
            lines.append(
                "Result: PASS (0 leaking (PC, occ, model) sites above threshold; "
                f"top: [{top_str}])"
            )
            return "\n".join(lines)

        leaks_sorted = sorted(leaks, key=lambda e: abs(e.t_stat), reverse=True)
        lines.append(
            f"Result: LEAKAGE DETECTED ({len(leaks_sorted)} leaking sites above |t| > {thresh})"
        )
        lines.append(
            f"{'PC':<12} | {'Occ':<4} | {'Model':<22} | {'t-stat':<9} | "
            f"{'Mean(F/R)':<15} | {'Instruction':<26} | {'Source'}"
        )
        lines.append("-" * 100)
        for entry in leaks_sorted[:max_entries]:
            t_str = (
                f"{entry.t_stat:+.2f}"
                if math.isfinite(entry.t_stat)
                else ("+INF" if entry.t_stat > 0 else "-INF")
            )
            means = f"{entry.mean_fixed:.2f}/{entry.mean_random:.2f}"
            lines.append(
                f"0x{entry.pc:08x}   | {entry.occ:<4} | {entry.model:<22} | {t_str:<9} | "
                f"{means:<15} | {entry.instruction:<26} | {entry.source_loc}"
            )
        if len(leaks_sorted) > max_entries:
            omitted = len(leaks_sorted) - max_entries
            lines.append(f"... ({omitted} additional leaking sites omitted)")
        return "\n".join(lines)
