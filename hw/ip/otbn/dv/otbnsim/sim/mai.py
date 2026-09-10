# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from dataclasses import dataclass
from typing import Any, List, Optional, Tuple

from .csr import CSRFile
from .ispr import DumbISPR
from .mai_ispr import MaiOperation
from .wsr import WSRFile

# The masking accelerator interface (MAI) emulates the behavior of the interface and the actual
# accelerators.

# Enable or disable assertions which check that the inputs and outputs of the accelerators
# meet certain constraints (e.g., being smaller than the modulus).
CHECK_ACCELERATOR_CONSTRAINTS = False

_MASK32 = (1 << 32) - 1


def _mod_smear(mod: int) -> int:
    """Smear all set bits of mod rightward to fill below the MSB."""
    mask = mod & _MASK32
    for i in range(5):
        mask |= mask >> (1 << i)
    return mask & _MASK32


def _urnd_fields(urnd_val: int) -> Tuple[int, int, int, int]:
    """Unpack a 389-bit Bivium keystream word into its named fields.

    [321:0]   rand:     322-bit HPC3 gadget randomness
    [353:322] mask_0:   32-bit remask share 0
    [385:354] mask_1:   32-bit remask share 1
    [388:386] cnt:      3-bit starting counter offset
    """
    rand = urnd_val & ((1 << 322) - 1)
    mask_0 = (urnd_val >> 322) & _MASK32
    mask_1 = (urnd_val >> 354) & _MASK32
    cnt = (urnd_val >> 386) & 0x7
    return rand, mask_0, mask_1, cnt


def hpc3_vec(x0: int, x1: int, y0: int, y1: int, r: int, rp: int,
             w0: int = 0, w1: int = 0) -> Tuple[int, int]:
    """HPC3/HPC3o gadget operating on 32 independent bit-lanes simultaneously.

    EnW=0 (HPC3):  z = x & y
    EnW=1 (HPC3o): z = w ^ (x & y)

    All arguments are 32-bit packed integers.
    r, rp: one fresh random bit per lane.

    Returns (z0, z1) satisfying z0^z1 == (x0^x1)&(y0^y1)^(w0^w1) per bit.
    """
    y_masked_0 = y0 ^ r
    y_masked_1 = y1 ^ r
    inner_0 = (x0 & y_masked_0) ^ w0 ^ rp
    inner_1 = (x1 & y_masked_1) ^ w1 ^ rp
    return (inner_0 ^ (x0 & y_masked_1),
            inner_1 ^ (x1 & y_masked_0))


# Broadcast helpers indexed by (level-1), i.e. index 0 = level 1 = step 1.
# Used to broadcast the remote G/P values to all active positions in a group.
_BCAST_GS: Tuple[int, ...] = (0x55555555, 0x11111111, 0x01010101, 0x00010001, 0x00000001)
_BCAST_FILL: Tuple[int, ...] = (2, 12, 240, 0xFF00, 0xFFFF0000)


# Per-level masks for _advance_level, indexed by (level-1).
# At level lv, each 32-bit word is split into 32/period groups with a lower feedthrough
# half and an upper active half:
#   active_mask         upper-half bits of every group, written with new computed G/P
#   inv_active          lower-half bits, PG copies through unchanged
#   p_mask              active_mask minus group-0's active bits. Group-0 active
#                       PP is dropped because no other group reads group-0 PP as
#                       a remote.
#   feedthrough_pp_mask lower-half bits of groups. Group-0 lower half is
#                       also zeroed so that rem_pp for group-0 stays 0, without
#                       this the initial non-zero pre_p values would persist via
#                       feedthrough and feed a non-zero rem_pp into the P gadget.
def _build_level_masks() -> Tuple[Tuple[int, int, int, int], ...]:
    out = []
    for lv in range(1, 6):
        step = 1 << (lv - 1)
        period = 2 * step
        active_mask = 0
        for k in range(32 // period):
            active_mask |= ((1 << step) - 1) << (period * k + step)
        inv_active = _MASK32 ^ active_mask
        g0_active_mask = ((1 << step) - 1) << step
        p_mask = active_mask ^ g0_active_mask
        group0_all_mask = (1 << period) - 1
        feedthrough_pp_mask = inv_active & (_MASK32 ^ group0_all_mask)
        out.append((active_mask, inv_active, p_mask, feedthrough_pp_mask))
    return tuple(out)


_LEVEL_MASKS: Tuple[Tuple[int, int, int, int], ...] = _build_level_masks()


# SIMD within register bit-splitting helpers (module-level for minimal call overhead).

def _bs_extract(x: int, step: int) -> int:
    """Extract bits at positions 0, step, 2*step, etc. from x and pack them into
    bit positions 0, 1, 2, etc. of the result (bit i of result = bit i*step of x)."""
    if step == 2:
        x &= 0x5555555555555555
        x = (x | (x >> 1)) & 0x3333333333333333
        x = (x | (x >> 2)) & 0x0F0F0F0F0F0F0F0F
        x = (x | (x >> 4)) & 0x00FF00FF00FF00FF
        x = (x | (x >> 8)) & 0x0000FFFF0000FFFF
        x = (x | (x >> 16)) & 0x00000000FFFFFFFF
        return x
    x &= 0x1111111111111111
    x = (x | (x >> 3)) & 0x0303030303030303
    x = (x | (x >> 6)) & 0x000F000F000F000F
    x = (x | (x >> 12)) & 0x000000FF000000FF
    x = (x | (x >> 24)) & 0x000000000000FFFF
    return x


def _bs_scatter(x: int, gap: int) -> int:
    """Spread bits of x into every (gap+1)-th position
    (bit i of x = bit i*(gap+1) of result)."""
    x = (x ^ (x << 16)) & 0x0000FFFF0000FFFF
    x = (x ^ (x << 8)) & 0x00FF00FF00FF00FF
    if gap == 8:
        return x
    x = (x ^ (x << 4)) & 0x0F0F0F0F0F0F0F0F
    if gap == 4:
        return x
    x = (x ^ (x << 2)) & 0x3333333333333333
    if gap == 2:
        return x
    x = (x ^ (x << 1)) & 0x5555555555555555
    return x


# Per-level randomness extraction, one function per level.
# Everything is inlined to minimize function call overhead.

def _ur0(ri: int) -> Tuple[int, int, int, int]:
    """Level 0 (precompute) spread ri across 2 groups:
    ri[63:0] & 0xFFFFFFFFFFFFFFFF -> (r, rp) at 0xFFFFFFFF."""
    n = ri & 0xFFFFFFFFFFFFFFFF
    return _bs_extract(n, 2), _bs_extract(n >> 1, 2), 0, 0


def _ur1(ri: int) -> Tuple[int, int, int, int]:
    """Level 1 (step=1) spread ri across 4 groups:
    ri[125:64] & 0x3FFFFFFFFFFFFFFF -> (r_G, rp_G, r_P, rp_P) at 0xAAAAAAAA."""
    n = (ri >> 64) & 0x3FFFFFFFFFFFFFFF
    lower = n & 3
    upper = n >> 2
    r1 = _bs_extract(upper, 4)
    r2 = _bs_extract(upper >> 1, 4)
    r3 = _bs_extract(upper >> 2, 4)
    r4 = _bs_extract(upper >> 3, 4)
    v1 = (lower & 1) | (r1 << 1)
    v2 = ((lower >> 1) & 1) | (r2 << 1)
    return (_bs_scatter(v1, 1) << 1, _bs_scatter(v2, 1) << 1,
            _bs_scatter(r3, 1) << 3, _bs_scatter(r4, 1) << 3)


def _ur2(ri: int) -> Tuple[int, int, int, int]:
    """Level 2 (step=2) spread ri across 4 groups:
    ri[185:126] & 0xFFFFFFFFFFFFFFF -> (r_G, rp_G, r_P, rp_P) at 0xCCCCCCCC."""
    n = (ri >> 126) & 0xFFFFFFFFFFFFFFF
    lower = n & 0xF
    upper = n >> 4
    p1 = _bs_extract(lower, 2)
    p2 = _bs_extract(lower >> 1, 2)
    r1 = _bs_extract(upper, 4)
    r2 = _bs_extract(upper >> 1, 4)
    r3 = _bs_extract(upper >> 2, 4)
    r4 = _bs_extract(upper >> 3, 4)
    v1 = p1 | (r1 << 2)
    v2 = p2 | (r2 << 2)
    return (_bs_scatter(v1, 2) << 2, _bs_scatter(v2, 2) << 2,
            _bs_scatter(r3, 2) << 6, _bs_scatter(r4, 2) << 6)


def _ur3(ri: int) -> Tuple[int, int, int, int]:
    """Level 3 (step=4) spread ri across 4 groups:
    ri[241:186] & 0xFFFFFFFFFFFFFF -> (r_G, rp_G, r_P, rp_P) at 0xF0F0F0F0."""
    n = (ri >> 186) & 0xFFFFFFFFFFFFFF
    lower = n & 0xFF
    upper = n >> 8
    p1 = _bs_extract(lower, 2)
    p2 = _bs_extract(lower >> 1, 2)
    r1 = _bs_extract(upper, 4)
    r2 = _bs_extract(upper >> 1, 4)
    r3 = _bs_extract(upper >> 2, 4)
    r4 = _bs_extract(upper >> 3, 4)
    v1 = p1 | (r1 << 4)
    v2 = p2 | (r2 << 4)
    return (_bs_scatter(v1, 4) << 4, _bs_scatter(v2, 4) << 4,
            _bs_scatter(r3, 4) << 12, _bs_scatter(r4, 4) << 12)


def _ur4(ri: int) -> Tuple[int, int, int, int]:
    """Level 4 (step=8) spread ri across 4 groups:
    ri[289:242] & 0xFFFFFFFFFFFF -> (r_G, rp_G, r_P, rp_P) at 0xFF00FF00."""
    n = (ri >> 242) & 0xFFFFFFFFFFFF
    lower = n & 0xFFFF
    upper = n >> 16
    p1 = _bs_extract(lower, 2)
    p2 = _bs_extract(lower >> 1, 2)
    r1 = _bs_extract(upper, 4)
    r2 = _bs_extract(upper >> 1, 4)
    r3 = _bs_extract(upper >> 2, 4)
    r4 = _bs_extract(upper >> 3, 4)
    v1 = p1 | (r1 << 8)
    v2 = p2 | (r2 << 8)
    return (_bs_scatter(v1, 8) << 8, _bs_scatter(v2, 8) << 8,
            _bs_scatter(r3, 8) << 24, _bs_scatter(r4, 8) << 24)


def _ur5(ri: int) -> Tuple[int, int, int, int]:
    """Level 5 (step=16) spread ri across 2 groups:
    ri[321:290] & 0xFFFFFFFF -> (r_G, rp_G) at 0xFFFF0000."""
    n = (ri >> 290) & 0xFFFFFFFF
    return _bs_extract(n, 2) << 16, _bs_extract(n >> 1, 2) << 16, 0, 0


_UNPACK_RAND_FNS: Tuple[Any, ...] = (_ur0, _ur1, _ur2, _ur3, _ur4, _ur5)


@dataclass
class _SecAddStage:
    # pg / pp / pre_p: 32-bit packed shares (s0, s1).
    pg: Tuple[int, int]
    pp: Tuple[int, int]
    # pre_p carries the initial XOR propagate (inp1 ^ inp2) through all stages unchanged.
    pre_p: Tuple[int, int]
    # How many prefix-tree levels have been applied (0 = pre-compute only).
    level: int
    # rand from the cycle when this stage was last advanced (or created).
    # Used by the NEXT advance: level-L gadgets consume the rand that was
    # current when level L-1 ran (one cycle earlier).
    rand: int = 0


class SecureAdder:
    """Cycle-accurate model of the secure adder.

    Masked Sklansky parallel-prefix adder, Width=32, Stages=5, Latency=6 cycles.
    Inputs are first-order Boolean sharings (share0, share1) of 32-bit values.
    Output is a (Width+1)-bit sharing that includes the carry-out in bit [32].
    rand (322 bits) must be fresh every cycle the pipeline is active.

    Calling convention each clock cycle:
        result = adder.peek()         # read output (must come first)
        adder.step(rand, stall)       # shift pipeline
        adder.push(inp1, inp2, rand)  # inject new input (same rand)
    """

    WIDTH = 32
    STAGES = 5  # log2(32)
    LATENCY = STAGES + 1
    RAND_WIDTH = 2 * (STAGES * WIDTH + 1)  # 322

    def __init__(self) -> None:
        self._stages: List[Optional[_SecAddStage]] = [None] * self.LATENCY
        self._num_in_flight: int = 0

    def push(self, inp1: Tuple[int, int], inp2: Tuple[int, int],
             rand: int) -> None:
        """Apply level-0 pre-compute and place result in pipeline stage 0.

        Must be called after step() within the same clock cycle.
        rand bits [63:0] are consumed (2 bits per HPC3 gadget, 32 gadgets).
        """
        self._stages[0] = self._precompute(inp1, inp2, rand)
        self._num_in_flight += 1

    def step(self, rand: int, stall: bool = False) -> None:
        """Advance the pipeline by one stage unless stalled.

        Iterates from the tail so each entry is read before being overwritten.
        Each in-flight entry advances one prefix-tree level using the rand
        stored in it (from the previous cycle). After advancing, the stored
        rand is updated to the current rand for the next level's advance.
        Clears stage 0 so that push() can inject a new element this cycle.
        """
        if stall:
            return
        if self._num_in_flight == 0:
            return  # nothing to advance
        tail_was_set = self._stages[self.LATENCY - 1] is not None
        for si in range(self.LATENCY - 1, 0, -1):
            src = self._stages[si - 1]
            if src is not None:
                new_stage = self._advance_level(src, src.rand)
                new_stage.rand = rand
                self._stages[si] = new_stage
            else:
                self._stages[si] = None
        self._stages[0] = None
        if tail_was_set:
            self._num_in_flight -= 1

    def peek(self) -> Optional[Tuple[int, int]]:
        """Return output shares (33-bit each) if a result is ready, else None."""
        stage = self._stages[-1]
        return self._final_sum(stage) if stage is not None else None

    def _precompute(self, inp1: Tuple[int, int], inp2: Tuple[int, int],
                    rand: int) -> _SecAddStage:
        """Level-0: pg = inp1 AND inp2 via 32 parallel HPC3 gadgets, pp = inp1 XOR inp2."""
        s0_a, s1_a = inp1
        s0_b, s1_b = inp2
        r, rp, _, _ = _ur0(rand)
        pg_s0, pg_s1 = hpc3_vec(s0_a, s1_a, s0_b, s1_b, r, rp)
        pre_p_s0 = (s0_a ^ s0_b) & _MASK32
        pre_p_s1 = (s1_a ^ s1_b) & _MASK32
        pre_p = (pre_p_s0, pre_p_s1)
        return _SecAddStage(
            pg=(pg_s0 & _MASK32, pg_s1 & _MASK32),
            pp=pre_p,
            pre_p=pre_p,
            level=0,
            rand=rand,
        )

    def _advance_level(self, stage: _SecAddStage, rand: int) -> _SecAddStage:
        """Apply the next Sklansky prefix-tree level using vectorized HPC3 gadgets.

        All 32 bit-lanes are processed simultaneously. Active bits (upper half of
        each 2*step-bit group) receive computed G/P values, feedthrough bits
        (lower half) are copied. Group-0 pp is always 0.
        """
        level = stage.level + 1
        lv_idx = level - 1
        step = 1 << lv_idx

        pg_s0, pg_s1 = stage.pg
        pp_s0, pp_s1 = stage.pp

        # Broadcast each group's remote (position step-1 within the group) to all
        # active positions in that group (step..2*step-1). Uses precomputed
        # group_sel (_BCAST_GS) and fill multiplier (_BCAST_FILL).
        gs = _BCAST_GS[lv_idx]
        fill = _BCAST_FILL[lv_idx]
        shift = step - 1
        rem_pg_s0 = ((pg_s0 >> shift) & gs) * fill & _MASK32
        rem_pg_s1 = ((pg_s1 >> shift) & gs) * fill & _MASK32
        rem_pp_s0 = ((pp_s0 >> shift) & gs) * fill & _MASK32
        rem_pp_s1 = ((pp_s1 >> shift) & gs) * fill & _MASK32

        r_G, rp_G, r_P, rp_P = _UNPACK_RAND_FNS[level](rand)

        active_mask, inv_active, p_mask, feedthrough_pp_mask = _LEVEL_MASKS[lv_idx]

        # G gadgets (HPC3o): new_pg[bi] = pg[bi] ^ (pp[bi] & pg[remote])
        g_s0, g_s1 = hpc3_vec(rem_pg_s0, rem_pg_s1, pp_s0, pp_s1, r_G, rp_G, pg_s0, pg_s1)

        # P gadgets (HPC3): new_pp[bi] = pp[remote] & pp[bi] (non-group-0 active only)
        p_s0, p_s1 = hpc3_vec(rem_pp_s0, rem_pp_s1, pp_s0, pp_s1, r_P, rp_P)

        # Merge values into the next level values:
        # active -> values that were just computed,
        # feedthrough -> copy from previous level,
        # group-0 pp bits -> 0.
        new_pg_s0 = (pg_s0 & inv_active) | (g_s0 & active_mask)
        new_pg_s1 = (pg_s1 & inv_active) | (g_s1 & active_mask)
        new_pp_s0 = (pp_s0 & feedthrough_pp_mask) | (p_s0 & p_mask)
        new_pp_s1 = (pp_s1 & feedthrough_pp_mask) | (p_s1 & p_mask)

        return _SecAddStage(
            pg=(new_pg_s0 & _MASK32, new_pg_s1 & _MASK32),
            pp=(new_pp_s0 & _MASK32, new_pp_s1 & _MASK32),
            pre_p=stage.pre_p,
            level=level,
            rand=0,
        )

    def _final_sum(self, stage: _SecAddStage) -> Tuple[int, int]:
        """Combinational sum: result[bi] = pre_p[bi] ^ pg[bi-1], carry-out at bit 32."""
        pg_s0, pg_s1 = stage.pg
        pre_p_s0, pre_p_s1 = stage.pre_p
        # (pg << 1) places pg[bi-1] at position bi, bit 0 gets 0 (no carry-in).
        res_s0 = (pre_p_s0 ^ ((pg_s0 << 1) & _MASK32)) | ((pg_s0 >> 31) << 32)
        res_s1 = (pre_p_s1 ^ ((pg_s1 << 1) & _MASK32)) | ((pg_s1 >> 31) << 32)
        return res_s0, res_s1


class _MaskingAccelerator:
    """Pipeline-accurate model of the masking accelerator using SecureAdder.

    Implements all four modes selected by `mode`:
      SecAdd:       single pass, no modular reduction, latency 7.
      SecAddMod:    two-pass modular adder,            latency 15 / 22.
      A2B:          arithmetic-to-boolean conversion,  latency 15 / 22.
      B2A:          boolean-to-arithmetic conversion,  latency 16 / 23.

    Calling convention (from MaskingAcceleratorInterface each cycle):
        peek():                       read oldest result
        step(rand, mask_0, mask_1):   advance pipeline
        push(s00,s01,s10,s11,
             rand, mask_0, mask_1):   register one pass-1 input
    """

    VEC_SIZE = 8  # number of 32-bit lanes per batch

    def __init__(self, mod_wsr: DumbISPR, mode: MaiOperation) -> None:
        self._mod_wsr = mod_wsr
        self._mode = mode
        self._adder = SecureAdder()
        # Completed (s0_32, s1_32) results ready for writeback. Not reset between
        # batches so that writeback can drain while the next batch is already starting.
        self._output_queue: List[Tuple[int, int]] = []
        self._reset_batch()

    def _reset_batch(self) -> None:
        # Input register: (inp1, inp2) waiting to be pushed to the adder.
        self._inp_reg: Optional[Tuple[Tuple[int, int], Tuple[int, int]]] = None
        # Pass-1 result FIFO: 33-bit share pairs buffered for pass-2.
        self._pass1_buf: List[Tuple[int, int]] = []
        # B2A only: mask_mod values pushed alongside each input element.
        self._mask_fifo: List[int] = []
        # Expected unmasked result per element.
        self._check_fifo: List[Optional[int]] = []
        # How many pass-1 inputs have been pushed from the register into the adder.
        self._pass1_adder_count: int = 0
        # How many pass-2 inputs have been pushed to the adder.
        self._pass2_fed: int = 0
        # True once all pass-1 inputs are done and pass-2 is self-feeding.
        self._in_pass2: bool = False
        # Running total of adder outputs collected this batch.
        self._adder_outputs: int = 0

    def push(self, in0_s0: int, in0_s1: int, in1_s0: int, in1_s1: int,
             mask_0: int, mask_1: int) -> None:
        """Encode one pass-1 element and store it in the input register."""
        mod = self._modulus()
        inp1, inp2 = self._encode(in0_s0, in0_s1, in1_s0, in1_s1,
                                  mask_0, mask_1, mod)
        self._inp_reg = (inp1, inp2)
        if self._mode == MaiOperation.B2A:
            self._mask_fifo.append(mask_0 & _mod_smear(mod))
        self._check_fifo.append(
            self._calc_expected_unmasked(in0_s0, in0_s1, in1_s0, in1_s1, mod))

    def step(self, rand: int, stall: bool = False) -> None:
        """Advance the pipeline one cycle."""
        if stall:
            return

        # 1. Collect adder output before advancing.
        raw = self._adder.peek()
        if raw is not None:
            self._adder_outputs += 1
            if self._enable_mod() and self._adder_outputs <= self.VEC_SIZE:
                self._pass1_buf.append(raw)  # pass-1 -> buffer
            else:
                self._emit_result(raw)  # pass-2 or direct -> output

            # Once the last expected output is collected, reset input-tracking so the
            # next batch starts clean. _output_queue is left intact, writeback may
            # still be draining it.
            total_outputs = 2 * self.VEC_SIZE if self._enable_mod() else self.VEC_SIZE
            if self._adder_outputs == total_outputs:
                if self._mask_fifo:
                    raise RuntimeError("mask_fifo not empty at batch end")
                if self._check_fifo:
                    raise RuntimeError("check_fifo not empty at batch end")
                self._reset_batch()

        # 2. Advance adder pipeline.
        self._adder.step(rand)

        # 3. Push input register -> adder (mutually exclusive with pass-2 feed).
        pushed_p1 = False
        if self._inp_reg is not None:
            inp1, inp2 = self._inp_reg
            self._adder.push(inp1, inp2, rand)
            self._inp_reg = None
            self._pass1_adder_count += 1
            pushed_p1 = True

        # 4. Enter pass-2 one cycle after the last pass-1 push.
        if (self._enable_mod()
                and self._pass1_adder_count == self.VEC_SIZE
                and not self._in_pass2
                and not pushed_p1):
            self._in_pass2 = True

        # 5. Self-feed pass-2 inputs (one per cycle, not on same cycle as a p1 push).
        if (self._in_pass2
                and not pushed_p1
                and self._pass2_fed < self.VEC_SIZE
                and self._pass1_buf):
            p1 = self._pass1_buf.pop(0)
            inp1_p2, inp2_p2 = self._pass2_inputs(p1)
            self._adder.push(inp1_p2, inp2_p2, rand)
            self._pass2_fed += 1

    def peek(self) -> Optional[Tuple[int, int]]:
        """Return the oldest completed (s0, s1) pair, or None."""
        if self._output_queue:
            return self._output_queue.pop(0)
        return None

    def is_busy(self) -> bool:
        if self._inp_reg is not None:
            return True
        if self._adder._num_in_flight > 0:
            return True
        return bool(self._pass1_buf or self._output_queue)

    def _modulus(self) -> int:
        return self._mod_wsr.read_unsigned() & _MASK32

    def _enable_mod(self) -> bool:
        return self._mode != MaiOperation.SECADD

    def _encode(self, in0_s0: int, in0_s1: int, in1_s0: int, in1_s1: int,
                mask_0: int, mask_1: int,
                mod: int) -> Tuple[Tuple[int, int], Tuple[int, int]]:
        """Compute (inp1_share, inp2_share) for the adder per mode."""
        mod_neg = (-mod) & _MASK32
        if self._mode == MaiOperation.A2B:
            # inp1 = (a0 ^ r0,             r0)
            # inp2 = ((a1 + mod_neg) ^ r1, r1)
            inp1 = (in0_s0 ^ mask_0, mask_0)
            inp2 = (((in0_s1 + mod_neg) & _MASK32) ^ mask_1, mask_1)
        elif self._mode == MaiOperation.B2A:
            # inp1 = in0_i (Boolean sharing of a)
            # inp2 = ((-mask_mod) ^ r1, r1)
            mask_mod = mask_0 & _mod_smear(mod)
            inp1 = (in0_s0, in0_s1)
            inp2 = (((-mask_mod) & _MASK32) ^ mask_1, mask_1)
        else:
            # SecAdd / SecAddMod: pass through directly.
            inp1 = (in0_s0, in0_s1)
            inp2 = (in1_s0, in1_s1)
        return inp1, inp2

    def _calc_expected_unmasked(self, in0_s0: int, in0_s1: int, in1_s0: int, in1_s1: int,
                                mod: int) -> Optional[int]:
        """Compute the expected unmasked result for one element, per the MAI spec.

        Returns None if the modulus makes the operation's result undefined (mod == 0
        for the modes that use the modulus).

        Input form and target value per mode:
          SECADD:    in0, in1 are Boolean shares of a, b. Computes (a + b) mod 2^32.
          SECADDMOD: in0, in1 are Boolean shares of a, b, pre-encoded with -mod baked
                     in, i.e. a + b = true_a + true_b - mod. Computes (true_a + true_b)
                     mod mod, i.e. (a + b + mod) mod mod.
          A2B:       in0 is an arithmetic share of a (in1 unused). Computes a mod mod.
          B2A:       in0 is a Boolean share of a (in1 unused). Computes a mod mod.
        """
        a = in0_s0 ^ in0_s1
        b = in1_s0 ^ in1_s1
        if self._mode == MaiOperation.SECADD:
            return (a + b) & _MASK32
        if mod == 0:
            return None
        if self._mode == MaiOperation.SECADDMOD:
            true_sum = a + b
            if true_sum >> 32:
                return true_sum & _MASK32
            return (true_sum + mod) & _MASK32
        if self._mode == MaiOperation.A2B:
            return (in0_s0 + in0_s1) % mod
        if self._mode == MaiOperation.B2A:
            return a % mod
        raise ValueError(f'Unhandled MAI mode: {self._mode}')

    def _check_unmasked_result(self, result: Tuple[int, int]) -> None:
        """Pop the expected value queued at push time and check it against `result`."""
        expected = self._check_fifo.pop(0)
        if expected is None:
            # _calc_expected_unmasked() returns None when mod == 0 makes the result
            # undefined for this mode. There's nothing to check in that case.
            return
        s0, s1 = result
        if self._mode == MaiOperation.B2A:
            mod = self._modulus()
            actual = (s0 + s1) % mod
        else:
            actual = (s0 & _MASK32) ^ (s1 & _MASK32)
        if actual != expected:
            raise ValueError(
                f"MAI {self._mode!r} unmasked output mismatch: "
                f"got {actual:#x}, expected {expected:#x}")

    def _pass2_inputs(
            self, p1: Tuple[int, int]
    ) -> Tuple[Tuple[int, int], Tuple[int, int]]:
        """Compute pass-2 adder inputs from a 33-bit pass-1 result.

        carry0=1 means share 0 overflowed: no correction needed.
        carry1=1 means share 1 overflowed: add modulus to share 1 to correct.
        """
        s0, s1 = p1
        mod = self._modulus()
        carry0 = (s0 >> 32) & 1
        carry1 = (s1 >> 32) & 1
        inp1 = (s0 & _MASK32, s1 & _MASK32)
        inp2 = (0 if carry0 else mod, mod if carry1 else 0)
        return inp1, inp2

    def _emit_result(self, raw: Tuple[int, int]) -> None:
        """Finalise a pass-2 (or direct) output and enqueue it."""
        s0, s1 = raw
        if self._mode == MaiOperation.B2A:
            # result[0] = mask_mod (popped from FIFO)
            # result[1] = XOR of the two masked shares, narrowed by mod_smear
            mask_mod = self._mask_fifo.pop(0)
            mod = self._modulus()
            diff = (s0 & _MASK32) ^ (s1 & _MASK32)
            result = (mask_mod, diff & _mod_smear(mod))
        else:
            result = (s0 & _MASK32, s1 & _MASK32)
        self._check_unmasked_result(result)
        self._output_queue.append(result)


class MaskingAcceleratorInterface:
    def __init__(self, csrs: CSRFile, wsrs: WSRFile) -> None:
        # _cnt: element-index offset for dispatch. Loaded from URND.cnt during
        # the secure wipe and after each 8-element dispatch. Initialised to 0;
        # the first real value comes from on_sec_wipe_zero_step() before EXEC.
        self._cnt = 0
        # _wb_cnt: element-index offset for writeback. Matches _cnt at operation
        # start and is updated when writeback completes, ensuring dispatch and
        # writeback for the same operation use the same counter value.
        self._wb_cnt = 0
        self.on_start(csrs, wsrs)

    def on_start(self, csrs: CSRFile, wsrs: WSRFile) -> None:
        '''Reset the MAI for the start of an OTBN execution'''
        self.csrs = csrs
        self.wsrs = wsrs

        # Single accelerator object shared handles all modes. Its _mode is updated
        # to the current MAI_CTRL operation when a new operation starts (start bit
        # fires).
        self._accel = _MaskingAccelerator(self.wsrs.MOD, MaiOperation.A2B)

        # Dispatch related variables
        # The dispatch logic is responsible for pushing inputs into the accelerator.
        self._dispatch_idx = 0
        self.is_dispatching = False

        # Writeback related variables
        # The writeback logic is responsible for receiving results from the accelerator into the
        # output WSRs.
        self._writeback_idx = 0

        # NOTE: _cnt and _wb_cnt are intentionally not reset here. They are
        # captured during the preceding secure wipe via on_sec_wipe_zero_step()
        # and must survive the on_start() call so that the first MAI operation
        # uses the correct element ordering.

        # Deferred busy clear: set True when the last output is written, cleared
        # in the following step() to model the one-cycle register-update latency.
        self._pending_busy_clear = False

    def on_sec_wipe_zero_step(self) -> None:
        '''Called during the secure-wipe zero step to latch the initial counter.

        The URND Bivium has been stepped up to this cycle in _step_wiping(). The
        keystream for this cycle is already in wsrs.URND._next_value.
        '''
        _, _, _, cnt = _urnd_fields(self.wsrs.URND.pending_value())
        self._cnt = cnt
        self._wb_cnt = cnt

    def step(self) -> None:
        '''Advance the MAI simulation by one cycle.

        This is expected to be called before the current instruction executes / steps.'''
        # The step logic sets bits and values in the cycle where the instruction can read it which
        # is different compared to how CRSs are updated when an instruction writes to them.
        # Setting values "immediately" simplifies the status flag handling because the abort case
        # must not be considered.

        rand, mask_0, mask_1, _ = _urnd_fields(self.wsrs.URND._value)

        # Apply deferred busy clear from the previous cycle.
        if self._pending_busy_clear:
            self._pending_busy_clear = False
            self.csrs.MAI_STATUS.update_busy_bit(False)

        # Idle fast-path: if nothing is active and no new start is pending,
        # skip all pipeline/writeback work.
        if (not self.is_dispatching
                and not self.csrs.MAI_STATUS.is_busy()
                and not self.csrs.MAI_CTRL.is_start_bit_set()):
            return

        # Writeback logic:
        # Get the newest result and write it into the output WSRs. This is done before
        # advancing the pipeline to model the fact that the result is available at
        # the start of the cycle.
        results = self._accel.peek()
        if results is not None:
            res_s0, res_s1 = results
            wb_idx = (self._wb_cnt + self._writeback_idx) % _MaskingAccelerator.VEC_SIZE
            # Write to the output WSRs
            self.wsrs.MAI_RES_S0.set_32bit_unsigned(res_s0, wb_idx)
            self.wsrs.MAI_RES_S1.set_32bit_unsigned(res_s1, wb_idx)
            self._writeback_idx += 1

        # Detect if we finished writing back. Defer the busy clear by one cycle
        # to model the one-cycle register-update latency. Update _wb_cnt from
        # _cnt so the next operation's writeback uses the cnt latched at the
        # end of this operation's dispatch.
        if self._writeback_idx >= _MaskingAccelerator.VEC_SIZE:
            self._writeback_idx = 0
            self._wb_cnt = self._cnt
            self._pending_busy_clear = True

        # Advance the accelerator pipeline
        self._accel.step(rand)

        # Start a new operation if start bit was set in last cycle
        if self.csrs.MAI_CTRL.is_start_bit_set():
            # The start bit may only be set if the MAI is not busy. If this assertion fails, the
            # check when writing to the MAI_CTRL CSR is wrong.
            assert not self.csrs.MAI_STATUS.is_busy()
            self._accel._mode = self.csrs.MAI_CTRL.current_operation()
            # _cnt was already captured in the wipe phase via on_sec_wipe_zero_step().
            # Begin pushing inputs in the dispatch logic.
            self.is_dispatching = True
            # Immediately set the busy bit so the current instruction is not allowed to start the
            # next execution.
            self.csrs.MAI_STATUS.update_busy_bit(True)
            # Immediately reset the input-ready bit such that any configuration change check does
            # not allow changing the operation type.
            self.csrs.MAI_STATUS.update_input_ready_bit(False)
            # Immediately reset the start bit such that it always reads zero.
            self.csrs.MAI_CTRL.update_start_bit(False)

        if self.is_dispatching:
            # B2A rejection sampling.
            # Stall this cycle without advancing _dispatch_idx so the next cycle's URND
            # provides a fresh mask_mod candidate.
            b2a_stall = False
            if self.csrs.MAI_CTRL.current_operation() == MaiOperation.B2A:
                mod = self.wsrs.MOD.read_unsigned() & _MASK32
                if mod > 0 and (mask_0 & _mod_smear(mod)) >= mod:
                    b2a_stall = True
            if not b2a_stall:
                idx = (self._cnt + self._dispatch_idx) % _MaskingAccelerator.VEC_SIZE
                in0_s0 = self.wsrs.MAI_IN0_S0.read_32bit_unsigned(idx)
                in0_s1 = self.wsrs.MAI_IN0_S1.read_32bit_unsigned(idx)
                in1_s0 = self.wsrs.MAI_IN1_S0.read_32bit_unsigned(idx)
                in1_s1 = self.wsrs.MAI_IN1_S1.read_32bit_unsigned(idx)
                self._accel.push(in0_s0, in0_s1, in1_s0, in1_s1, mask_0, mask_1)
                self._dispatch_idx += 1

        # Detect if we have finished dispatching
        if self._dispatch_idx >= _MaskingAccelerator.VEC_SIZE:
            self._dispatch_idx = 0
            self.is_dispatching = False
            # Latch the random dispatch index for the next execution.
            _, _, _, new_cnt = _urnd_fields(self.wsrs.URND._value)
            self._cnt = new_cnt
            # Immediately set the input-ready bit as the input WSRs can be overwritten in
            # this cycle.
            self.csrs.MAI_STATUS.update_input_ready_bit(True)

    def is_busy(self) -> bool:
        '''Returns whether the MAI is currently busy processing an operation.'''
        return self.csrs.MAI_STATUS.is_busy()

    def is_input_ready(self) -> bool:
        '''Returns whether the MAI is ready to accept new inputs.'''
        return self.csrs.MAI_STATUS.is_input_ready()

    def ready_for_inputs(self) -> bool:
        return self.is_input_ready()

    def ready_to_start(self) -> bool:
        return not self.is_busy()

    def is_valid_ctrl_change(self, value: int) -> bool:
        '''Return whether writing value to the MAI_CTRL CSR is currently allowed.'''
        # Bits [31:6] are reserved; any non-zero bits there are a software error.
        if self.csrs.MAI_CTRL.has_reserved_bits(value):
            return False

        # Changing the operation while the MAI is busy is a software error.
        if self.is_busy() and self.csrs.MAI_CTRL.would_change_raw_op(value):
            return False

        # When start fires, the MAI must not be busy and the next operation value must be
        # a valid choice.
        if self.csrs.MAI_CTRL.would_set_start_bit(value):
            if not self.ready_to_start():
                return False
            if not self.csrs.MAI_CTRL.is_raw_op_valid(value):
                return False

        return True
