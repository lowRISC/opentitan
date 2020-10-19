# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional, Tuple

from riscvmodel.types import Trace, TracePC  # type: ignore


from .csr import CSRFile
from .dmem import Dmem
from .ext_regs import OTBNExtRegs
from .flags import FlagReg
from .gpr import GPRs
from .reg import RegFile
from .wsr import WSRFile


class TraceLoopStart(Trace):  # type: ignore
    def __init__(self, iterations: int, bodysize: int):
        self.iterations = iterations
        self.bodysize = bodysize

    def __str__(self) -> str:
        return "Start LOOP, {} iterations, bodysize: {}".format(
            self.iterations, self.bodysize)


class TraceLoopIteration(Trace):  # type: ignore
    def __init__(self, iteration: int, total: int):
        self.iteration = iteration
        self.total = total

    def __str__(self) -> str:
        return "LOOP iteration {}/{}".format(self.iteration, self.total)


class LoopLevel:
    '''An object representing a level in the current loop stack

    start_addr is the first instruction inside the loop (the instruction
    following the loop instruction). insn_count is the number of instructions
    in the loop (and must be positive). restarts is one less than the number of
    iterations, and must be positive.

    '''
    def __init__(self, start_addr: int, insn_count: int, restarts: int):
        assert 0 <= start_addr
        assert 0 < insn_count
        assert 0 < restarts

        self.loop_count = 1 + restarts
        self.restarts_left = restarts
        self.start_addr = start_addr
        self.match_addr = start_addr + 4 * insn_count


class LoopStack:
    '''An object representing the loop stack

    An entry on the loop stack represents a possible back edge: the
    restarts_left counter tracks the number of these back edges. The entry is
    removed when the counter gets to zero.

    '''
    def __init__(self) -> None:
        self.stack = []  # type: List[LoopLevel]
        self.trace = []  # type: List[Trace]

    def start_loop(self,
                   next_addr: int,
                   insn_count: int,
                   loop_count: int) -> Optional[int]:
        '''Start a loop.

        Adds the loop to the stack and returns the next PC if it's not
        straight-line. If the loop count is one, this acts as a NOP (and
        doesn't change the stack). If the loop count is zero, this doesn't
        change the stack but the next PC will be the match address.

        '''
        assert 0 <= next_addr
        assert 0 < insn_count
        assert 0 <= loop_count

        self.trace.append(TraceLoopStart(loop_count, insn_count))

        if loop_count == 0:
            return next_addr + 4 * insn_count

        if loop_count > 1:
            self.stack.append(LoopLevel(next_addr, insn_count, loop_count - 1))

        return None

    def step(self, next_pc: int) -> Optional[int]:
        '''Update loop stack. If we should loop, return new PC'''
        if self.stack:
            top = self.stack[-1]
            if next_pc == top.match_addr:
                assert top.restarts_left > 0
                top.restarts_left -= 1

                if not top.restarts_left:
                    self.stack.pop()

                # 1-based iteration number
                idx = top.loop_count - top.restarts_left
                self.trace.append(TraceLoopIteration(idx, top.loop_count))

                return top.start_addr

        return None

    def changes(self) -> List[Trace]:
        return self.trace

    def commit(self) -> None:
        self.trace = []


class OTBNState:
    def __init__(self) -> None:
        self.gprs = GPRs()
        self.wdrs = RegFile('w', 256, 32)

        self.wsrs = WSRFile()
        self.csrs = CSRFile()

        self.pc = 0
        self.pc_next = None  # type: Optional[int]
        self.dmem = Dmem()

        # Stall cycle support: if an instruction causes one or more stall
        # cycles, we call add_stall_cycles. This increments self._stalls (a
        # non-negative count of the number of stall cycles to wait). On
        # self.commit(), the self.stalled flag gets set if necessary and
        # self._stalls is decremented.
        self.stalled = False
        self._stalls = 0

        self.loop_stack = LoopStack()
        self.ext_regs = OTBNExtRegs()
        self.running = False

    def add_stall_cycles(self, num_cycles: int) -> None:
        '''Add a single stall cycle before the next insn completes'''
        assert num_cycles >= 0
        self._stalls += num_cycles

    def loop_start(self, iterations: int, bodysize: int) -> None:
        next_pc = int(self.pc) + 4
        skip_pc = self.loop_stack.start_loop(next_pc, bodysize, iterations)
        if skip_pc is not None:
            self.pc_next = skip_pc

    def loop_step(self) -> None:
        back_pc = self.loop_stack.step(self.pc + 4)
        if back_pc is not None:
            self.pc_next = back_pc

    def changes(self) -> List[Trace]:
        c = self.gprs.changes()
        if self.pc_next is not None:
            c.append(TracePC(self.pc_next))
        c += self.dmem.changes()
        c += self.loop_stack.changes()
        c += self.ext_regs.changes()
        c += self.wsrs.changes()
        c += self.csrs.flags.changes()
        c += self.wdrs.changes()
        return c

    def commit(self) -> None:
        # Update self.stalled. If the instruction we just ran stalled us then
        # self._stalls will be positive but self.stalled will be false.
        assert self._stalls >= 0
        if self._stalls > 0:
            self.stalled = True
            self._stalls -= 1
        else:
            self.stalled = False

        # If we're stalled, there's nothing more to do: we only commit when we
        # finish our stall cycles.
        if self.stalled:
            return

        self.gprs.commit()
        self.pc = self.pc_next if self.pc_next is not None else self.pc + 4
        self.pc_next = None
        self.dmem.commit()
        self.loop_stack.commit()
        self.ext_regs.commit()
        self.wsrs.commit()
        self.csrs.flags.commit()
        self.wdrs.commit()

    def start(self) -> None:
        '''Set the running flag and the ext_reg busy flag'''
        self.ext_regs.set_bits('STATUS', 1 << 0)
        self.running = True
        # Stall the first cycle immediately after start. The RTL issues its
        # first instruction fetch the cycle after start so only begins executing
        # the cycle following that. This stall ensures the ISS matches that
        # behaviour so stays in sync with the RTL rather than one cycle ahead
        # during simulation.
        self.add_stall_cycles(1)

    def get_quarter_word_unsigned(self, idx: int, qwsel: int) -> int:
        '''Select a 64-bit quarter of a wide register.

        The bits are interpreted as an unsigned value.

        '''
        assert 0 <= idx <= 31
        assert 0 <= qwsel <= 3
        full_val = self.wdrs.get_reg(idx).read_unsigned()
        return (full_val >> (qwsel * 64)) & ((1 << 64) - 1)

    def set_half_word_unsigned(self, idx: int, hwsel: int, value: int) -> None:
        '''Set the low or high 128-bit half of a wide register to value.

        The value should be unsigned.

        '''
        assert 0 <= idx <= 31
        assert 0 <= hwsel <= 1
        assert 0 <= value <= (1 << 128) - 1

        shift = 128 * hwsel
        shifted_input = value << shift
        mask = ((1 << 128) - 1) << shift

        old_val = self.wdrs.get_reg(idx).read_unsigned()
        new_val = (old_val & ~mask) | shifted_input
        self.wdrs.get_reg(idx).write_unsigned(new_val)

    @staticmethod
    def add_with_carry(a: int, b: int, carry_in: int) -> Tuple[int, FlagReg]:
        '''Compute a + b + carry_in and resulting flags.

        Here, a and b are unsigned 256-bit numbers and carry_in is 0 or 1.
        Returns a pair (result, flags) where result is the unsigned 256-bit
        result and flags is the FlagReg that the computation generates.

        '''
        mask256 = (1 << 256) - 1
        assert 0 <= a <= mask256
        assert 0 <= b <= mask256
        assert 0 <= carry_in <= 1

        result = a + b + carry_in
        carryless_result = result & mask256
        C = bool((result >> 256) & 1)

        return (carryless_result, FlagReg.mlz_for_result(C, carryless_result))

    @staticmethod
    def sub_with_borrow(a: int, b: int, borrow_in: int) -> Tuple[int, FlagReg]:
        '''Compute a - b - borrow_in and resulting flags.

        Here, a and b are unsigned 256-bit numbers and borrow_in is 0 or 1.
        Returns a pair (result, flags) where result is the unsigned 256-bit
        result and flags is the FlagReg that the computation generates.

        '''
        mask256 = (1 << 256) - 1
        assert 0 <= a <= mask256
        assert 0 <= b <= mask256
        assert 0 <= borrow_in <= 1

        result = a - b - borrow_in
        carryless_result = result & mask256
        C = bool((result >> 256) & 1)

        return (carryless_result, FlagReg.mlz_for_result(C, carryless_result))

    def set_flags(self, fg: int, flags: FlagReg) -> None:
        '''Update flags for a flag group'''
        self.csrs.flags[fg] = flags

    def set_mlz_flags(self, fg: int, result: int) -> None:
        '''Update M, L, Z flags for a flag group using the given result'''
        self.csrs.flags[fg] = \
            FlagReg.mlz_for_result(self.csrs.flags[fg].C, result)

    def post_insn(self) -> None:
        '''Update state after running an instruction but before commit'''
        self.loop_step()
        self.gprs.post_insn()

    def read_csr(self, idx: int) -> int:
        '''Read the CSR with index idx as an unsigned 32-bit number'''
        return self.csrs.read_unsigned(self.wsrs, idx)

    def write_csr(self, idx: int, value: int) -> None:
        '''Write value (an unsigned 32-bit number) to the CSR with index idx'''
        self.csrs.write_unsigned(self.wsrs, idx, value)
