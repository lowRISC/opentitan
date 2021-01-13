# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional, Tuple

from shared.mem_layout import get_memory_layout

from .alert import BadAddrError, LoopError
from .csr import CSRFile
from .dmem import Dmem
from .ext_regs import OTBNExtRegs
from .flags import FlagReg
from .gpr import GPRs
from .reg import RegFile
from .trace import Trace, TracePC
from .wsr import WSRFile


class TraceLoopStart(Trace):
    def __init__(self, iterations: int, bodysize: int):
        self.iterations = iterations
        self.bodysize = bodysize

    def trace(self) -> str:
        return "Start LOOP, {} iterations, bodysize: {}".format(
            self.iterations, self.bodysize)


class TraceLoopIteration(Trace):
    def __init__(self, iteration: int, total: int):
        self.iteration = iteration
        self.total = total

    def trace(self) -> str:
        return "LOOP iteration {}/{}".format(self.iteration, self.total)


class LoopLevel:
    '''An object representing a level in the current loop stack

    start_addr is the first instruction inside the loop (the instruction
    following the loop instruction). insn_count is the number of instructions
    in the loop (and must be positive). restarts is one less than the number of
    iterations, and must be non-negative.

    '''
    def __init__(self, start_addr: int, insn_count: int, restarts: int):
        assert 0 <= start_addr
        assert 0 < insn_count
        assert 0 <= restarts

        self.loop_count = 1 + restarts
        self.restarts_left = restarts
        self.start_addr = start_addr
        self.match_addr = start_addr + 4 * insn_count


class LoopStack:
    '''An object representing the loop stack

    The loop stack holds up to 8 LoopLevel objects, corresponding to nested
    loops.

    '''
    stack_depth = 8

    def __init__(self) -> None:
        self.stack = []  # type: List[LoopLevel]
        self.trace = []  # type: List[Trace]

    def start_loop(self,
                   next_addr: int,
                   loop_count: int,
                   insn_count: int) -> None:
        '''Start a loop.

        next_addr is the address of the first instruction in the loop body.
        loop_count must be positive and is the number of times to execute the
        loop. insn_count must be positive and is the number of instructions in
        the loop body.

        '''
        assert 0 <= next_addr
        assert 0 < insn_count
        assert 0 < loop_count

        if len(self.stack) == LoopStack.stack_depth:
            raise LoopError('loop stack overflow')

        self.trace.append(TraceLoopStart(loop_count, insn_count))
        self.stack.append(LoopLevel(next_addr, insn_count, loop_count - 1))

    def check_insn(self, pc: int, insn_affects_control: bool) -> None:
        '''Check for branch instructions at the end of a loop body'''
        if self.stack:
            top = self.stack[-1]
            if pc + 4 == top.match_addr:
                # We're about to execute the last instruction in the loop body.
                # Make sure that it isn't a jump, branch or another loop
                # instruction.
                if insn_affects_control:
                    raise LoopError('control instruction at end of loop')

    def step(self, next_pc: int) -> Optional[int]:
        '''Update loop stack. If we should loop, return new PC'''
        if self.stack:
            top = self.stack[-1]

            if next_pc == top.match_addr:
                assert top.restarts_left >= 0

                # 1-based iteration number
                loop_idx = top.loop_count - top.restarts_left

                if not top.restarts_left:
                    self.stack.pop()
                    ret_val = None
                else:
                    top.restarts_left -= 1
                    ret_val = top.start_addr

                self.trace.append(TraceLoopIteration(loop_idx, top.loop_count))
                return ret_val

        return None

    def changes(self) -> List[Trace]:
        return self.trace

    def commit(self) -> None:
        self.trace = []

    def abort(self) -> None:
        self.trace = []


class OTBNState:
    def __init__(self) -> None:
        self.gprs = GPRs()
        self.wdrs = RegFile('w', 256, 32)

        self.wsrs = WSRFile()
        self.csrs = CSRFile()

        self.pc = 0
        self.pc_next = None  # type: Optional[int]

        _, imem_size = get_memory_layout()['IMEM']
        self.imem_size = imem_size

        self.dmem = Dmem()

        # Stall cycle support: if an instruction causes one or more stall
        # cycles, we call add_stall_cycles. This increments self._stalls (a
        # non-negative count of the number of stall cycles to wait). On
        # self.commit(), the self.stalled flag gets set if necessary and
        # self._stalls is decremented.
        #
        # As a special case, we stall for one cycle before fetching the first
        # instruction (to match the behaviour of the RTL). This is modelled by
        # setting self._start_stall and self.stalled.
        self.stalled = False
        self._stalls = 0
        self._start_stall = False

        self.loop_stack = LoopStack()
        self.ext_regs = OTBNExtRegs()
        self.running = False

    def add_stall_cycles(self, num_cycles: int) -> None:
        '''Add stall cycles before the next insn completes'''
        assert num_cycles >= 0
        self._stalls += num_cycles

    def loop_start(self, iterations: int, bodysize: int) -> None:
        next_pc = int(self.pc) + 4
        self.loop_stack.start_loop(next_pc, iterations, bodysize)

    def loop_step(self) -> None:
        back_pc = self.loop_stack.step(self.pc + 4)
        if back_pc is not None:
            self.pc_next = back_pc

    def changes(self) -> List[Trace]:
        c = []  # type: List[Trace]
        c += self.gprs.changes()
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

        # If self._start_stall, this is the end of the stall cycle at the start
        # of a run. We've just cleared self.stalled. Clear self._start_stall
        # and commit self.ext_regs (so the start flag becomes visible) but then
        # return rather than advancing the PC, ensuring we don't skip the first
        # instruction.
        if self._start_stall:
            self._start_stall = False
            self.ext_regs.commit()
            return

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

    def abort(self) -> None:
        '''Abort any pending state changes'''
        # This should only be called when an instruction's execution goes
        # wrong. If self._stalls is positive, the bad execution caused those
        # stalls, so we should just zero them.
        self._stalls = 0

        self.gprs.abort()
        self.pc_next = None
        self.dmem.abort()
        self.loop_stack.abort()
        self.ext_regs.abort()
        self.wsrs.abort()
        self.csrs.flags.abort()
        self.wdrs.abort()

    def start(self) -> None:
        '''Set the running flag and the ext_reg busy flag'''
        self.ext_regs.set_bits('STATUS', 1 << 0)
        self.running = True
        self._start_stall = True
        self.stalled = True

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

    def pre_insn(self, insn_affects_control: bool) -> None:
        '''Run before running an instruction'''
        self.loop_stack.check_insn(self.pc, insn_affects_control)

    def check_jump_dest(self) -> None:
        '''Check whether self.pc_next is a valid jump/branch target

        If not, raises a BadAddrError.

        '''
        if self.pc_next is None:
            return

        # The PC should always be non-negative (it's an error in the simulator
        # if that's come unstuck)
        assert 0 <= self.pc_next

        # Check the new PC is word-aligned
        if self.pc_next & 3:
            raise BadAddrError('pc', self.pc_next,
                               'address is not 4-byte aligned')

        # Check the new PC lies in instruction memory
        if self.pc_next >= self.imem_size:
            raise BadAddrError('pc', self.pc_next,
                               'address lies above the top of imem')

    def post_insn(self) -> None:
        '''Update state after running an instruction but before commit'''
        self.check_jump_dest()
        self.loop_step()

    def read_csr(self, idx: int) -> int:
        '''Read the CSR with index idx as an unsigned 32-bit number'''
        return self.csrs.read_unsigned(self.wsrs, idx)

    def write_csr(self, idx: int, value: int) -> None:
        '''Write value (an unsigned 32-bit number) to the CSR with index idx'''
        self.csrs.write_unsigned(self.wsrs, idx, value)

    def peek_call_stack(self) -> List[int]:
        '''Return the current call stack, bottom-first'''
        return self.gprs.peek_call_stack()

    def stop(self, err_code: Optional[int]) -> None:
        '''Set flags to stop the processor.

        If err_code is not None, it is the value to write to the ERR_BITS
        register.

        '''
        # INTR_STATE is the interrupt state register. Bit 0 (which is being
        # set) is the 'done' flag.
        self.ext_regs.set_bits('INTR_STATE', 1 << 0)
        # STATUS is a status register. Bit 0 (being cleared) is the 'busy' flag
        self.ext_regs.clear_bits('STATUS', 1 << 0)

        if err_code is not None:
            self.ext_regs.write('ERR_BITS', err_code, True)

        self.running = False
