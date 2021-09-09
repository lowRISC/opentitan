# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List, Optional

from shared.mem_layout import get_memory_layout

from .csr import CSRFile
from .dmem import Dmem
from .constants import ErrBits, Status
from .ext_regs import OTBNExtRegs
from .flags import FlagReg
from .gpr import GPRs
from .loop import LoopStack
from .reg import RegFile
from .trace import Trace, TracePC
from .wsr import WSRFile


class OTBNState:
    def __init__(self) -> None:
        self.gprs = GPRs()
        self.wdrs = RegFile('w', 256, 32)

        self.wsrs = WSRFile()
        self.csrs = CSRFile()

        self.pc = 0
        self._pc_next_override = None  # type: Optional[int]

        _, imem_size = get_memory_layout()['IMEM']
        self.imem_size = imem_size

        self.dmem = Dmem()

        # Stalling support: Instructions can indicate they should stall by
        # yielding in OTBNInsn.execute. For non instruction related stalls,
        # setting self.non_insn_stall will produce a stall.
        #
        # As a special case, we stall until the URND reseed is completed then
        # stall for one more cycle before fetching the first instruction (to
        # match the behaviour of the RTL). This is modelled by setting
        # self._start_stall, self._urnd_stall and self.non_insn_stall
        self.non_insn_stall = False
        self._start_stall = False
        self._urnd_stall = False

        self.loop_stack = LoopStack()
        self.ext_regs = OTBNExtRegs()
        self.running = False

        self._err_bits = 0
        self.pending_halt = False

        self._new_rnd_data = None  # type: Optional[int]
        self._urnd_reseed_complete = False

    def get_next_pc(self) -> int:
        if self._pc_next_override is not None:
            return self._pc_next_override
        return self.pc + 4

    def set_next_pc(self, next_pc: int) -> None:
        '''Overwrite the next program counter, e.g. as result of a jump.'''
        assert(self.is_pc_valid(next_pc))
        self._pc_next_override = next_pc

    def set_rnd_data(self, rnd_data: int) -> None:
        self._new_rnd_data = rnd_data

    def set_urnd_reseed_complete(self) -> None:
        self._urnd_reseed_complete = True

    def loop_start(self, iterations: int, bodysize: int) -> None:
        self.loop_stack.start_loop(self.pc + 4, iterations, bodysize)

    def loop_step(self, loop_warps: Dict[int, int]) -> None:
        back_pc = self.loop_stack.step(self.pc, loop_warps)
        if back_pc is not None:
            self.set_next_pc(back_pc)

    def in_loop(self) -> bool:
        '''The processor is currently executing a loop.'''

        # A loop is executed if the loop stack is not empty.
        return bool(self.loop_stack.stack)

    def changes(self) -> List[Trace]:
        c = []  # type: List[Trace]
        c += self.gprs.changes()
        if self._pc_next_override is not None:
            # Only append the next program counter to the trace if it is special
            c.append(TracePC(self.get_next_pc()))
        c += self.dmem.changes()
        c += self.loop_stack.changes()
        c += self.ext_regs.changes()
        c += self.wsrs.changes()
        c += self.csrs.flags.changes()
        c += self.wdrs.changes()
        return c

    def commit(self, sim_stalled: bool) -> None:
        # In case of a pending halt only commit the external registers, which
        # contain e.g. the ERR_BITS field, but nothing else.
        if self.pending_halt:
            self.ext_regs.commit()
            return

        # If error bits are set, pending_halt should have been set as well.
        assert self._err_bits == 0

        if self._new_rnd_data:
            self.wsrs.RND.set_unsigned(self._new_rnd_data)
            self._new_rnd_data = None

        if self._urnd_stall:
            if self._urnd_reseed_complete:
                self._urnd_stall = False

            return

        # If self._start_stall, this is the end of the stall cycle at the start
        # of a run. Clear self.non_insn_stall and self._start_stall
        # and commit self.ext_regs (so the start flag becomes visible).
        if self._start_stall:
            self._start_stall = False
            self.non_insn_stall = False
            self.ext_regs.commit()

        # If we're stalled, there's nothing more to do: we only commit the rest
        # of the architectural state when we finish our stall cycles.
        if sim_stalled:
            return

        self.dmem.commit()
        self.gprs.commit()
        self.pc = self.get_next_pc()
        self._pc_next_override = None
        self.loop_stack.commit()
        self.ext_regs.commit()
        self.wsrs.commit()
        self.csrs.flags.commit()
        self.wdrs.commit()

    def _abort(self) -> None:
        '''Abort any pending state changes'''
        self.gprs.abort()
        self._pc_next_override = None
        self.dmem.abort()
        self.loop_stack.abort()
        self.ext_regs.abort()
        self.wsrs.abort()
        self.csrs.flags.abort()
        self.wdrs.abort()

    def start(self) -> None:
        '''Set the running flag and the ext_reg busy flag; perform state init'''
        self.ext_regs.write('STATUS', Status.BUSY_EXECUTE, True)
        self.ext_regs.write('INSN_CNT', 0, True)
        self.running = True
        self._start_stall = True
        self._urnd_stall = True
        self.non_insn_stall = True
        self.pending_halt = False
        self._err_bits = 0
        self._urnd_reseed_complete = False

        self.pc = self.get_start_addr()

        # Reset CSRs, WSRs, loop stack and call stack
        self.csrs = CSRFile()
        self.wsrs = WSRFile()
        self.loop_stack = LoopStack()
        self.gprs.start()

    def get_start_addr(self) -> int:
        '''Get the start address of the processor.

        Set the start address by writing the external register START_ADDR before
        calling start(), and commiting the external register changes.

        '''
        return self.ext_regs.read('START_ADDR', True)

    def stop(self) -> None:
        '''Set flags to stop the processor and maybe abort the instruction.

        If the current instruction has caused an error (so self._err_bits is
        nonzero), abort all its pending changes, including changes to external
        registers.

        If not, we've just executed an ECALL. The only pending change will be
        the increment of INSN_CNT that we want to keep.

        Either way, set the appropriate bits in the external ERR_CODE register,
        clear the busy flag and write STOP_PC.

        '''
        if self._err_bits:
            # Abort all pending changes, including changes to external registers.
            self._abort()

        # INTR_STATE is the interrupt state register. Bit 0 (which is being
        # set) is the 'done' flag.
        self.ext_regs.set_bits('INTR_STATE', 1 << 0)
        # STATUS is a status register. Return to idle.
        self.ext_regs.write('STATUS', Status.IDLE, True)

        # Make any error bits visible
        self.ext_regs.write('ERR_BITS', self._err_bits, True)

        # Make the final PC visible. This isn't currently in the RTL, but is
        # useful in simulations that want to track whether we stopped where we
        # expected to stop.
        self.ext_regs.write('STOP_PC', self.pc, True)

        self.running = False

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

    def is_pc_valid(self, pc: int) -> bool:
        '''Return whether pc is a valid program counter.'''
        # The PC should always be non-negative since it's represented as an
        # unsigned value. (It's an error in the simulator if that's come
        # unstuck)
        assert 0 <= pc

        # Check the new PC is word-aligned
        if pc & 3:
            return False

        # Check the new PC lies in instruction memory
        if pc >= self.imem_size:
            return False

        return True

    def post_insn(self, loop_warps: Dict[int, int]) -> None:
        '''Update state after running an instruction but before commit'''
        self.ext_regs.increment_insn_cnt()
        self.loop_step(loop_warps)
        self.gprs.post_insn()

        self._err_bits |= self.gprs.err_bits() | self.loop_stack.err_bits()
        if self._err_bits:
            self.pending_halt = True

        # Check that the next PC is valid, but only if we're not stopping
        # anyway. This handles the case where we have a straight-line
        # instruction at the top of memory. Jumps and branches to invalid
        # addresses are handled in the instruction definition.
        #
        # This check is squashed if we're already halting, which avoids a
        # problem when you have an ECALL instruction at the top of memory (the
        # next address is bogus, but we don't care because we're stopping
        # anyway).
        if not self.is_pc_valid(self.get_next_pc()) and not self.pending_halt:
            self._err_bits |= ErrBits.BAD_INSN_ADDR
            self.pending_halt = True

    def read_csr(self, idx: int) -> int:
        '''Read the CSR with index idx as an unsigned 32-bit number'''
        return self.csrs.read_unsigned(self.wsrs, idx)

    def write_csr(self, idx: int, value: int) -> None:
        '''Write value (an unsigned 32-bit number) to the CSR with index idx'''
        self.csrs.write_unsigned(self.wsrs, idx, value)

    def peek_call_stack(self) -> List[int]:
        '''Return the current call stack, bottom-first'''
        return self.gprs.peek_call_stack()

    def stop_at_end_of_cycle(self, err_bits: int) -> None:
        '''Tell the simulation to stop at the end of the cycle

        Any bits set in err_bits will be set in the ERR_BITS register when
        we're done.

        '''
        self._err_bits |= err_bits
        self.pending_halt = True
