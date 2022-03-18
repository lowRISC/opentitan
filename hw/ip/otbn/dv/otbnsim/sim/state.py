# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import IntEnum
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


# The number of cycles spent in the 'WIPE' state. This takes constant time in
# the RTL, mirrored here.
_WIPE_CYCLES = 98


class FsmState(IntEnum):
    r'''State of the internal start/stop FSM

    The FSM diagram looks like:


          IDLE -> PRE_EXEC -> FETCH_WAIT -> EXEC
            ^                                | |
            \---------------- WIPING_GOOD <--/ |
                                               |
                  LOCKED <--  WIPING_BAD  <----/

    IDLE represents the state when nothing is going on but there have been no
    fatal errors. It matches Status.IDLE. LOCKED represents the state when
    there has been a fatal error. It matches Status.LOCKED.

    PRE_EXEC, FETCH_WAIT, EXEC, WIPING_GOOD and WIPING_BAD correspond to
    Status.BUSY_EXECUTE. PRE_EXEC is the period after starting OTBN where we're
    still waiting for an EDN value to seed URND. FETCH_WAIT is the single cycle
    delay after seeding URND to fill the prefetch stage. EXEC is the period
    where we start fetching and executing instructions.

    WIPING_GOOD and WIPING_BAD represent the time where we're performing a
    secure wipe of internal state (ending in updating the STATUS register to
    show we're done). The difference between them is that WIPING_GOOD goes back
    to IDLE and WIPING_BAD goes to LOCKED.

    This is a refinement of the Status enum and the integer values are picked
    so that you can divide by 10 to get the corresponding Status entry. (This
    isn't used in the code, but makes debugging slightly more convenient when
    you just have the numeric values available).
    '''
    IDLE = 0
    PRE_EXEC = 10
    FETCH_WAIT = 11
    EXEC = 12
    WIPING_GOOD = 13
    WIPING_BAD = 14
    LOCKED = 2550


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

        self._fsm_state = FsmState.IDLE
        self._next_fsm_state = FsmState.IDLE

        self.loop_stack = LoopStack()
        self.ext_regs = OTBNExtRegs()

        self._err_bits = 0
        self.pending_halt = False

        self.rnd_256b_counter = 0
        self.urnd_256b_counter = 0

        self.rnd_set_flag = False

        self.rnd_req = 0
        self.rnd_cdc_pending = False
        self.urnd_cdc_pending = False

        self.rnd_cdc_counter = 0
        self.urnd_cdc_counter = 0

        self.rnd_256b = 0
        self.urnd_256b = 4 * [0]
        self.urnd_64b = 0

        # To simulate injecting integrity errors, we set a flag to say that
        # IMEM is no longer readable without getting an error. This can't take
        # effect instantly because the RTL's prefetch stage (which we don't
        # model except for matching its timing) has a copy of the next
        # instruction. Make this a counter, decremented once per cycle. When we
        # get to zero, we set the flag.
        self._time_to_imem_invalidation = None  # type: Optional[int]
        self.invalidated_imem = False

        # This flag controls whether we do the secure wipe sequence after
        # finishing an operation. Eventually it will be unconditionally enabled
        # (once everything works together properly).
        self.secure_wipe_enabled = False

        # This is the number of cycles left for wiping. When we're in the
        # WIPING_GOOD or WIPING_BAD state, this should be a non-negative
        # number. Initialise to -1 to catch bugs if we forget to set it.
        self.wipe_cycles = -1

        # If this is nonzero, there's been an error injected from outside. The
        # Sim.step function will OR these bits into err_bits and stop at the
        # end of the next cycle. (We don't just call stop_at_end_of_cycle
        # because this runs earlier in the cycle than step(), which would mean
        # we wouldn't see the final instruction get executed and then
        # cancelled).
        self.injected_err_bits = 0

    def get_next_pc(self) -> int:
        if self._pc_next_override is not None:
            return self._pc_next_override
        return self.pc + 4

    def set_next_pc(self, next_pc: int) -> None:
        '''Overwrite the next program counter, e.g. as result of a jump.'''
        assert(self.is_pc_valid(next_pc))
        self._pc_next_override = next_pc

    def edn_urnd_step(self, urnd_data: int) -> None:
        # Take the new data
        assert 0 <= urnd_data < (1 << 32)

        # There should not be a pending URND result before an EDN step.
        assert not self.urnd_cdc_pending

        # Collect 32b packages in a 64b array of 4 elements
        shift_num = 32 * (self.urnd_256b_counter % 2)
        self.urnd_64b = self.urnd_64b | (urnd_data << shift_num)

        if self.urnd_256b_counter % 2:
            idx = self.urnd_256b_counter // 2
            self.urnd_256b[idx] = self.urnd_64b
            self.urnd_64b = 0

        if self.urnd_256b_counter == 7:
            # Reset the 32b package counter and wait until receiving done
            # signal from RTL
            self.urnd_256b_counter = 0
            self.urnd_cdc_pending = True
        else:
            # Count until 8 valid packages are received
            self.urnd_256b_counter += 1
            return

        # Reset the 32b package counter and wait until receiving done
        # signal from RTL
        self.urnd_256b_counter = 0

    def edn_rnd_step(self, rnd_data: int) -> None:
        # Take the new data
        assert 0 <= rnd_data < (1 << 32)

        # There should not be a pending RND result before an EDN step.
        assert not self.rnd_cdc_pending

        # Collect 32b packages in a 256b variable
        new_word = rnd_data << (32 * self.rnd_256b_counter)
        assert new_word < (1 << 256)
        self.rnd_256b = self.rnd_256b | new_word

        if self.rnd_256b_counter == 7:
            # Reset the 32b package counter and wait until receiving done
            # signal from RTL
            self.rnd_256b_counter = 0
            self.rnd_cdc_pending = True
        else:
            # Count until 8 valid packages are received
            self.rnd_256b_counter += 1
            return

        # Reset the 32b package counter and wait until receiving done
        # signal from RTL
        self.rnd_256b_counter = 0

    def edn_flush(self) -> None:
        # EDN Flush gets called after a reset signal from EDN clock domain
        # arrives. It clears out internals of the model regarding EDN data
        # processing on both RND and URND side.
        self.rnd_256b = 0
        self.rnd_cdc_pending = False
        self.rnd_cdc_counter = 0
        self.rnd_256b_counter = 0

        self.urnd_64b = 0
        self.urnd_256b = 4 * [0]
        self.urnd_256b_counter = 0
        self.urnd_cdc_pending = False
        self.urnd_cdc_counter = 0

    def rnd_reg_set(self) -> None:
        # This sets RND register inside WSR immediately. Calling this with
        # using DPI causes timing problems so it is best to it when we want
        # to actually set RND register (at commit method and at the start if
        # RND processing is completed after OTBN stopped running)
        if self.rnd_set_flag:
            self.wsrs.RND.set_unsigned(self.rnd_256b)
            self.rnd_256b = 0
            self.rnd_cdc_pending = False
            self.rnd_set_flag = False
            self.rnd_cdc_counter = 0

    def rnd_completed(self) -> None:
        # This will be called when all the packages are received and processed
        # by RTL. Model will set RND register, pending flag and internal
        # variables will be cleared.

        # These must be true since model calculates RND data faster than RTL.
        # But the synchronisation of the data should not take more than
        # 5 cycles ideally.
        assert self.rnd_cdc_counter < 6

        # TODO: Assert rnd_cdc_pending when request is correctly modelled.
        self.rnd_set_flag = True

    def urnd_completed(self) -> None:
        # URND completed gets called after RTL signals that the processing
        # of incoming EDN data is done. This also sets up EXEC state of the
        # FSM of the model. This includes a dirty hack which disables
        # fsm_state assertion because we are always calling this method
        # while we are doing system level tests. This will be removed after
        # request modelling of EDN is done.
        assert self.urnd_cdc_counter < 6

        # TODO: Assert urnd_cdc_pending when request is correctly modelled.
        self.wsrs.URND.set_seed(self.urnd_256b)
        self.urnd_256b = 4 * [0]
        self.urnd_cdc_pending = False
        self.urnd_cdc_counter = 0

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
            # Only append the next program counter to the trace if it has
            # been set explicitly.
            c.append(TracePC(self.get_next_pc()))
        c += self.dmem.changes()
        c += self.loop_stack.changes()
        c += self.ext_regs.changes()
        c += self.wsrs.changes()
        c += self.csrs.flags.changes()
        c += self.wdrs.changes()
        return c

    def running(self) -> bool:
        return self._fsm_state not in [FsmState.IDLE, FsmState.LOCKED]

    def wiping(self) -> bool:
        return self._fsm_state in [FsmState.WIPING_GOOD, FsmState.WIPING_BAD]

    def commit(self, sim_stalled: bool) -> None:
        if self._time_to_imem_invalidation is not None:
            self._time_to_imem_invalidation -= 1
            if self._time_to_imem_invalidation == 0:
                self.invalidated_imem = True
                self._time_to_imem_invalidation = None

        # Check if we processed the RND data, if so set the register. This is
        # done seperately from the rnd_completed method because in other case
        # we are exiting stall caused by RND waiting by one cycle too early.
        self.rnd_reg_set()

        # If model is waiting for the RND register to cross CDC, increment a
        # counter to say how long we've waited. This lets us spot if the CDC
        # gets stuck for some reason.
        if self.rnd_cdc_pending:
            self.rnd_cdc_counter += 1

        # If model is waiting for the RND register to cross CDC, increment a
        # counter to say how long we've waited. This lets us spot if the CDC
        # gets stuck for some reason.
        if self.urnd_cdc_pending:
            self.urnd_cdc_counter += 1

        old_state = self._fsm_state

        self._fsm_state = self._next_fsm_state
        self.ext_regs.commit()

        # Pull URND out separately because we also want to commit this in some
        # "idle-ish" states (FETCH_WAIT)
        self.wsrs.URND.commit()

        # In some states, we can get away with just committing external
        # registers (which lets us reflect things like the update to the STATUS
        # register) but nothing else. This is just an optimisation: if
        # everything is working properly, there won't be any other pending
        # changes.
        if old_state not in [FsmState.EXEC,
                             FsmState.WIPING_GOOD, FsmState.WIPING_BAD]:
            return

        self.gprs.commit()

        # If we're stalled, there's nothing more to do: we only commit the rest
        # of the architectural state when we finish our stall cycles.
        if sim_stalled:
            return

        self.dmem.commit()
        self.pc = self.get_next_pc()
        self._pc_next_override = None
        self.loop_stack.commit()
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
        '''Start running; perform state init'''
        self.ext_regs.write('STATUS', Status.BUSY_EXECUTE, True)
        self.pending_halt = False
        self._err_bits = 0

        self._fsm_state = FsmState.PRE_EXEC
        self._next_fsm_state = FsmState.PRE_EXEC

        self.pc = 0

        # Reset CSRs, WSRs, loop stack and call stack. WSRs have special
        # treatment because some of them have values that persist across
        # operations.
        self.csrs = CSRFile()
        self.wsrs.on_start()
        self.loop_stack = LoopStack()
        self.gprs.empty_call_stack()

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
            # Abort all pending changes, including changes to external
            # registers.
            self._abort()

        # INTR_STATE is the interrupt state register. Bit 0 (which is being
        # set) is the 'done' flag.
        self.ext_regs.set_bits('INTR_STATE', 1 << 0)

        should_lock = (self._err_bits >> 16) != 0

        # Make any error bits visible
        self.ext_regs.write('ERR_BITS', self._err_bits, True)

        # Make the final PC visible. This isn't currently in the RTL, but is
        # useful in simulations that want to track whether we stopped where we
        # expected to stop.
        self.ext_regs.write('STOP_PC', self.pc, True)

        # Set the WIPE_START flag if we were running. This is used to tell the
        # C++ model code that this is a good time to inspect DMEM and check
        # that the RTL and model match. The flag will be cleared again on the
        # next cycle.
        if self._fsm_state in [FsmState.FETCH_WAIT, FsmState.EXEC]:
            self.ext_regs.write('WIPE_START', 1, True)

        # Switch to a 'wiping' state
        self._next_fsm_state = (FsmState.WIPING_BAD if should_lock
                                else FsmState.WIPING_GOOD)
        self.wipe_cycles = (_WIPE_CYCLES if self.secure_wipe_enabled else 2)

        # Clear the "we should stop soon" flag
        self.pending_halt = False

    def get_fsm_state(self) -> FsmState:
        return self._fsm_state

    def set_fsm_state(self, new_state: FsmState) -> None:
        self._next_fsm_state = new_state

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

    def invalidate_imem(self) -> None:
        self._time_to_imem_invalidation = 2

    def clear_imem_invalidation(self) -> None:
        '''Clear any effective or pending IMEM invalidation'''
        self._time_to_imem_invalidation = None
        self.invalidated_imem = False

    def wipe(self) -> None:
        if not self.secure_wipe_enabled:
            return

        self.gprs.empty_call_stack()
        self.gprs.wipe()
        self.wdrs.wipe()
        self.wsrs.wipe()
        self.csrs.wipe()

    def take_injected_err_bits(self) -> None:
        '''Apply any injected errors, stopping at the end of the cycle'''
        if self.injected_err_bits != 0:
            self.stop_at_end_of_cycle(self.injected_err_bits)
            self.injected_err_bits = 0
