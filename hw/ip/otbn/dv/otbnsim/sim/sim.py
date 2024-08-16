# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Iterator, List, Optional, Tuple

from .constants import ErrBits, LcTx, Status, read_lc_tx_t
from .decode import EmptyInsn
from .isa import OTBNInsn
from .state import OTBNState, FsmState
from .stats import ExecutionStats
from .trace import Trace

# A dictionary that defines a function of the form "address -> from -> to". If
# PC is the current PC and cnt is the count for the innermost loop then
# warps[PC][cnt] = new_cnt means that we should warp the current count to
# new_cnt.
LoopWarps = Dict[int, Dict[int, int]]

# The return type of the Step function: a possible instruction that was
# executed, together with a list of changes.
StepRes = Tuple[Optional[OTBNInsn], List[Trace]]


class OTBNSim:
    def __init__(self) -> None:
        self.state = OTBNState()
        self.program = []  # type: List[OTBNInsn]
        self.loop_warps = {}  # type: LoopWarps
        self.stats = None  # type: Optional[ExecutionStats]
        self._execute_generator = None  # type: Optional[Iterator[None]]
        self._next_insn = None  # type: Optional[OTBNInsn]

    def load_program(self, program: List[OTBNInsn]) -> None:
        self.program = program.copy()
        self.state.clear_imem_invalidation()

    def add_loop_warp(self, addr: int, from_cnt: int, to_cnt: int) -> None:
        '''Add a new loop warp to the simulation'''
        self.loop_warps.setdefault(addr, {})[from_cnt] = to_cnt

    def load_data(self, data: bytes, has_validity: bool) -> None:
        '''Load bytes into DMEM, starting at address zero.

        If has_validity is true, each 32-bit word should be represented by 5
        bytes (1 byte that says whether the word is valid, then 4 bytes that
        give the word in little-endian format). If has_validity is false, each
        word is considered valid and is represented by 4 bytes in little-endian
        format.

        '''
        self.state.dmem.load_le_words(data, has_validity)

    def start(self, collect_stats: bool) -> None:
        '''Prepare to start the execution.

        Use run() or step() to actually execute the program.

        '''
        self.stats = ExecutionStats(self.program) if collect_stats else None
        self._execute_generator = None
        self._next_insn = None
        self.state.start()

    def initial_secure_wipe(self) -> None:
        '''This is run at the start of a secure wipe after reset.'''
        self.state.start_init_sec_wipe()

    def start_mem_wipe(self, is_imem: bool) -> None:
        if self.state.get_fsm_state() != FsmState.IDLE:
            return

        new_status = (Status.BUSY_SEC_WIPE_IMEM
                      if is_imem else Status.BUSY_SEC_WIPE_DMEM)

        self.state.set_fsm_state(FsmState.MEM_SEC_WIPE)
        self.state.ext_regs.write('STATUS', new_status, True)

    def _fetch(self, pc: int) -> OTBNInsn:
        word_pc = pc >> 2
        if word_pc >= len(self.program):
            raise RuntimeError('Trying to execute instruction at address '
                               '{:#x}, but the program is only {:#x} '
                               'bytes ({} instructions) long. Since there '
                               'are no architectural contents of the '
                               'memory here, we have to stop.'
                               .format(pc,
                                       4 * len(self.program),
                                       len(self.program)))

        if self.state.invalidated_imem:
            return EmptyInsn(self.state.pc)

        return self.program[word_pc]

    def _on_stall(self,
                  verbose: bool,
                  fetch_next: bool) -> List[Trace]:
        '''This is run on a stall cycle'''
        self.state.stop_if_pending_halt()
        changes = self.state.changes()
        self.state.commit(sim_stalled=True)
        if fetch_next:
            self._next_insn = self._fetch(self.state.pc)
        if self.stats is not None and not self.state.wiping():
            self.stats.record_stall()
        if verbose:
            self._print_trace(self.state.pc, '(stall)', changes)

        return changes

    def _on_retire(self,
                   verbose: bool,
                   insn: OTBNInsn) -> List[Trace]:
        '''This is run when an instruction completes'''
        assert self._execute_generator is None
        self.state.post_insn(self.loop_warps.get(self.state.pc, {}))

        if self.stats is not None:
            self.stats.record_insn(insn, self.state)

        halting = self.state.stop_if_pending_halt()
        changes = self.state.changes()

        # Program counter before commit
        pc_before = self.state.pc
        self.state.commit(sim_stalled=False)

        # Fetch the next instruction unless we're done or this instruction had
        # `has_fetch_stall` set (in which case we inject a single cycle stall).
        no_fetch = halting or insn.has_fetch_stall
        self._next_insn = None if no_fetch else self._fetch(self.state.pc)

        disasm = insn.disassemble(pc_before)
        if verbose:
            self._print_trace(pc_before, disasm, changes)

        return changes

    def _delayed_insn_cnt_zero(self, delay_if_locking: int) -> None:
        '''Zero INSN_CNT if we are in a wiping state and are going to lock
        after wipe.

        This is delayed by delay_if_locking (using state.time_to_insn_cnt_zero)
        to match the timing in the RTL.
        '''
        assert self.state.get_fsm_state() in [FsmState.PRE_WIPE,
                                              FsmState.WIPING]

        # Only zero instruction count if we're wiping before lock
        if not self.state.lock_after_wipe:
            return

        # We don't print "INSN_CNT=0" on every cycle of the wipe, so we should
        # only do something if the current value is nonzero.
        if self.state.ext_regs.read('INSN_CNT', True) == 0:
            return

        # In this case, we know we want to zero INSN_CNT. There might be an
        # operation to do so that has already been enqueued. If not (or if it
        # would be waiting longer than delay_if_locking), switch to a new
        # counter.
        if self.state.time_to_insn_cnt_zero is None:
            self.state.time_to_insn_cnt_zero = delay_if_locking
        count = min(self.state.time_to_insn_cnt_zero, delay_if_locking)

        if count == 0:
            # If _time_to_insn_cnt_zero is now zero, it means that this is the
            # cycle to update insn_cnt.
            self.state.ext_regs.write('INSN_CNT', 0, True)
            self.state.time_to_insn_cnt_zero = None
        else:
            # If _time_to_insn_cnt_zero isn't zero, we should decrement it
            # (maybe we'll update insn_cnt next cycle).
            self.state.time_to_insn_cnt_zero = count - 1

    def step(self, verbose: bool) -> StepRes:
        '''Run a single cycle.

        Returns the instruction, together with a list of the architectural
        changes that have happened. If the model isn't currently executing,
        returns no instruction and no changes.

        '''
        fsm_state = self.state.get_fsm_state()
        # Pairs: (stepper, handles_injected_err). If handles_injected_err is
        # False then the generic code here will deal with any pending errors in
        # self.state.injected_err_bits. If True, then we expect the stepper
        # function to handle them.
        steppers = {
            FsmState.MEM_SEC_WIPE: (self._step_ext_wipe, False),
            FsmState.IDLE: (self._step_idle, False),
            FsmState.PRE_EXEC: (self._step_pre_exec, False),
            FsmState.EXEC: (self._step_exec, True),
            FsmState.PRE_WIPE: (self._step_pre_wipe, False),
            FsmState.WIPING: (self._step_wiping, False),
            FsmState.LOCKED: (self._step_idle, False)
        }

        stepper, handles_injected_err = steppers[fsm_state]
        self.state.step(not handles_injected_err)

        return stepper(verbose)

    def _step_idle(self, verbose: bool) -> StepRes:
        '''Step the simulation when OTBN is IDLE or LOCKED'''
        self.state.stop_if_pending_halt()

        is_locked = self.state.get_fsm_state() == FsmState.LOCKED

        # If we are locked or get an RMA request, the INSN_CNT register should
        # be zeroed. To avoid sending a line to stdout on every cycle, we only
        # actually do the register write if we've just entered the locked state
        # or the write will change something.
        should_zero = is_locked or self.state.rma_req == LcTx.ON
        new_zero = (self.state.cycles_in_this_state == 0 or
                    self.state.ext_regs.read('INSN_CNT', True) != 0)
        if should_zero and new_zero:
            self.state.ext_regs.write('INSN_CNT', 0, True)

        if self.state.delayed_lock:
            self.state.set_fsm_state(FsmState.LOCKED)
            self.state.ext_regs.write('STATUS', Status.LOCKED, True)
            is_locked = True

        # If we are IDLE and get an RMA request, we want to start a secure
        # wipe, which will eventually put us into the LOCKED state.
        if self.state.rma_req == LcTx.ON and not is_locked:
            self.state.ext_regs.write('STATUS', Status.BUSY_SEC_WIPE_INT, True)
            self.state.set_fsm_state(FsmState.PRE_WIPE)
            self.state.lock_after_wipe = True
            self.state.wipe_rounds_done = 0

        if self.state.init_sec_wipe_is_running() and not is_locked:
            # Wait for the URND seed. If there is some genuine state to wipe
            # (because self.state.has_state_to_wipe is true), then we switch to
            # WIPING, setting lock_after_wipe to true if the FSM state is
            # currently LOCKED.
            #
            # As a special case, there might be an RMA request and this might
            # be just after reset. In that case, we don't need to worry about
            # wiping state (because the entropy complex might not have been set
            # up yet, we might not even be able to seed URND). In that case, we
            # jump straight to the LOCKED state.
            if self.state.wsrs.URND.running:
                # If URND finishes, it's probably the seed for a secure wipe.
                # But there's an extra possibility: we might have seen an RMA
                # request before any instructions get run. In that case, the
                # rma_req flag will be high and the has_state_to_wipe flag will
                # be low. Jump straight to the LOCKED state and skip the WIPING
                # state (since there is nothing that needs wiping anyway).
                start_of_time_rma = (self.state.rma_req == LcTx.ON and
                                     not self.state.has_state_to_wipe)
                if start_of_time_rma:
                    self.state.complete_init_sec_wipe()
                    self.state.set_fsm_state(FsmState.LOCKED)
                    self.state.ext_regs.write('STATUS', Status.LOCKED, True)
                else:
                    self.state.set_fsm_state(FsmState.WIPING)
                    if is_locked:
                        self.state.lock_after_wipe = True

        changes = self.state.changes()
        self.state.commit(sim_stalled=True)
        return (None, changes)

    def _step_ext_wipe(self, verbose: bool) -> StepRes:
        '''Step the simulation DMEM/IMEM wipe operation'''
        self.state.stop_if_pending_halt()
        changes = self.state.changes()
        self.state.commit(sim_stalled=True)
        return (None, changes)

    def _step_pre_exec(self, verbose: bool) -> StepRes:
        '''Step the simulation in the PRE_EXEC state

        In this state, we're waiting for a URND seed. Once that appears, we
        switch to EXEC.
        '''
        if self.state.wsrs.URND.running:
            self.state.set_fsm_state(FsmState.EXEC)

        changes = self._on_stall(verbose, fetch_next=False)

        # Correctly handle an RMA request when we're still waiting to start by
        # jumping immediately to the LOCKED state
        if self.state.rma_req == LcTx.ON:
            self.lock_immediately()

        # Zero INSN_CNT the cycle after we are told to start
        if self.state.ext_regs.read('INSN_CNT', True) != 0:
            self.state.ext_regs.write('INSN_CNT', 0, True)

        return (None, changes)

    def _step_exec(self, verbose: bool) -> StepRes:
        '''Step the simulation when executing code'''

        # The initial secure wipe *must* be done when executing code.
        assert self.state.init_sec_wipe_is_done()

        self.state.wsrs.URND.step()

        insn = self._next_insn
        if insn is None:
            self.state.take_injected_err_bits()
            return (None, self._on_stall(verbose, fetch_next=True))

        # If there is an RMA request, we treat it a bit like a fatal error, and
        # abort any instruction that's currently running
        if self.state.rma_req == LcTx.ON:
            # TODO: Passing a nonzero value in ErrBits is incorrect: we don't
            #       actually expect anything to get set in the ERR_BITS
            #       register. But there's a bug somewhere in the Python code
            #       here and we don't properly stop execution when the err_bits
            #       register is nonzero. This is an ugly hack, and will die if
            #       someone reads ERR_BITS after we've stopped. But it gets the
            #       test working for now.
            self.state.stop_at_end_of_cycle(1)
            self.state.set_fsm_state(FsmState.PRE_WIPE)
            self.state.lock_after_wipe = True
            self._execute_generator = None

        # Whether or not we're currently executing an instruction, we fetched
        # an instruction on the previous cycle. If that fetch failed then
        # insn.has_bits will be false. In that case, generate an error by
        # throwing away the generator so we start executing the (bogus)
        # instruction immediately.
        if not insn.has_bits:
            self._execute_generator = None

        if self._execute_generator is None:
            # This is the first cycle for an instruction. Run any setup for
            # the state object and then start running the instruction
            # itself.
            self.state.pre_insn(insn.affects_control)

            # Either execute the instruction directly (if it is a
            # single-cycle instruction without a `yield` in execute()), or
            # return a generator for multi-cycle instructions. Note that
            # this doesn't consume the first yielded value.
            self._execute_generator = insn.execute(self.state)

        if self._execute_generator is not None:
            # This is a cycle for a multi-cycle instruction (which possibly
            # started just above)
            try:
                next(self._execute_generator)
            except StopIteration:
                self._execute_generator = None

        if (self.state.wsrs.RND.rep_err_escalate):
            self.state.stop_at_end_of_cycle(ErrBits.RND_REP_CHK_FAIL)
        if (self.state.wsrs.RND.fips_err_escalate):
            self.state.stop_at_end_of_cycle(ErrBits.RND_FIPS_CHK_FAIL)

        # Handle any pending injected error. Note that this has to run after
        # we've executed any instruction, to ensure we get a trace entry for
        # that instruction before it gets shot down.
        self.state.take_injected_err_bits()

        # If something bad happened asynchronously (because of an escalation),
        # we might have an unfinished instruction. But we want to turn it into
        # a "finished, but aborted" one.
        if self.state.pending_halt:
            self._execute_generator = None

        sim_stalled = (self._execute_generator is not None)
        if not sim_stalled:
            return (insn, self._on_retire(verbose, insn))

        return (None, self._on_stall(verbose, fetch_next=False))

    def _step_pre_wipe(self, verbose: bool) -> StepRes:
        '''Step the simulation when waiting for a URND seed for wipe'''

        # If we get an RMA request before we've managed to run any rounds of
        # wiping then we are waiting for our first URND seed. The entropy
        # complex might not be up, so we don't want to wait for a seed. Handle
        # this by jumping straight to the WIPING state and setting the number
        # of rounds to 1 (so that we don't wait again for a seed afterwards)
        if self.state.rma_req == LcTx.ON and not self.state.edn_seen_running:
            self.state.lock_after_wipe = True
            self.state.wipe_rounds_to_do = 1
            self.state.set_fsm_state(FsmState.WIPING)

        # Clear the WIPE_START register if it was set.
        if self.state.ext_regs.read('WIPE_START', True):
            self.state.ext_regs.write('WIPE_START', 0, True)

        # Zero INSN_CNT once if we're going to lock after wipe.
        self._delayed_insn_cnt_zero(0)

        if self.state.wsrs.URND.running:
            # Reflect wiping in STATUS register if it has not been updated yet.
            if ((self.state.ext_regs.read('STATUS', True) not in
                 [Status.BUSY_SEC_WIPE_INT, Status.LOCKED])):
                self.state.ext_regs.write('STATUS',
                                          Status.BUSY_SEC_WIPE_INT, True)

            self.state.set_fsm_state(FsmState.WIPING)

        return (None, self._on_stall(verbose, fetch_next=False))

    def _step_wiping(self, verbose: bool) -> StepRes:
        '''Step the simulation when wiping'''
        assert self.state.wipe_cycles >= 0

        # Keep track of whether there was actually a wipe operation in progress
        # (rather than us waiting for a URND seed for the next round). If there
        # was, then subtract one from the number of cycles left in that
        # operation.
        was_wiping = self.state.wipe_cycles > 0
        if was_wiping:
            self.state.wipe_cycles -= 1

        is_good = not self.state.lock_after_wipe
        locking = self.state.rma_req == LcTx.ON or not is_good

        # If there is an RMA request, ensure lock_after_wipe is set (since
        # we're going to lock when we're done)
        if self.state.rma_req == LcTx.ON:
            self.state.lock_after_wipe = True

        # If something bad happened asynchronously (because of an escalation),
        # we want to finish the secure wipe but accept no further commands.  To
        # this end, turn this into a "wipe because something bad happended".
        if self.state.pending_halt:
            self.state.lock_after_wipe = True

        # Zero INSN_CNT once if we're going to lock after wipe.
        self._delayed_insn_cnt_zero(1)

        if self.state.wipe_cycles == 1:
            # This is the penultimate clock cycle of a wipe round. We want to
            # model the behaviour that we expect "at the end of a wipe round".
            #
            # On the last wipe round, we actually perform a wipe on the model
            # side and set STATUS (to IDLE or LOCKED) to show that the wiping
            # has finished .
            #
            # If there's another wipe round to follow, we mark the URND
            # register as not available and request a new seed.
            #
            # RMA requests are a special case where the "last round" might
            # actually be the first one as well.
            final_wipe_round = (self.state.wipe_rounds_done ==
                                (self.state.wipe_rounds_to_do - 1))
            if final_wipe_round:
                next_status = Status.LOCKED if locking else Status.IDLE
                self.state.ext_regs.write('STATUS', next_status, True)
                self.state.wipe()
            else:
                self.state.wsrs.URND.running = False
                self.state._urnd_client.request()

        if self.state.wipe_cycles == 0:
            if was_wiping:
                self.state.wipe_rounds_done += 1

            final_wipe_round = (self.state.wipe_rounds_done ==
                                self.state.wipe_rounds_to_do)

            # This is the last clock cycle of a wipe round. Switch back to
            # PRE_WIPE if there is another round to do. If not, switch to
            # LOCKED or IDLE.
            if not final_wipe_round:
                self.state.set_fsm_state(FsmState.PRE_WIPE)
            else:
                # Set a flag that tells us to lock when we get to idle. This
                # matches the cycle of delay that happens between the end of a
                # secure wipe where we see an invalid RMA request and the
                # status getting locked.
                if self.state.rma_req != LcTx.OFF:
                    self.state.delayed_lock = True

                # We've finished the final round in the current secure wipe. If
                # there is an invalid RMA signal or we were already going to
                # lock after wipe (so have the locking signal set) then we
                # should lock. Otherwise, jump to IDLE.
                if locking:
                    next_state = FsmState.LOCKED
                    self.state.ext_regs.write('STATUS', Status.LOCKED, True)
                else:
                    next_state = FsmState.IDLE
                    if self.state.init_sec_wipe_is_running():
                        self.state.complete_init_sec_wipe()

                # Also, set wipe_cycles to an invalid value to make really sure
                # we've left the wiping code. Leave wipe_rounds_done unchanged
                # so that the "completed wipe" is visible when we come to write
                # out the U/V line later. We'll zero it again when we enter a
                # wiping state next time.
                self.state.wipe_cycles = -1

                self.state.set_fsm_state(next_state)

        return (None, self._on_stall(verbose, fetch_next=False))

    def dump_data(self) -> bytes:
        return self.state.dmem.dump_le_words()

    def _print_trace(self, pc: int, disasm: str, changes: List[Trace]) -> None:
        '''Print a trace of the current instruction'''
        changes_str = ', '.join([t.trace() for t in changes])
        print('{:08x} | {:45} | [{}]'.format(pc, disasm, changes_str))

    def on_otp_cdc_done(self) -> None:
        '''Signifies when the scrambling key request gets processed'''
        # This happens when we're doing a memory secure wipe, in which case we
        # want to switch to IDLE. However, it also happens if we're at the end
        # of a run that either will lock or already has done. In that case, we
        # don't want to do an FSM state change.
        cur_state = self.state.get_fsm_state()
        allowed_states = [FsmState.MEM_SEC_WIPE,
                          FsmState.PRE_WIPE, FsmState.WIPING, FsmState.LOCKED]
        assert cur_state in allowed_states
        if cur_state == FsmState.MEM_SEC_WIPE:
            self.state.ext_regs.write('STATUS', Status.IDLE, True)
            self.state.set_fsm_state(FsmState.IDLE)

    def send_err_escalation(self,
                            err_val: int, lock_immediately: bool) -> None:
        '''React to an error escalation'''
        assert err_val & ~ErrBits.MASK == 0
        self.state.injected_err_bits |= err_val
        self.state.lock_immediately = lock_immediately

    def lock_immediately(self) -> None:
        '''React to an event that should cause us to immediately jump to the
        locked state.'''
        self.state.set_fsm_state(FsmState.LOCKED)
        self.state.ext_regs.write('STATUS',
                                  Status.LOCKED, True, immediately=True)

    def set_rma_req(self, rma_req: int) -> None:
        '''Set the rma request pin state, based on a given integer input.

        This gets read later, on the special cycles when it should have an
        effect.
        '''
        self.state.rma_req = read_lc_tx_t(rma_req)

    def urnd_completed(self) -> None:
        '''An outstanding URND request has just completed.

        Pass the data to self.state (to tell it the data is ready). But also
        check that we are in a state where we expect to have made a URND
        request that can complete. If not, we should immediately jump to the
        locked state.
        '''
        self.state.urnd_completed()
        # There should only be a URND response if one of the following is true:
        #
        #  1. We're in PRE_EXEC, so are waiting for a seed for the urnd
        #     register itself.
        #
        #  2. We are in the middle of a secure wipe round and are waiting for
        #     the seed to run the second round.
        #
        # If we get a response at another time, we should treat it as
        # "unsolicited" and lock immediately.
        #
        # To distinguish (3) from "a URND ack appeared when we were in the
        # middle of the actual wipe operation", we can check the wipe_cycles
        # counter. This will be zero when the first round wipe operation is
        # done and we are waiting for the second round seed.

        cur_state = self.state.get_fsm_state()
        if cur_state not in [FsmState.PRE_EXEC, FsmState.PRE_WIPE]:
            self.lock_immediately()
