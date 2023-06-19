# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Iterator, List, Optional, Tuple

from .constants import ErrBits, Status
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
        if self.state.get_fsm_state() != FsmState.IDLE:
            return
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
            FsmState.WIPING_GOOD: (self._step_wiping, False),
            FsmState.WIPING_BAD: (self._step_wiping, False),
            FsmState.LOCKED: (self._step_idle, False)
        }

        stepper, handles_injected_err = steppers[fsm_state]
        self.state.step(not handles_injected_err)

        return stepper(verbose)

    def _step_idle(self, verbose: bool) -> StepRes:
        '''Step the simulation when OTBN is IDLE or LOCKED'''
        self.state.stop_if_pending_halt()
        if ((self.state._fsm_state == FsmState.LOCKED and
             self.state.cycles_in_this_state == 0)):
            self.state.ext_regs.write('INSN_CNT', 0, True)

        if self.state.init_sec_wipe_is_running():
            # Wait for the URND seed. Once that appears, switch to WIPING_GOOD
            # unless the FSM state is already LOCKED, in which case we change
            # it to WIPING_BAD.
            if self.state.wsrs.URND.running:
                if self.state.get_fsm_state() == FsmState.LOCKED:
                    self.state.set_fsm_state(FsmState.WIPING_BAD)
                else:
                    self.state.set_fsm_state(FsmState.WIPING_GOOD)

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

    def _step_wiping(self, verbose: bool) -> StepRes:
        '''Step the simulation when wiping'''
        assert self.state.wipe_cycles >= 0
        if self.state.wipe_cycles > 0:
            self.state.wipe_cycles -= 1

        # If something bad happened asynchronously (because of an escalation),
        # we want to finish the secure wipe but accept no further commands.  To
        # this end, turn this into a "wipe because something bad happended".
        if self.state.pending_halt:
            self.state._fsm_state = FsmState.WIPING_BAD

        # Reflect wiping in STATUS register if it has not been updated yet.
        if (self.state.wipe_cycles > 0 and
            (self.state.ext_regs.read('STATUS', True) not in
             [Status.BUSY_SEC_WIPE_INT, Status.LOCKED])):
            self.state.ext_regs.write('STATUS', Status.BUSY_SEC_WIPE_INT, True)

        is_good = self.state.get_fsm_state() == FsmState.WIPING_GOOD

        # Clear the WIPE_START register if it was set.
        if self.state.ext_regs.read('WIPE_START', True):
            self.state.ext_regs.write('WIPE_START', 0, True)

        # Zero INSN_CNT once if we're in state WIPING_BAD.
        if not is_good and self.state.ext_regs.read('INSN_CNT', True) != 0:
            if ((self.state.zero_insn_cnt_next or
                 not self.state.lock_immediately)):
                self.state.ext_regs.write('INSN_CNT', 0, True)
                self.state.zero_insn_cnt_next = False
            if self.state.lock_immediately:
                # Zero INSN_CNT in the *next* cycle to match RTL control flow.
                self.state.zero_insn_cnt_next = True

        if self.state.wipe_cycles == 1:
            # This is the penultimate clock cycle of a wipe round.
            if self.state.first_round_of_wipe:
                # This is the first round.
                self.state.wsrs.URND.running = False
                if not self.state.rma_req:
                    # If not wiping because of an RMA request, request an URND
                    # refresh.
                    self.state._urnd_client.request()
            if (not self.state.first_round_of_wipe) or self.state.rma_req:
                # This is the second wipe round or the only round of a wipe
                # during an RMA request, so wipe all registers and set STATUS.
                next_status = Status.IDLE if is_good else Status.LOCKED
                self.state.ext_regs.write('STATUS', next_status, True)
                self.state.wipe()

        if self.state.wipe_cycles == 0:
            # This is the final clock cycle of a wipe round.
            if self.state.first_round_of_wipe and not self.state.rma_req:
                # This is the first wipe round and since there's no RMA
                # request, a second round must follow after URND refresh
                # acknowledgment.
                if self.state.wsrs.URND.running:
                    self.state.first_round_of_wipe = False
                    self.state.set_fsm_state(self.state.get_fsm_state())
            else:
                # This is the second wipe round or the only wipe round during
                # an RMA request. If the wipe was good, set the next state to
                # IDLE; otherwise set it to LOCKED.
                if is_good:
                    assert not self.state.rma_req
                    next_state = FsmState.IDLE
                    if self.state.init_sec_wipe_is_running():
                        self.state.complete_init_sec_wipe()
                else:
                    next_state = FsmState.LOCKED

                # Also, set wipe_cycles to an invalid value to make really sure
                # we've left the wiping code.
                self.wipe_cycles = -1
                self.state.first_round_of_wipe = True
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
        assert cur_state in [FsmState.MEM_SEC_WIPE,
                             FsmState.WIPING_BAD, FsmState.LOCKED]
        if cur_state == FsmState.MEM_SEC_WIPE:
            self.state.ext_regs.write('STATUS', Status.IDLE, True)
            self.state.set_fsm_state(FsmState.IDLE)

    def send_err_escalation(self,
                            err_val: int, lock_immediately: bool) -> None:
        '''React to an error escalation'''
        assert err_val & ~ErrBits.MASK == 0
        self.state.injected_err_bits |= err_val
        self.state.lock_immediately = lock_immediately

    def send_rma_req(self) -> None:
        # Incoming RMA request basically acts like a fatal error.
        # It does not immediately change the status to LOCKED just like any
        # fatal error except spurious URND ack.
        self.state.rma_req = True
        self.state.pending_halt = True
