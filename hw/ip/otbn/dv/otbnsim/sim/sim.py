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
from .ext_regs import TraceExtRegChange, ExtRegChange


# A dictionary that defines a function of the form "address -> from -> to". If
# PC is the current PC and cnt is the count for the innermost loop then
# warps[PC][cnt] = new_cnt means that we should warp the current count to
# new_cnt.
LoopWarps = Dict[int, Dict[int, int]]


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

    def configure(self, enable_secure_wipe: bool) -> None:
        self.state.secure_wipe_enabled = enable_secure_wipe

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

        if self.state.pending_halt:
            # We've reached the end of the run (either because of an ECALL
            # instruction or an error).
            self.state.stop()

        changes = self.state.changes()

        # Program counter before commit
        pc_before = self.state.pc
        self.state.commit(sim_stalled=False)

        # Fetch the next instruction unless this instruction had
        # `has_fetch_stall` set, in which case we inject a single cycle stall.
        self._next_insn = (None if insn.has_fetch_stall
                           else self._fetch(self.state.pc))

        disasm = insn.disassemble(pc_before)
        if verbose:
            self._print_trace(pc_before, disasm, changes)

        return changes

    def step(self, verbose: bool) -> Tuple[Optional[OTBNInsn], List[Trace]]:
        '''Run a single cycle.

        Returns the instruction, together with a list of the architectural
        changes that have happened. If the model isn't currently running,
        returns no instruction and no changes.

        '''
        if not self.state.running():
            changes = self.state.changes()
            self.state.commit(sim_stalled=True)
            return (None, changes)

        if self.state.fsm_state == FsmState.PRE_EXEC:
            # Zero INSN_CNT the cycle after we are told to start (and every
            # cycle after that until we start executing instructions, but that
            # doesn't really matter)
            changes = self._on_stall(verbose, fetch_next=False)
            changes += [TraceExtRegChange('RND_REQ',
                                          ExtRegChange('=', 0, True, 0))]
            self.state.ext_regs.write('INSN_CNT', 0, True)
            return (None, changes)

        # If we are not in PRE_EXEC, then we have a valid URND seed. So we
        # should step URND regardless of whether we're actually executing
        # instructions.
        self.state.wsrs.URND.commit()
        self.state.wsrs.URND.step()

        if self.state.fsm_state == FsmState.FETCH_WAIT:
            changes = self._on_stall(verbose, fetch_next=False)
            return (None, changes)

        if self.state.fsm_state in [FsmState.WIPING_GOOD, FsmState.WIPING_BAD]:
            assert self.state.wipe_cycles > 0
            self.state.wipe_cycles -= 1

            # Clear the WIPE_START register if it was set
            if self.state.ext_regs.read('WIPE_START', True):
                self.state.ext_regs.write('WIPE_START', 0, True)

            # Wipe all registers and set STATUS on the penultimate cycle.
            if self.state.wipe_cycles == 1:
                next_status = (Status.IDLE
                               if self.state.fsm_state == FsmState.WIPING_GOOD
                               else Status.LOCKED)
                self.state.ext_regs.write('STATUS', next_status, True)
                self.state.wipe()

            return (None, self._on_stall(verbose, fetch_next=False))

        assert self.state.fsm_state == FsmState.EXEC

        insn = self._next_insn
        if insn is None:
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

        sim_stalled = (self._execute_generator is not None)
        if not sim_stalled:
            return (insn, self._on_retire(verbose, insn))

        return (None, self._on_stall(verbose, fetch_next=False))

    def dump_data(self) -> bytes:
        return self.state.dmem.dump_le_words()

    def _print_trace(self, pc: int, disasm: str, changes: List[Trace]) -> None:
        '''Print a trace of the current instruction'''
        changes_str = ', '.join([t.trace() for t in changes])
        print('{:08x} | {:45} | [{}]'.format(pc, disasm, changes_str))

    def on_lc_escalation(self) -> None:
        '''React to a lifecycle controller escalation signal'''
        self.state.stop_at_end_of_cycle(ErrBits.LIFECYCLE_ESCALATION)
