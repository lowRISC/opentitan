# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional, Tuple

from .isa import OTBNInsn
from .state import OTBNState
from .stats import ExecutionStats
from .trace import Trace

_TEST_RND_DATA = \
    0x99999999_99999999_99999999_99999999_99999999_99999999_99999999_99999999


class OTBNSim:
    def __init__(self) -> None:
        self.state = OTBNState()
        self.program = []  # type: List[OTBNInsn]
        self.stats = None  # type: Optional[ExecutionStats]

    def load_program(self, program: List[OTBNInsn]) -> None:
        self.program = program.copy()

    def load_data(self, data: bytes) -> None:
        self.state.dmem.load_le_words(data)

    def start(self) -> None:
        '''Prepare to start the execution.

        Use run() or step() to actually execute the program.

        '''
        self.stats = ExecutionStats(self.program)
        self.state.start()

    def run(self, verbose: bool, collect_stats: bool) -> int:
        '''Run until ECALL.

        Return the number of cycles taken.

        '''
        insn_count = 0
        # ISS will stall at start until URND data is valid, immediately set it
        # valid when in free running mode as nothing else will.
        self.state.set_urnd_reseed_complete()
        while self.state.running:
            self.step(verbose, collect_stats)
            insn_count += 1

            if self.state.wsrs.RND.pending_request:
                # If an instruction requests RND data, make it available
                # immediately.
                self.state.wsrs.RND.set_unsigned(_TEST_RND_DATA)

        return insn_count

    def step(self,
             verbose: bool,
             collect_stats: bool) -> Tuple[Optional[OTBNInsn], List[Trace]]:
        '''Run a single instruction.

        Returns the instruction, together with a list of the architectural
        changes that have happened. If the model isn't currently running,
        returns no instruction and no changes.

        '''
        if not self.state.running:
            return (None, [])

        assert self.stats is not None

        # Program counter before commit
        pc_before = self.state.pc

        word_pc = self.state.pc >> 2
        if word_pc >= len(self.program):
            raise RuntimeError('Trying to execute instruction at address '
                               '{:#x}, but the program is only {:#x} '
                               'bytes ({} instructions) long. Since there '
                               'are no architectural contents of the '
                               'memory here, we have to stop.'
                               .format(self.state.pc,
                                       4 * len(self.program),
                                       len(self.program)))
        insn = self.program[word_pc]

        sim_stalled = self.state.non_insn_stall
        if not sim_stalled:
            # Instruction can stall sim by returning False from `pre_execute`
            sim_stalled = not insn.pre_execute(self.state)

        if sim_stalled:
            self.state.commit(sim_stalled=True)
            disasm = '(stall)'
            changes = []

            if collect_stats:
                self.stats.record_stall()
        else:
            self.state.pre_insn(insn.affects_control)
            insn.execute(self.state)
            self.state.post_insn()

            if collect_stats:
                self.stats.record_insn(insn, self.state)

            if self.state.pending_halt:
                # We've reached the end of the run (either because of an ECALL
                # instruction or an error).
                self.state.stop()

            changes = self.state.changes()

            # Only commit() may change the program counter.
            assert pc_before == self.state.pc

            self.state.commit(sim_stalled=False)

            disasm = insn.disassemble(pc_before)

        if verbose:
            self._print_trace(pc_before, disasm, changes)

        return (None if sim_stalled else insn, changes)

    def dump_data(self) -> bytes:
        return self.state.dmem.dump_le_words()

    def _print_trace(self, pc: int, disasm: str, changes: List[Trace]) -> None:
        '''Print a trace of the current instruction'''
        changes_str = ', '.join([t.trace() for t in changes])
        print('{:08x} | {:45} | [{}]'.format(pc, disasm, changes_str))
