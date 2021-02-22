# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional, Tuple

from .isa import OTBNInsn
from .state import OTBNState
from .trace import Trace


class OTBNSim:
    def __init__(self) -> None:
        self.state = OTBNState()
        self.program = []  # type: List[OTBNInsn]

    def load_program(self, program: List[OTBNInsn]) -> None:
        self.program = program.copy()

    def load_data(self, data: bytes) -> None:
        self.state.dmem.load_le_words(data)

    def run(self, verbose: bool) -> int:
        '''Run until ECALL.

        Return the number of cycles taken.

        '''
        insn_count = 0
        while self.state.running:
            self.step(verbose)
            insn_count += 1

        return insn_count

    def step(self, verbose: bool) -> Tuple[Optional[OTBNInsn], List[Trace]]:
        '''Run a single instruction.

        Returns the instruction, together with a list of the architectural
        changes that have happened. If the model isn't currently running,
        returns no instruction and no changes.

        '''
        if not self.state.running:
            return (None, [])

        was_stalled = self.state.stalled
        pc_before = self.state.pc

        if was_stalled:
            insn = None
            changes = []
            self.state.commit()
        else:
            word_pc = int(self.state.pc) >> 2
            if word_pc >= len(self.program):
                raise RuntimeError('Trying to execute instruction at address '
                                   '{:#x}, but the program is only {:#x} '
                                   'bytes ({} instructions) long. Since there '
                                   'are no architectural contents of the '
                                   'memory here, we have to stop.'
                                   .format(int(self.state.pc),
                                           4 * len(self.program),
                                           len(self.program)))
            insn = self.program[word_pc]

            if insn.insn.cycles > 1:
                self.state.add_stall_cycles(insn.insn.cycles - 1)

            self.state.pre_insn(insn.affects_control)
            insn.execute(self.state)
            self.state.post_insn()

            if self.state.pending_halt:
                # Roll back any pending state changes, ensuring that a faulting
                # instruction doesn't actually do anything (this also aborts an
                # ECALL instruction, but that doesn't really matter because it
                # doesn't have any side-effects). Also generate a change that
                # sets an appropriate error bits in the external ERR_CODE
                # register and clears the busy flag.
                self.state.stop()
                changes = self.state.changes()
            else:
                changes = self.state.changes()
                self.state.commit()

        if verbose:
            disasm = ('(stall)' if insn is None
                      else insn.disassemble(pc_before))
            self._print_trace(pc_before, disasm, changes)

        return (insn, changes)

    def dump_data(self) -> bytes:
        return self.state.dmem.dump_le_words()

    def _print_trace(self, pc: int, disasm: str, changes: List[Trace]) -> None:
        '''Print a trace of the current instruction to verbose_file'''
        changes_str = ', '.join([t.trace() for t in changes])
        print('{:08x} | {:45} | [{}]'.format(pc, disasm, changes_str))
