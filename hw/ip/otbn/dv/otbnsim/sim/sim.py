# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import struct
from typing import List

from .isa import OTBNInsn
from .model import OTBNModel


class OTBNSim:
    def __init__(self, model: OTBNModel):
        self.model = model
        self.program = []  # type: List[OTBNInsn]

    def load_program(self, program: List[OTBNInsn]) -> None:
        self.program = program.copy()

    def load_data(self, data: bytes) -> None:
        # Explicitly zero-pad data to a multiple of 4 bytes if necessary
        if len(data) & 3:
            data += b'0' * (4 - (len(data) & 3))

        mem = self.model.state.memory.memory
        for word_idx, int_val in enumerate(struct.iter_unpack('<I', data)):
            mem[word_idx] = int_val[0]

    def run(self, start_addr: int) -> int:
        '''Start a simulation at reset_addr and run until ECALL.

        Return the number of instructions executed.

        '''
        self.model.state.reset(pc=start_addr)
        self.model.state.start()
        insn_count = 0
        while self.model.state.running:
            self.step()
            insn_count += 1

        return insn_count

    def step(self) -> List[str]:
        '''Run a single instruction.

        Returns a list of the architectural changes that have happened.

        '''
        if not self.model.state.running:
            return []

        word_pc = int(self.model.state.pc) >> 2

        if word_pc >= len(self.program):
            raise RuntimeError('Trying to execute instruction at address '
                               '{:#x}, but the program is only {:#x} bytes '
                               '({} instructions) long. Since there is no '
                               'architectural contents of the memory here, we '
                               'have to stop.'
                               .format(int(self.model.state.pc),
                                       4 * len(self.program),
                                       len(self.program)))
        insn = self.program[word_pc]

        self.model.state.pc += 4
        insn.execute(self.model)
        self.model.post_insn()

        changes = self.model.state.changes()
        if self.model.verbose:
            disasm = insn.disassemble(int(self.model.state.pc))
            self.model.print_trace(disasm)

        self.model.state.commit()
        return changes

    def dump_data(self) -> bytes:
        data = b""
        mem = self.model.state.memory.memory
        for a in mem:
            data += struct.pack("<L", mem[a])
        return data
