# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from riscvmodel.insn import *

from .isa import *
from .model import OTBNState

@isaOTBN("loop", opcode=0b0001011, funct3=0b000)
class InstructionLOOP(InstructionLType):
    def execute(self, model: State):
        pass

@isaOTBN("loopi", opcode=0b0001011, funct3=0b001)
class InstructionLOOPI(InstructionLIType):
    def execute(self, model: OTBNState):
        model.state.loop_start(int(self.iter), int(self.bodysize))
