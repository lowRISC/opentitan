# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from riscvmodel.insn import *

from .isa import *
from .model import OTBNState, OTBNModel

@isaOTBN("loop", opcode=0b0001011, funct3=0b000)
class InstructionLOOP(InstructionLType):
    def execute(self, model: OTBNModel):
        pass

@isaOTBN("loopi", opcode=0b0001011, funct3=0b001)
class InstructionLOOPI(InstructionLIType):
    def execute(self, model: OTBNModel):
        model.state.loop_start(int(self.iter), int(self.bodysize))

@isaOTBN("bn.wsrrs", opcode=0b0001011, funct3=0b100, funct31=0, funct30=1, funct29=1, funct28=1)
class InstructionBNWSRRS(InstructionBNCSType):
    def execute(self, model: OTBNModel):
        rnd = model.state.csr_read(self.wcsr)
        model.state.wreg[self.wrd] = model.state.wreg[self.wsr] & rnd

@isaOTBN("bn.not", opcode=0b0101011, funct3=0b111, funct31=0b0)
class InstructionBNNOT(InstructionBNAType):
    def execute(self, model: OTBNModel):
        b_shifted = model.state.wreg[self.wrs2]
        model.state.wreg[self.wrd] = ~b_shifted

@isaOTBN("bn.xor", opcode=0b0101011, funct3=0b111, funct31=0b1)
class InstructionBNXOR(InstructionBNAType):
    def execute(self, model: OTBNModel):
        b_shifted = model.state.wreg[self.wrs2]
        a = model.state.wreg[self.wrs1]
        model.state.wreg[self.wrd] = a ^ b_shifted
