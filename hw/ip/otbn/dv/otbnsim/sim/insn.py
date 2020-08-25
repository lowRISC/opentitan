# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from riscvmodel.insn import isa  # type: ignore

from .isa import (InstructionBNAFType,
                  InstructionBNAIType,
                  InstructionBNAMType,
                  InstructionBNANType,
                  InstructionBNAQType,
                  InstructionBNAType,
                  InstructionBNCSType,
                  InstructionBNCType,
                  InstructionBNISType,
                  InstructionBNIType,
                  InstructionBNMVRType,
                  InstructionBNMVType,
                  InstructionBNRType,
                  InstructionBNSType,
                  InstructionLIType,
                  InstructionLType,
                  ShiftReg)
from .model import OTBNModel
from .variant import RV32IXotbn


@isa("loop", RV32IXotbn, opcode=0b1111011, funct2=0b00)
class InstructionLOOP(InstructionLType):
    """
    Loop (indirect)

    Repeat a sequence of code multiple times. The number of iterations is a GPR
    value. The length of the loop is given as immediate.

    Alternative assembly notation: The size of the loop body is given by the
    number of instructions in the parentheses.

    LOOP <grs> (
      # loop body
    )
    """
    def execute(self, model: OTBNModel) -> None:
        assert self.rs1 is not None
        model.state.loop_start(int(model.state.intreg[self.rs1]),
                               int(self.bodysize))


@isa("loopi", RV32IXotbn, opcode=0b1111011, funct2=0b01)
class InstructionLOOPI(InstructionLIType):
    """
    Loop Immediate

    Repeat a sequence of code multiple times. The number of iterations is given
    as an immediate, as is the length of the loop. The number of iterations must
    be larger than zero.

    Alternative assembly notation. The size of the loop body is given by the
    number of instructions in the parentheses.

    LOOPI <iterations> (
      # loop body
    )

    """
    def execute(self, model: OTBNModel) -> None:
        model.state.loop_start(int(self.iter), int(self.bodysize))


@isa("bn.add", RV32IXotbn, opcode=0b0101011, funct3=0b000)
class InstructionBNADD(InstructionBNAFType):
    """
    Add

    Adds two WDR values, writes the result to the destination WDR and updates
    flags. The content of the second source WDR can be shifted by an immediate
    before it is consumed by the operation.
    """
    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1].unsigned())
        b_shifted = ShiftReg(int(model.state.wreg[self.wrs2].unsigned()),
                             self.shift_type, self.shift_bytes)
        (result, flags) = model.add_with_carry(a, b_shifted, 0)
        model.state.wreg[self.wrd] = result
        model.state.flags[self.fg] = flags


@isa("bn.addc", RV32IXotbn, opcode=0b0101011, funct3=0b010)
class InstructionBNADDC(InstructionBNAFType):
    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1].unsigned())
        b_shifted = ShiftReg(int(model.state.wreg[self.wrs2].unsigned()),
                             self.shift_type, self.shift_bytes)
        (result, flags) = model.add_with_carry(a, b_shifted,
                                               model.state.flags[self.fg].C)
        model.state.wreg[self.wrd] = result
        model.state.flags[self.fg] = flags


@isa("bn.addi", RV32IXotbn, opcode=0b0101011, funct3=0b100, funct30=0)
class InstructionBNADDI(InstructionBNAIType):
    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1].unsigned())
        b = int(self.imm)
        (result, flags) = model.add_with_carry(a, b, 0)
        model.state.wreg[self.wrd] = result
        model.state.flags[self.fg] = flags


@isa("bn.addm", RV32IXotbn, opcode=0b0101011, funct3=0b101, funct30=0)
class InstructionBNADDM(InstructionBNAMType):
    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1].unsigned())
        b = int(model.state.wreg[self.wrs2].unsigned())
        (result, _) = model.add_with_carry(a, b, 0)
        if result >= int(model.state.mod):
            result -= int(model.state.mod)
        model.state.wreg[self.wrd] = result


@isa("bn.mulqacc", RV32IXotbn, opcode=0b0111011)
class InstructionBNMULQACC(InstructionBNAQType):
    """
    Quarter-word Multiply and Accumulate

    Multiplies two WLEN/4 WDR values and adds the result to an accumulator after
    shifting it. Optionally shifts some/all of the resulting accumulator value
    out to a destination WDR.
    """
    def execute(self, model: OTBNModel) -> None:
        assert self.wrs1 is not None
        assert self.wrs2 is not None
        assert self.wrs1_qwsel is not None
        assert self.wrs2_qwsel is not None
        assert self.acc_shift_imm is not None

        a_qw = model.get_wr_quarterword(self.wrs1, self.wrs1_qwsel)
        b_qw = model.get_wr_quarterword(self.wrs2, self.wrs2_qwsel)

        mul_res = a_qw * b_qw

        acc = int(model.state.single_regs['acc'])

        if (self.zero_acc):
            acc = 0

        acc += (mul_res << (self.acc_shift_imm * 64))

        if self.wb_variant > 0:
            if self.wb_variant == 1:
                model.set_wr_halfword(self.wrd, acc, self.wrd_hwsel)
                acc = acc >> 128
            elif self.wb_variant == 2:
                model.state.wreg[self.wrd].set(acc)

        model.state.single_regs['acc'].update(acc)


@isa("bn.sub", RV32IXotbn, opcode=0b0101011, funct3=0b001)
class InstructionBNSUB(InstructionBNAFType):
    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b_shifted = ShiftReg(int(model.state.wreg[self.wrs2]), self.shift_type,
                             self.shift_bytes)
        (result, flags) = model.add_with_carry(a, -b_shifted, 0)
        model.state.wreg[self.wrd] = result
        model.state.flags[self.fg] = flags


@isa("bn.subb", RV32IXotbn, opcode=0b0101011, funct3=0b011)
class InstructionBNSUBB(InstructionBNAFType):
    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b_shifted = ShiftReg(int(model.state.wreg[self.wrs2]), self.shift_type,
                             self.shift_bytes)
        (result,
         flags) = model.add_with_carry(a, -b_shifted,
                                       1 - model.state.flags[self.fg].C)
        model.state.wreg[self.wrd] = result
        model.state.flags[self.fg] = flags


@isa("bn.subi", RV32IXotbn, opcode=0b0101011, funct3=0b100, funct30=1)
class InstructionBNSUBI(InstructionBNAIType):
    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b = int(self.imm)
        (result, flags) = model.add_with_carry(a, -b, 0)
        model.state.wreg[self.wrd] = result
        model.state.flags[self.fg] = flags


@isa("bn.subm", RV32IXotbn, opcode=0b0101011, funct3=0b101, funct30=1)
class InstructionBNSUBM(InstructionBNAMType):
    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b = int(model.state.wreg[self.wrs2])
        result, _ = model.add_with_carry(a, -b, 0)
        if result >= model.state.mod:
            result -= model.state.mod
        model.state.wreg[self.wrd] = result


@isa("bn.and", RV32IXotbn, opcode=0b0101011, funct3=0b110, funct31=0)
class InstructionBNAND(InstructionBNAType):
    """
    Bitwise AND

    Performs a bitwise and operation. Takes the values stored in registers
    referenced by wrs1 and wrs2 and stores the result in the register referenced
    by wrd. The content of the second source register can be shifted by an
    immediate before it is consumed by the operation.
    """
    def execute(self, model: OTBNModel) -> None:
        assert self.shift_type is not None

        b_shifted = ShiftReg(model.state.wreg[self.wrs2],
                             self.shift_type, self.shift_bytes)
        a = model.state.wreg[self.wrs1]
        model.state.wreg[self.wrd] = a & b_shifted


@isa("bn.or", RV32IXotbn, opcode=0b0101011, funct3=0b110, funct31=1)
class InstructionBNOR(InstructionBNAType):
    """
    Bitwise OR

    Performs a bitwise or operation. Takes the values stored in WDRs referenced
    by wrs1 and wrs2 and stores the result in the WDR referenced by wrd. The
    content of the second source WDR can be shifted by an immediate before it is
    consumed by the operation.
    """
    def execute(self, model: OTBNModel) -> None:
        assert self.shift_type is not None

        b_shifted = ShiftReg(model.state.wreg[self.wrs2],
                             self.shift_type, self.shift_bytes)
        a = model.state.wreg[self.wrs1]
        model.state.wreg[self.wrd] = a | b_shifted


@isa("bn.not", RV32IXotbn, opcode=0b0101011, funct3=0b111, funct31=0)
class InstructionBNNOT(InstructionBNANType):
    """
    Bitwise NOT

    Negates the value in <wrs>, storing the result into <wrd>. The source value
    can be shifted by an immediate before it is consumed by the operation.
    """
    def execute(self, model: OTBNModel) -> None:
        b_shifted = model.state.wreg[self.wrs1]
        model.state.wreg[self.wrd] = ~b_shifted


@isa("bn.xor", RV32IXotbn, opcode=0b0101011, funct3=0b111, funct31=1)
class InstructionBNXOR(InstructionBNAType):
    """
    Bitwise XOR.

    Performs a bitwise xor operation. Takes the values stored in WDRs referenced
    by wrs1 and wrs2 and stores the result in the WDR referenced by wrd. The
    content of the second source WDR can be shifted by an immediate before it is
    consumed by the operation.
    """
    def execute(self, model: OTBNModel) -> None:
        b_shifted = model.state.wreg[self.wrs2]
        a = model.state.wreg[self.wrs1]
        model.state.wreg[self.wrd] = a ^ b_shifted


@isa("bn.rshi", RV32IXotbn, opcode=0b1111011, funct2=0b11)
class InstructionBNRSHI(InstructionBNRType):
    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b = int(model.state.wreg[self.wrs2])
        shift_bit = int(self.imm)
        model.state.wreg[self.wrd] = (((a << 256) | b) >> shift_bit) & (
            (1 << 256) - 1)


@isa("bn.sel", RV32IXotbn, opcode=0b0001011, funct3=0b000)
class InstructionBNSEL(InstructionBNSType):
    def execute(self, model: OTBNModel) -> None:
        # self.flag gives a number (0-3), which we need to convert to a flag
        # name for use with BitflagRegister.
        assert self.flag is not None
        assert 0 <= self.flag <= 3
        flag_name = ['C', 'L', 'M', 'Z'][self.flag]

        flag_is_set = model.state.flags[self.fg].get(flag_name)
        val = model.state.wreg[self.wrs1 if flag_is_set else self.wrs2]
        model.state.wreg[self.wrd] = val


@isa("bn.cmp", RV32IXotbn, opcode=0b0001011, funct3=0b001)
class InstructionBNCMP(InstructionBNCType):
    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b_shifted = ShiftReg(int(model.state.wreg[self.wrs2]), self.shift_type,
                             self.shift_bytes)
        (_, flags) = model.add_with_carry(a, -b_shifted, 0)
        model.state.flags[self.fg] = flags


@isa("bn.cmpb", RV32IXotbn, opcode=0b0001011, funct3=0b011)
class InstructionBNCMPB(InstructionBNCType):
    def execute(self, model: OTBNModel) -> None:
        a = int(model.state.wreg[self.wrs1])
        b_shifted = ShiftReg(int(model.state.wreg[self.wrs2]), self.shift_type,
                             self.shift_bytes)
        (_, flags) = model.add_with_carry(a, -b_shifted,
                                          1 - model.state.flags[self.fg].C)
        model.state.flags[self.fg] = flags


@isa("bn.lid", RV32IXotbn, opcode=0b0001011, funct3=0b100)
class InstructionBNLID(InstructionBNIType):
    """
    Load Word (indirect source, indirect destination)

    Calculates a byte memory address by adding the offset to the value in the
    GPR grs1. The value from this memory address is then copied into the WDR
    pointed to by the value in GPR grd.

    After the operation, either the value in the GPR grs1, or the value in grd
    can be optionally incremented.

    If grs1_inc is set, the value in grs1 is incremented by the value WLEN/8
    (one word). If grd_inc is set, the value in grd is incremented by the value
    1.
    """
    def execute(self, model: OTBNModel) -> None:
        assert self.rs is not None
        assert self.rd is not None

        addr = int(model.state.intreg[self.rs] + int(self.imm))
        wrd = int(model.state.intreg[self.rd])
        word = model.load_wlen_word_from_memory(addr)
        model.state.wreg[wrd] = word


@isa("bn.sid", RV32IXotbn, opcode=0b0001011, funct3=0b101)
class InstructionBNSID(InstructionBNISType):
    """
    Store Word (indirect source, indirect destination)

    Calculates a byte memory address by adding the offset to the value in the
    GPR grs1. The value from the WDR pointed to by grs2 is then copied into the
    memory.

    After the operation, either the value in the GPR grs1, or the value in grs2
    can be optionally incremented.

    If grs1_inc is set, the value in grs1 is incremented by the value WLEN/8
    (one word). If grs2_inc is set, the value in grs2 is incremented by the
    value 1.
    """
    def execute(self, model: OTBNModel) -> None:
        assert self.rs2 is not None
        assert self.rs1 is not None

        addr = int(model.state.intreg[self.rs2] + int(self.imm))
        wrs = int(model.state.intreg[self.rs1])
        word = int(model.state.wreg[wrs])
        model.store_wlen_word_to_memory(addr, word)


@isa("bn.mov", RV32IXotbn, opcode=0b0001011, funct3=0b110, funct31=0)
class InstructionBNMOV(InstructionBNMVType):
    def execute(self, model: OTBNModel) -> None:
        model.state.wreg[self.wrd] = model.state.wreg[self.wrs]


@isa("bn.movr", RV32IXotbn, opcode=0b0001011, funct3=0b110, funct31=1)
class InstructionBNMOVR(InstructionBNMVRType):
    def execute(self, model: OTBNModel) -> None:
        assert self.rd is not None
        assert self.rs is not None
        wrd = int(model.state.intreg[self.rd])
        wrs = int(model.state.intreg[self.rs])
        model.state.wreg[wrd] = model.state.wreg[wrs]
        if self.rd_inc:
            model.state.intreg[self.rd] += 1
        if self.rs_inc:
            model.state.intreg[self.rs] += 1


@isa("bn.wsrrs", RV32IXotbn, opcode=0b0001011, funct3=0b111, funct31=0)
class InstructionBNWSRRS(InstructionBNCSType):
    """
    Atomic Read and Set Bits in WSR
    """
    def execute(self, model: OTBNModel) -> None:
        csr = model.state.wcsr_read(self.wsr)
        model.state.wreg[self.wrd] = model.state.wreg[self.wrs] & csr


@isa("bn.wsrrw", RV32IXotbn, opcode=0b0001011, funct3=0b111, funct31=1)
class InstructionBNWSRRW(InstructionBNCSType):
    def execute(self, model: OTBNModel) -> None:
        index = int(self.wsr)
        old_val = model.state.wcsr_read(index)
        new_val = model.state.wreg[self.wrs]

        model.state.wcsr_write(index, new_val)
        model.state.wreg[self.wrd] = old_val
