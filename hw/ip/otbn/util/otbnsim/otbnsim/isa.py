# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from riscvmodel.isa import Instruction, InstructionFunct3Type, Field
from riscvmodel.variant import Variant
from riscvmodel.model import State
from riscvmodel.types import Immediate

from .variant import RV32IXotbn

from enum import IntEnum
from abc import ABCMeta


class InstructionFunct2Type(Instruction):
    field_funct2 = Field(name="funct2",
                         base=12,
                         size=2,
                         description="",
                         static=True)


class InstructionFunct31Type(Instruction):
    field_funct31 = Field(name="funct31",
                          base=31,
                          size=1,
                          description="",
                          static=True)


class InstructionFunct30Type(Instruction):
    field_funct30 = Field(name="funct30",
                          base=30,
                          size=1,
                          description="",
                          static=True)


class InstructionW3Type(Instruction):
    field_wrd = Field(name="wrd", base=7, size=5)
    field_wrs1 = Field(name="wrs1", base=15, size=5)
    field_wrs2 = Field(name="wrs2", base=20, size=5)


class InstructionFGType(Instruction):
    field_fg = Field(
        name="fg",
        base=31,
        size=1,
        description="Flag group to use. Defaults to 0.\n\nValid range: 0..1")


class InstructionShiftType(Instruction):
    field_shift_type = Field(
        name="shift_type",
        base=30,
        size=1,
        description="The direction of an optional shift applied to <wrs2>.")
    field_shift_bytes = Field(
        name="shift_bytes",
        base=25,
        size=5,
        description=
        "Number of bytes by which to shift <wrs2>. Defaults to 0.\n\nValid range: 0..31"
    )


class InstructionLType(InstructionFunct2Type):
    isa_format_id = "L"

    asm_arg_signature = "<iter>, <bodysize>"

    field_rs1 = Field(name="rs1", base=15, size=5, description="")
    field_bodysize = Field(name="bodysize", base=20, size=12, description="")

    def __init__(self, rs1: int = None, bodysize: int = None):
        super().__init__()
        self.rs1 = rs1
        self.bodysize = Immediate(bits=12, signed=False, init=bodysize)

    def randomize(self, variant: Variant):
        self.rs1 = randrange(0, variant.intregs)
        self.bodysize.randomize()

    def __str__(self):
        return "{} x{}, {}".format(self.mnemonic, self.rs1, self.bodysize)


class InstructionLIType(InstructionFunct2Type):
    isa_format_id = "LI"

    asm_arg_signature = "<rs1>, <bodysize>"

    field_iter = Field(name="iter", base=7, size=5, description="")
    field_bodysize = Field(name="bodysize", base=20, size=12, description="")

    def __init__(self, iter: int = None, bodysize: int = None):
        super().__init__()
        self.iter = Immediate(bits=10, signed=False, init=iter)
        self.bodysize = Immediate(bits=12, signed=False, init=bodysize)

    def ops_from_list(self, ops):
        self.iter.set(int(ops[0]))
        self.bodysize.set(int(ops[1]))

    def __str__(self):
        return "{} {}, {}".format(self.mnemonic, self.iter, self.bodysize)


class ShiftType(IntEnum):
    LSL = 0  # logical shift left
    LSR = 1  # logical shift right


def ShiftReg(reg, shift_type, shift_bytes):
    if shift_type == ShiftType.LSL:
        return reg << (shift_bytes.value << 3)
    else:
        return reg >> (shift_bytes.value << 3)


class InstructionBNAType(InstructionFunct3Type,
                         InstructionFunct31Type,
                         InstructionShiftType,
                         InstructionW3Type,
                         metaclass=ABCMeta):
    """
    :param wrd: Name of the destination WDR
    :param wrs1: Name of the first source WDR
    :param wrs2: Name of the second source WDR
    :param shift_type: The direction of an optional shift applied to <wrs2>.
    :param shift_bytes: Number of bytes by which to shift <wrs2>. Defaults to 0. Valid range: 0..31.
    """
    isa_format_id = "BNA"

    asm_arg_signature = "<wrd>, <wrs1>, <wrs2> [, <shift_type> <shift_bytes>B]"

    def __init__(self,
                 wrd: int = None,
                 wrs1: int = None,
                 wrs2: int = None,
                 shift_bytes: int = 0,
                 shift_type: int = ShiftType.LSL):
        super().__init__()
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.shift_bytes = Immediate(bits=5,
                                     signed=False,
                                     init=shift_bytes or 0)
        self.shift_type = shift_type

    def ops_from_list(self, ops):
        self.wrd = int(ops[0][1:])
        self.wrs1 = int(ops[1][1:])
        self.wrs2 = int(ops[2][1:])
        if len(ops) > 3:
            self.shift_bytes.set(int(ops[4][:-1]))
            self.shift_type = ShiftType.LSL if ops[3] == "<<" else ShiftType.LSR

    def __str__(self):
        asm = "{} w{}, w{}, w{}".format(self.mnemonic, self.wrd, self.wrs1,
                                        self.wrs2)
        if int(self.shift_bytes) > 0:
            asm += ", {} {}B".format(
                "<<" if self.shift_type == ShiftType.LSL else ">>",
                self.shift_bytes)
        return asm


class InstructionBNANType(InstructionFunct3Type, InstructionFunct31Type,
                          InstructionShiftType):
    isa_format_id = "BNAN"

    asm_arg_signature = "<wrd>, <wrs1> [, <shift_type> <shift_bytes>B]"

    field_wrd = Field(name="wrd", base=7, size=5, description="")
    field_wrs1 = Field(name="wrs1", base=20, size=5, description="")

    def __init__(self,
                 wrd: int = None,
                 wrs1: int = None,
                 shift_bytes: int = 0,
                 shift_type: int = ShiftType.LSL):
        super().__init__()
        self.wrd = wrd
        self.wrs1 = wrs1
        self.shift_bytes = Immediate(bits=5, signed=False, init=shift_bytes)
        self.shift_type = shift_type

    def ops_from_list(self, ops):
        self.wrd = int(ops[0][1:])
        self.wrs1 = int(ops[1][1:])
        if len(ops) > 2:
            self.shift_bytes.set(int(ops[3][:-1]))
            self.shift_type = ShiftType.LSL if ops[2] == "<<" else ShiftType.LSR

    def __str__(self):
        return "{} w{}, w{}".format(self.mnemonic, self.wrd, self.wrs1)


class InstructionBNCSType(InstructionFunct3Type, InstructionFunct31Type):
    isa_format_id = "BNCS"

    asm_arg_signature = "<wrd>, <wsr>, <wrs>"

    field_wrd = Field(name="wrd", base=7, size=5)
    field_wrs = Field(name="wrs", base=15, size=5)
    field_wsr = Field(name="wsr", base=20, size=8)

    def __init__(self, wrd: int = None, wsr: int = None, wrs: int = None):
        super().__init__()
        self.wrd = wrd
        self.wrs = wrs
        self.wsr = Immediate(bits=8, signed=False, init=wrs)

    def ops_from_list(self, ops):
        self.wrd = int(ops[0][1:])
        self.wrs = int(ops[2][1:])
        self.wsr.set(int(ops[1], 0))

    def __str__(self):
        return "{} w{}, {}, w{}".format(self.mnemonic, self.wrd, self.wsr,
                                        self.wrs)


class InstructionBNAFType(InstructionFunct3Type, InstructionW3Type,
                          InstructionFGType, InstructionShiftType):

    isa_format_id = "BNAF"

    asm_arg_signature = "<wrd>, <wrs1>, <wrs2>[<shift_type> <shift_bytes>B] [, FG<flag_group>]"

    def __init__(self,
                 wrd: int = None,
                 wrs1: int = None,
                 wrs2: int = None,
                 shift_bytes: int = 0,
                 shift_type: int = ShiftType.LSL,
                 fg: int = 0):
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.shift_bytes = Immediate(bits=5, signed=False, init=shift_bytes)
        self.shift_type = shift_type
        self.fg = fg

    def ops_from_list(self, ops):
        self.wrd = int(ops[0][1:])
        self.wrs1 = int(ops[1][1:])
        self.wrs2 = int(ops[2][1:])
        if len(ops) > 3:
            off = 3
            if ops[3] == "<<":
                self.shift_type = ShiftType.LSL if ops[
                    3] == "<<" else ShiftType.LSR
                self.shift_bytes.set(int(ops[4][:-1]))
                off += 2
            if len(ops) > off:
                self.fg = int(ops[off][2:])

    def __str__(self):
        shift = "{} {}B".format(
            "<<" if self.shift_type == ShiftType.LSL else ">>",
            self.shift_bytes)
        return "{} w{}, w{}, w{}{}, FG{}".format(self.mnemonic, self.wrd,
                                                 self.wrs1, self.wrs2, shift,
                                                 self.fg)


class InstructionBNAIType(InstructionFunct3Type, InstructionFGType,
                          InstructionFunct30Type):
    isa_format_id = "BNAI"

    asm_arg_signature = "<wrd>, <wrs1>, <imm> [, FG<flag_group>]"

    field_wrd = Field(name="wrd", base=7, size=5)
    field_wrs1 = Field(name="wrs1", base=15, size=5)
    field_imm = Field(name="imm", base=20, size=10)
    field_sign = Field(name="sign", base=30, size=1)

    def __init__(self,
                 wrd: int = None,
                 wrs1: int = None,
                 imm: int = None,
                 fg: int = 0):
        self.wrd = wrd
        self.wrs1 = wrs1
        self.imm = Immediate(bits=10, signed=False, init=imm)
        self.shift_type = shift_type
        self.fg = fg

    def ops_from_list(self, ops):
        print(ops)
        self.wrd = int(ops[0][1:])
        self.wrs1 = int(ops[1][1:])
        self.wrs2 = int(ops[2], 0)
        if len(ops) > 3:
            self.fg = int(ops[3])


class InstructionBNAMType(InstructionFunct3Type, InstructionW3Type,
                          InstructionFunct30Type):
    isa_format_id = "BNAM"

    asm_arg_signature = "<wrd>, <wrs1>, <wrs2>"

    def __init__(self, wrd: int = None, wrs1: int = None, wrs2: int = None):
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs1 = wrs1

    def ops_from_list(self, ops):
        print(ops)
        self.wrd = int(ops[0][1:])
        self.wrs1 = int(ops[1][1:])
        self.wrs2 = int(ops[2][1:])

    def __str__(self):
        return "{} w{}, w{}, w{}".format(self.mnemonic, self.wrd, self.wrs1,
                                         self.wrs2)


class InstructionBNAQType(InstructionW3Type):
    isa_format_id = "BNAQ"

    asm_arg_signature = "[<wb_variant>][<zero_acc>] [<wrd><wrd_hwsel>,] <wrs1>.<wrs1_qwsel>, <wrs2>.<wrs2_qwsel>, <acc_shift_imm>"

    @classmethod
    def asm_signature(cls):
        return cls.mnemonic + cls.asm_arg_signature

    field_wb_variant = Field(name="wb_variant",
                             base=30,
                             size=2,
                             description="""
Result writeback instruction variant. If no writeback variant is chosen, no
destination register is written, and the multiplication result is only stored in
the accumulator.

Valid values:

* .S0 (value 0): Shift out the lower half-word of the value stored in the
  accumulator to a WLEN/2-sized half-word of the destination WDR. The
  destination half-word is selected by the wrd_hwsel field.

* .W0 (value 1): Write the value stored in the accumulator to the destination
  WDR.""")
    field_zero_acc = Field(name="zero_acc",
                           base=12,
                           size=1,
                           description="""
Zero the accumulator before accumulating the multiply result.

To specify, use the literal syntax .Z""")
    field_wrd_hwsel = Field(name="wrd_hwsel", base=29, size=1, description="")
    field_wrs1_qwsel = Field(name="wrs1_qwsel",
                             base=27,
                             size=2,
                             description="")
    field_wrs2_qwsel = Field(name="wrs2_qwsel",
                             base=25,
                             size=2,
                             description="")
    field_acc_shift_imm = Field(name="acc_shift_imm",
                                base=13,
                                size=2,
                                description="")

    def __init__(self,
                 wrd: int = 0,
                 wrs1: int = None,
                 wrs2: int = None,
                 wb_variant: int = 0,
                 zero_acc: bool = False,
                 wrd_hwsel: int = 0,
                 wrs1_qwsel: int = None,
                 wrs2_qwsel: int = None,
                 acc_shift_imm: int = None):
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.wb_variant = wb_variant
        self.zero_acc = zero_acc
        self.wrd_hwsel = wrd_hwsel
        self.wrs1_qwsel = wrs1_qwsel
        self.wrs2_qwsel = wrs2_qwsel
        self.acc_shift_imm = acc_shift_imm

    def ops_from_list(self, ops):
        off = 0
        if ops[off] in ["so", "wo"]:
            self.wb_variant = 1 if ops[0] == "so" else 2
            off += 1
        if ops[off] == "z":
            self.zero_acc = True
            off += 1
        if len(ops[off:]) > 3:
            assert self.wb_variant is not None
            wrd = ops[off]
            self.wrd = int(wrd[1:wrd.rfind(".")])
            self.wrd_hwsel = 1 if wrd[wrd.rfind(".") + 1] == "u" else 0
            off += 1
        wrs = ops[off]
        self.wrs1 = int(wrs[1:wrs.rfind(".")])
        self.wrs1_qwsel = int(wrs[wrs.rfind(".") + 1])
        wrs = ops[off + 1]
        self.wrs2 = int(wrs[1:wrs.rfind(".")])
        self.wrs2_qwsel = int(wrs[wrs.rfind(".") + 1])
        self.acc_shift_imm = int(ops[off + 2]) >> 6

    def __str__(self):
        istr = self.mnemonic
        if self.wb_variant > 0:
            istr += ".so" if self.wb_variant == 1 else ".wo"
        if self.zero_acc:
            istr += ".z"
        istr += " "
        if self.wb_variant > 0:
            istr += "w{}".format(self.wrd)
            if self.wb_variant == 1:
                istr += ".u" if self.wrd_hwsel == 1 else ".l"
            istr += ", "
        istr += "w{}.{}, ".format(self.wrs1, self.wrs1_qwsel)
        istr += "w{}.{}, ".format(self.wrs2, self.wrs2_qwsel)
        istr += str(self.acc_shift_imm * 64)
        return istr


class InstructionBNRType(InstructionW3Type, InstructionFunct2Type):
    isa_format_id = "BNR"

    asm_arg_signature = "<wrd>, <wrs1>, <wrs2> >> <imm>"

    field_imm = Field(name="imm", base=[14, 25], size=[1, 7], description="")

    def __init__(self,
                 wrd: int = None,
                 wrs1: int = None,
                 wrs2: int = None,
                 imm: int = None):
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.imm = Immediate(bits=8, signed=False, init=imm)

    def ops_from_list(self, ops):
        self.wrd = int(ops[0][1:])
        self.wrs1 = int(ops[1][1:])
        self.wrs2 = int(ops[2][1:])
        self.imm.set_from_bits(int(ops[4]))

    def __str__(self):
        return "{} w{}, w{}, w{} >> {}".format(self.mnemonic, self.wrd,
                                               self.wrs1, self.wrs2, self.imm)


class InstructionBNSType(InstructionW3Type, InstructionFunct3Type,
                         InstructionFGType):
    isa_format_id = "BNS"

    asm_arg_signature = "<wrd>, <wrs1>, <wrs2>, [FG<flag_group>.]flag"

    field_flag = Field(name="flag", base=25, size=2, description="")

    def __init__(self,
                 wrd: int = None,
                 wrs1: int = None,
                 wrs2: int = None,
                 fg: int = 0,
                 flag: int = None):
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.fg = fg
        self.flag = flag

    def ops_from_list(self, ops):
        self.wrd = int(ops[0][1:])
        self.wrs1 = int(ops[1][1:])
        self.wrs2 = int(ops[2][1:])
        if len(ops) > 4:
            self.fg = int(ops[3])
            self.flag = int(ops[4])
        else:
            self.flag = int(ops[3])

    def __str__(self):
        return "{} w{}, w{}, w{}{}, FG{}".format(self.mnemonic, self.wrd,
                                                 self.wrs1, self.wrs2, self.fg,
                                                 self.flag)


class InstructionBNCType(InstructionFunct3Type, InstructionFGType,
                         InstructionShiftType):
    isa_format_id = "BNC"

    asm_arg_signature = "<wrs1>, <wrs2>[<shift_type> <shift_bytes>B] [, FG<flag_group>]"

    field_wrs1 = Field(name="wrs1", base=15, size=5)
    field_wrs2 = Field(name="wrs2", base=20, size=5)

    def __init__(self,
                 wrs1: int = None,
                 wrs2: int = None,
                 shift_bytes: int = 0,
                 shift_type: int = ShiftType.LSL,
                 fg: int = 0):
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.shift_bytes = Immediate(bits=5, signed=False, init=shift_bytes)
        self.shift_type = shift_type
        self.fg = fg

    def ops_from_list(self, ops):
        self.wrs1 = int(ops[0][1:])
        self.wrs2 = int(ops[1][1:])
        if len(ops) > 2:
            off = 2
            if ops[2] == "<<":
                self.shift_type = ShiftType.LSL if ops[
                    2] == "<<" else ShiftType.LSR
                self.shift_bytes.set(int(ops[3][:-1]))
                off += 2
            if len(ops) > off:
                self.fg = int(ops[off][2:])

    def __str__(self):
        shift = "{} {}B".format(
            "<<" if self.shift_type == ShiftType.LSL else ">>",
            self.shift_bytes)
        return "{} w{}, w{}{}, FG{}".format(self.mnemonic, self.wrs1,
                                            self.wrs2, shift, self.fg)


class InstructionBNIType(InstructionFunct3Type):
    isa_format_id = "BNI"

    asm_arg_signature = "<grd>[<grd_inc>], <offset>(<grs1>[<grs1_inc>])"

    field_rd = Field(name="rd", base=7, size=5)
    field_rs = Field(name="rs", base=15, size=5)
    field_imm = Field(name="imm", base=22, size=10)
    field_rd_inc = Field(name="rd_inc", base=20, size=1)
    field_rs_inc = Field(name="rs_inc", base=21, size=1)

    def __init__(self,
                 rd: int = None,
                 rs: int = None,
                 imm: int = None,
                 rd_inc: bool = False,
                 rs_inc: bool = False):
        self.rd = rd
        self.rs = rs
        self.imm = Immediate(bits=10, signed=True)
        self.rd_inc = rd_inc
        self.rs_inc = rs_inc

    def ops_from_list(self, ops):
        self.rd = int(ops[0][1:])
        self.imm.set(int(ops[1]))
        self.rs = int(ops[2][1:])

    def __str__(self):
        return "{} x{}, {}(x{})".format(self.mnemonic, self.rd, self.imm,
                                        self.rs)


class InstructionBNISType(InstructionFunct3Type):
    isa_format_id = "BNIS"

    asm_arg_signature = "<grs1>[<grs1_inc>], <offset>(<grs2>[<grs2_inc>])"

    field_rs1 = Field(name="rs1", base=7, size=5)
    field_rs2 = Field(name="rs2", base=15, size=5)
    field_imm = Field(name="imm", base=22, size=10)
    field_rs1_inc = Field(name="rs1_inc", base=20, size=1)
    field_rs2_inc = Field(name="rs2_inc", base=21, size=1)

    def __init__(self,
                 rs1: int = None,
                 rs2: int = None,
                 imm: int = None,
                 rs1_inc: bool = False,
                 rs2_inc: bool = False):
        self.rs1 = rs1
        self.rs2 = rs2
        self.imm = Immediate(bits=10, signed=True)
        self.rs1_inc = rs1_inc
        self.rs2_inc = rs2_inc

    def ops_from_list(self, ops):
        self.rs1 = int(ops[0][1:])
        self.imm.set(int(ops[1]))
        self.rs2 = int(ops[2][1:])

    def __str__(self):
        return "{} x{}, {}(x{})".format(self.mnemonic, self.rs1, self.imm,
                                        self.rs2)


class InstructionBNMVType(InstructionFunct3Type, InstructionFunct31Type):
    isa_format_id = "BNMV"

    asm_arg_signature = "<wrd>, <wrs>"

    field_wrd = Field(name="wrd", base=7, size=5)
    field_wrs = Field(name="wrs", base=15, size=5)

    def __init__(self, wrd: int = None, wrs: int = None):
        self.wrd = wrd
        self.wrs = wrs

    def ops_from_list(self, ops):
        self.wrd = ops[0][1:]
        self.wrs = ops[1][1:]

    def __str__(self):
        return "{} w{}, w{}".format(self.mnemonic, self.wrd, self.wrs)


class InstructionBNMVRType(InstructionFunct3Type, InstructionFunct31Type):
    isa_format_id = "BNMVR"

    asm_arg_signature = "<rd>[<rd_inc>], <rs>[<rs_inc>]"

    field_rd = Field(name="rd", base=7, size=5)
    field_rs = Field(name="rs", base=15, size=5)
    field_rd_inc = Field(name="rd_inc", base=20, size=1)
    field_rs_inc = Field(name="rs_inc", base=21, size=1)

    def __init__(self,
                 rd: int = None,
                 rs: int = None,
                 rd_inc: bool = False,
                 rs_inc: bool = False):
        self.rd = rd
        self.rs = rs
        self.rd_inc = rd_inc
        self.rs_inc = rs_inc

    def ops_from_list(self, ops):
        self.rd_inc = ops[0].endswith("++")
        self.rd = int(ops[0][1:-2] if self.rd_inc else ops[0][1:])
        self.rs_inc = ops[1].endswith("++")
        self.rs = int(ops[1][1:-2] if self.rs_inc else ops[1][1:])

    def __str__(self):
        dpp = "++" if self.rd_inc else ""
        spp = "++" if self.rs_inc else ""
        return "{} x{}{}, x{}{}".format(self.mnemonic, self.rd, dpp, self.rs,
                                        spp)
