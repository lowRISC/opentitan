# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import IntEnum
from abc import ABCMeta
from typing import Optional, cast

from riscvmodel.isa import (Instruction,  # type: ignore
                            InstructionFunct3Type, Field)
from riscvmodel.types import Immediate  # type: ignore


class InstructionFunct2Type(Instruction):  # type: ignore
    field_funct2 = Field(name="funct2",
                         base=12,
                         size=2,
                         description="",
                         static=True)


class InstructionFunct31Type(Instruction):  # type: ignore
    field_funct31 = Field(name="funct31",
                          base=31,
                          size=1,
                          description="",
                          static=True)


class InstructionFunct30Type(Instruction):  # type: ignore
    field_funct30 = Field(name="funct30",
                          base=30,
                          size=1,
                          description="",
                          static=True)


class InstructionW3Type(Instruction):  # type: ignore
    field_wrd = Field(name="wrd", base=7, size=5)
    field_wrs1 = Field(name="wrs1", base=15, size=5)
    field_wrs2 = Field(name="wrs2", base=20, size=5)


class InstructionFGType(Instruction):  # type: ignore
    field_fg = Field(
        name="fg",
        base=31,
        size=1,
        description="Flag group to use. Defaults to 0.\n\nValid range: 0..1")


class InstructionShiftType(Instruction):  # type: ignore
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

    field_rs1 = Field(name="rs1", base=15, size=5, description="")
    field_bodysize = Field(name="bodysize", base=20, size=12, description="")

    def __init__(self,
                 rs1: Optional[int] = None,
                 bodysize: Optional[int] = None):
        super().__init__()
        self.rs1 = rs1
        self.bodysize = Immediate(bits=12, signed=False, init=bodysize)

    def __str__(self) -> str:
        return "{} x{}, {}".format(self.mnemonic, self.rs1, self.bodysize)


class InstructionLIType(InstructionFunct2Type):
    isa_format_id = "LI"

    field_iter = Field(name="iter", base=7, size=5, description="")
    field_bodysize = Field(name="bodysize", base=20, size=12, description="")

    def __init__(self,
                 iter: Optional[int] = None,
                 bodysize: Optional[int] = None):
        super().__init__()
        self.iter = Immediate(bits=10, signed=False, init=iter)
        self.bodysize = Immediate(bits=12, signed=False, init=bodysize)

    def __str__(self) -> str:
        return "{} {}, {}".format(self.mnemonic, self.iter, self.bodysize)


class ShiftType(IntEnum):
    LSL = 0  # logical shift left
    LSR = 1  # logical shift right


def ShiftReg(reg: int, shift_type: int, shift_bytes: Immediate) -> int:
    assert 0 <= int(shift_bytes)
    shift_bits = int(shift_bytes << 3)

    return (reg << shift_bits
            if shift_type == ShiftType.LSL
            else reg >> shift_bits)


class InstructionBNAType(InstructionFunct3Type,  # type: ignore
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

    def __init__(self,
                 wrd: Optional[int] = None,
                 wrs1: Optional[int] = None,
                 wrs2: Optional[int] = None,
                 shift_bytes: Optional[int] = None,
                 shift_type: ShiftType = ShiftType.LSL):
        super().__init__()
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.shift_bytes = Immediate(bits=5,
                                     signed=False,
                                     init=shift_bytes)
        self.shift_type = shift_type

    def __str__(self) -> str:
        asm = ("{} w{}, w{}, w{}"
               .format(self.mnemonic, self.wrd, self.wrs1, self.wrs2))
        if int(self.shift_bytes) > 0:
            asm += ", {} {}B".format(
                "<<" if self.shift_type == ShiftType.LSL else ">>",
                self.shift_bytes)
        return asm


class InstructionBNANType(InstructionFunct3Type,  # type: ignore
                          InstructionFunct31Type,
                          InstructionShiftType):
    isa_format_id = "BNAN"

    field_wrd = Field(name="wrd", base=7, size=5, description="")
    field_wrs1 = Field(name="wrs1", base=20, size=5, description="")

    def __init__(self,
                 wrd: Optional[int] = None,
                 wrs1: Optional[int] = None,
                 shift_bytes: int = 0,
                 shift_type: int = ShiftType.LSL):
        super().__init__()
        self.wrd = wrd
        self.wrs1 = wrs1
        self.shift_bytes = Immediate(bits=5, signed=False, init=shift_bytes)
        self.shift_type = shift_type

    def __str__(self) -> str:
        return "{} w{}, w{}".format(self.mnemonic, self.wrd, self.wrs1)


class InstructionBNCSType(InstructionFunct3Type,  # type: ignore
                          InstructionFunct31Type):
    isa_format_id = "BNCS"

    field_wrd = Field(name="wrd", base=7, size=5)
    field_wrs = Field(name="wrs", base=15, size=5)
    field_wsr = Field(name="wsr", base=20, size=8)

    def __init__(self,
                 wrd: Optional[int] = None,
                 wsr: Optional[int] = None,
                 wrs: Optional[int] = None):
        super().__init__()
        self.wrd = wrd
        self.wsr = Immediate(bits=8, signed=False, init=wsr)
        self.wsr = wrs

    def __str__(self) -> str:
        return ("{} w{}, w{}, {}"
                .format(self.mnemonic, self.wrd, self.wsr, self.wrs))


class InstructionBNAFType(InstructionFunct3Type,  # type: ignore
                          InstructionW3Type,
                          InstructionFGType,
                          InstructionShiftType):
    isa_format_id = "BNAF"

    def __init__(self,
                 wrd: Optional[int] = None,
                 wrs1: Optional[int] = None,
                 wrs2: Optional[int] = None,
                 shift_bytes: int = 0,
                 shift_type: int = ShiftType.LSL,
                 fg: int = 0):
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.shift_bytes = Immediate(bits=5, signed=False, init=shift_bytes)
        self.shift_type = shift_type
        self.fg = fg

    def __str__(self) -> str:
        shift = "{} {}B".format(
            "<<" if self.shift_type == ShiftType.LSL else ">>",
            self.shift_bytes)
        return "{} w{}, w{}, w{}{}, FG{}".format(self.mnemonic, self.wrd,
                                                 self.wrs1, self.wrs2, shift,
                                                 self.fg)


class InstructionBNAIType(InstructionFunct3Type,  # type: ignore
                          InstructionFGType,
                          InstructionFunct30Type):
    isa_format_id = "BNAI"

    field_wrd = Field(name="wrd", base=7, size=5)
    field_wrs1 = Field(name="wrs1", base=15, size=5)
    field_imm = Field(name="imm", base=20, size=10)
    field_fg = Field(name="fg", base=30, size=1)

    def __init__(self,
                 wrd: Optional[int] = None,
                 wrs1: Optional[int] = None,
                 imm: Optional[int] = None,
                 fg: int = 0):
        self.wrd = wrd
        self.wrs1 = wrs1
        self.imm = Immediate(bits=10, signed=False, init=imm)
        self.fg = fg


class InstructionBNAMType(InstructionFunct3Type,  # type: ignore
                          InstructionW3Type,
                          InstructionFunct30Type):
    isa_format_id = "BNAM"

    def __init__(self,
                 wrd: Optional[int] = None,
                 wrs1: Optional[int] = None,
                 wrs2: Optional[int] = None):
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs1 = wrs1

    def __str__(self) -> str:
        return "{} w{}, w{}, w{}".format(self.mnemonic, self.wrd, self.wrs1,
                                         self.wrs2)


class InstructionBNAQType(InstructionW3Type):
    isa_format_id = "BNAQ"

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
                 wrs1: Optional[int] = None,
                 wrs2: Optional[int] = None,
                 wb_variant: int = 0,
                 zero_acc: bool = False,
                 wrd_hwsel: int = 0,
                 wrs1_qwsel: Optional[int] = None,
                 wrs2_qwsel: Optional[int] = None,
                 acc_shift_imm: Optional[int] = None):
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.wb_variant = wb_variant
        self.zero_acc = zero_acc
        self.wrd_hwsel = wrd_hwsel
        self.wrs1_qwsel = wrs1_qwsel
        self.wrs2_qwsel = wrs2_qwsel
        self.acc_shift_imm = acc_shift_imm

    def __str__(self) -> str:
        istr = cast(str, self.mnemonic)
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
        istr += ('??' if self.acc_shift_imm is None
                 else str(self.acc_shift_imm * 64))
        return istr


class InstructionBNRType(InstructionW3Type, InstructionFunct2Type):
    isa_format_id = "BNR"

    field_imm = Field(name="imm", base=[14, 25], size=[1, 7], description="")

    def __init__(self,
                 wrd: Optional[int] = None,
                 wrs1: Optional[int] = None,
                 wrs2: Optional[int] = None,
                 imm: Optional[int] = None):
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.imm = Immediate(bits=8, signed=False, init=imm)

    def __str__(self) -> str:
        return "{} w{}, w{}, w{} >> {}".format(self.mnemonic, self.wrd,
                                               self.wrs1, self.wrs2, self.imm)


class InstructionBNSType(InstructionW3Type,
                         InstructionFunct3Type,  # type: ignore
                         InstructionFGType):
    isa_format_id = "BNS"

    field_flag = Field(name="flag", base=25, size=2, description="")

    def __init__(self,
                 wrd: Optional[int] = None,
                 wrs1: Optional[int] = None,
                 wrs2: Optional[int] = None,
                 fg: int = 0,
                 flag: Optional[int] = None):
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.fg = fg
        self.flag = flag

    def __str__(self) -> str:
        return "{} w{}, w{}, w{}{}, FG{}".format(self.mnemonic, self.wrd,
                                                 self.wrs1, self.wrs2, self.fg,
                                                 self.flag)


class InstructionBNCType(InstructionFunct3Type,  # type: ignore
                         InstructionFGType,
                         InstructionShiftType):
    isa_format_id = "BNC"

    field_wrs1 = Field(name="wrs1", base=15, size=5)
    field_wrs2 = Field(name="wrs2", base=20, size=5)

    def __init__(self,
                 wrs1: Optional[int] = None,
                 wrs2: Optional[int] = None,
                 shift_bytes: int = 0,
                 shift_type: int = ShiftType.LSL,
                 fg: int = 0):
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.shift_bytes = Immediate(bits=5, signed=False, init=shift_bytes)
        self.shift_type = shift_type
        self.fg = fg

    def __str__(self) -> str:
        shift = "{} {}B".format(
            "<<" if self.shift_type == ShiftType.LSL else ">>",
            self.shift_bytes)
        return "{} w{}, w{}{}, FG{}".format(self.mnemonic, self.wrs1,
                                            self.wrs2, shift, self.fg)


class InstructionBNIType(InstructionFunct3Type):  # type: ignore
    isa_format_id = "BNI"

    field_rd = Field(name="rd", base=7, size=5)
    field_rs = Field(name="rs", base=15, size=5)
    field_imm = Field(name="imm", base=[25, 22], size=[7, 3], offset=5)
    field_rd_inc = Field(name="rd_inc", base=20, size=1)
    field_rs_inc = Field(name="rs_inc", base=21, size=1)

    def __init__(self,
                 rd: Optional[int] = None,
                 rs: Optional[int] = None,
                 imm: Optional[int] = None,
                 rd_inc: bool = False,
                 rs_inc: bool = False):
        self.rd = rd
        self.rs = rs
        self.imm = Immediate(bits=10, signed=True)
        self.rd_inc = rd_inc
        self.rs_inc = rs_inc

    def __str__(self) -> str:
        return ("{} x{}, {}(x{})"
                .format(self.mnemonic, self.rd, self.imm, self.rs))


class InstructionBNISType(InstructionFunct3Type):  # type: ignore
    isa_format_id = "BNIS"

    field_rs1 = Field(name="rs1", base=7, size=5)
    field_rs2 = Field(name="rs2", base=15, size=5)
    field_imm = Field(name="imm", base=22, size=10)
    field_rs1_inc = Field(name="rs1_inc", base=20, size=1)
    field_rs2_inc = Field(name="rs2_inc", base=21, size=1)

    def __init__(self,
                 rs1: Optional[int] = None,
                 rs2: Optional[int] = None,
                 imm: Optional[int] = None,
                 rs1_inc: bool = False,
                 rs2_inc: bool = False):
        self.rs1 = rs1
        self.rs2 = rs2
        self.imm = Immediate(bits=10, signed=True)
        self.rs1_inc = rs1_inc
        self.rs2_inc = rs2_inc

    def __str__(self) -> str:
        return ("{} x{}, {}(x{})"
                .format(self.mnemonic, self.rs1, self.imm, self.rs2))


class InstructionBNMVType(InstructionFunct3Type,  # type: ignore
                          InstructionFunct31Type):
    isa_format_id = "BNMV"

    field_wrd = Field(name="wrd", base=7, size=5)
    field_wrs = Field(name="wrs", base=15, size=5)

    def __init__(self, wrd: Optional[int] = None, wrs: Optional[int] = None):
        self.wrd = wrd
        self.wrs = wrs

    def __str__(self) -> str:
        return "{} w{}, w{}".format(self.mnemonic, self.wrd, self.wrs)


class InstructionBNMVRType(InstructionFunct3Type,  # type: ignore
                           InstructionFunct31Type):
    isa_format_id = "BNMVR"

    field_rd = Field(name="rd", base=7, size=5)
    field_rs = Field(name="rs", base=15, size=5)
    field_rd_inc = Field(name="rd_inc", base=20, size=1)
    field_rs_inc = Field(name="rs_inc", base=21, size=1)

    def __init__(self,
                 rd: Optional[int] = None,
                 rs: Optional[int] = None,
                 rd_inc: bool = False,
                 rs_inc: bool = False):
        self.rd = rd
        self.rs = rs
        self.rd_inc = rd_inc
        self.rs_inc = rs_inc

    def __str__(self) -> str:
        dpp = "++" if self.rd_inc else ""
        spp = "++" if self.rs_inc else ""
        return "{} x{}{}, x{}{}".format(self.mnemonic, self.rd, dpp, self.rs,
                                        spp)
