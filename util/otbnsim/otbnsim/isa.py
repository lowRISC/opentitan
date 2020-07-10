# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from riscvmodel.isa import Instruction
from riscvmodel.variant import Variant
from riscvmodel.model import State
from riscvmodel.types import Immediate

from .variant import RV32IXotbn

from enum import Enum

class InstructionLType(Instruction):
    def __init__(self, rs1: int = None, bodysize: int = None):
        super().__init__()
        self.rs1 = rs1
        self.bodysize = Immediate(bits=12, signed=False)

    def randomize(self, variant: Variant):
        self.rs1 = randrange(0, variant.intregs)
        self.bodysize.randomize()

    def decode(self, machinecode: int):
        self.rs1 = (machinecode >> 15) & 0x1f
        self.bodysize.set_from_bits((machinecode >> 20) & 0xfff)

    def encode(self) -> int:
      x = self._opcode | (self._funct3 << 12)
      x |= (self.rs1 << 15) | (self.bodysize.unsigned() << 20)
      return x

    def __str__(self):
        return "{} x{}, {}".format(self._mnemonic, self.rs1, self.bodysize)

    def __eq__(self, other):
        if not super().__eq__(other):
            return False
        return self.rs1 == other.rs1 and self.bodysize == other.bodysize

class InstructionLIType(Instruction):
    def __init__(self, iter: int = None, bodysize: int = None):
        super().__init__()
        self.iter = Immediate(bits=10, signed=False)
        if iter:
            self.iter.set(iter)
        self.bodysize = Immediate(bits=12, signed=False)
        if bodysize:
            self.bodysize.set(bodysize)

    def randomize(self, variant: Variant):
        self.iter.randomize()
        self.bodysize.randomize()

    def decode(self, machinecode: int):
        self.iter.set_from_bits((((machinecode >> 15) & 0x1f) << 5) | ((machinecode >> 7) & 0x1F))
        self.bodysize.set_from_bits((machinecode >> 20) & 0xfff)

    def encode(self) -> int:
      x  = self._opcode | (self._funct3 << 12)
      x |= ((int(self.iter) >> 5) << 15) | ((int(self.iter) & 0x1F) << 7)
      x |= (self.bodysize.unsigned() << 20)
      return x

    def __str__(self):
        return "{} {}, {}".format(self._mnemonic, self.iter, self.bodysize)

    def __eq__(self, other):
        if not super().__eq__(other):
            return False
        return self.iter == other.iter and self.bodysize == other.bodysize

class ShiftType(Enum):
  LSL = 0 # logical shift left
  LSR = 1 # logical shift right

def DecodeShiftType(st: int) -> ShiftType:
  if st == 0:
    return ShiftType.LSL
  elif st == 1:
    return ShiftType.LSR
  else:
    raise Exception()

class InstructionBNAType(Instruction):
    def __init__(self, wrd: int=None, wrs1: int=None, wrs2: int=None, shift_bytes: int=None, shift_type: int=None):
        super().__init__()
        self.wrd = wrd
        self.wrs1 = wrs1
        self.wrs2 = wrs2
        self.shift_bytes = Immediate(bits=5, signed=False, init=shift_bytes)
        self.shift_type = DecodeShiftType(shift_type) if shift_type is not None else shift_type

    def randomize(self, variant):
        # TODO: shift randomization
        self.wrd.randomize()
        self.wrs1.randomize()
        self.wrs2.randomize()

    def ops_from_string(self, ops):
        # TODO: shift
        ops = [op for op in ops.split(",")]
        self.wrd = int(ops[0][1:])
        self.wrs1 = int(ops[1][1:])
        self.wrs2 = int(ops[1][1:])

    def __str__(self):
        return "{} w{}, w{}, w{}".format(self._mnemonic, self.wrd, self.wrs1, self.wrs2)

    def __eq__(self, other):
        if not super().__eq__(other):
            return False
        return self.wrd == other.wrd and self.wrs1 == other.wrs1 and self.wrs2 == other.wrs2 and self.shift_bytes == other.shift_bytes and self.shift_type == other.shift_type


class InstructionBNCSType(Instruction):
    def __init__(self, wrd: int=None, wsr: int=None, wcsr: int=None):
        super().__init__()
        self.wrd = wrd
        self.wsr = wsr
        self.wcsr = Immediate(bits=8, signed=False, init=wcsr)

    def randomize(self, variant: Variant):
        self.wrd.randomize()
        self.wsr.randomize()
        self.wcsr.randomize()

    def decode(self, machinecode: int):
        self.wrd = (machinecode >> 7) & 0x1f
        self.wsr = (machinecode >> 15) & 0x1f
        self.wcsr.set_from_bits((machinecode >> 20) & 0xff)

    def encode(self) -> int:
      x  = self._opcode | (self._funct3 << 12)
      x |= (self._funct31 << 31) | (self._funct30 << 30) | (self._funct29 << 29) | (self._funct28 << 28)
      x |= (self.wrd << 7) | (self.wsr << 15) | (int(self.wcsr) << 20)
      return x

    def ops_from_string(self, ops):
        ops = [op for op in ops.split(",")]
        self.wrd = int(ops[0][1:])
        self.wsr = int(ops[1][1:])
        self.wcsr.set(int(ops[2], 0))

    def __str__(self):
        return "{} w{}, w{}, {}".format(self._mnemonic, self.wrd, self.wsr, self.wcsr)

    def __eq__(self, other):
        if not super().__eq__(other):
            return False
        return self.wrd == other.wrd and self.wsr == other.wrd and self.wcsr == other.wcsr


def isaOTBN(mnemonic: str, *, opcode: int, funct3: int=None, funct28: int=None, funct29: int=None, funct30: int=None, funct31: int=None):
    """
    Decorator for the instructions. The decorator contains the static information for the instructions, in particular
    the encoding parameters and the assembler mnemonic.

    :param mnemonic: Assembler mnemonic
    :param opcode: Opcode of this instruction
    :param funct3: 3 bit function code on bits 14 to 12 (R-, I-, S- and B-type)
    :param funct7: 7 bit function code on bits 31 to 25 (R-type)
    :param funct12: 12 bit function code on bits 31 to 20
    :return: Wrapper class that overwrites the actual definition and contains static data
    """
    def wrapper(wrapped):
        """Get wrapper"""
        class WrappedClass(wrapped):
            """Generic wrapper class"""
            _mnemonic = mnemonic
            _variant = RV32IXotbn
            _opcode = opcode
            _funct3 = funct3
            _funct28 = funct28
            _funct29 = funct29
            _funct30 = funct30
            _funct31 = funct30

            @staticmethod
            def _match(machinecode: int):
                """Try to match a machine code to this instruction"""
                f3 = (machinecode >> 12) & 0x7
                f28 = (machinecode >> 28) & 0x1
                f29 = (machinecode >> 29) & 0x1
                f30 = (machinecode >> 30) & 0x1
                f31 = (machinecode >> 31) & 0x1
                if funct3 is not None and f3 != funct3:
                    return False
                if funct28 is not None and f28 != funct28:
                    return False
                if funct29 is not None and f29 != funct29:
                    return False
                if funct30 is not None and f30 != funct30:
                    return False
                if funct31 is not None and f31 != funct31:
                    return False
                return True

        WrappedClass.__name__ = wrapped.__name__
        WrappedClass.__module__ = wrapped.__module__
        WrappedClass.__qualname__ = wrapped.__qualname__
        return WrappedClass
    return wrapper
