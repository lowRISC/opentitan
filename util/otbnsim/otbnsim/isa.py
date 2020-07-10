# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from riscvmodel.isa import Instruction
from riscvmodel.variant import Variant
from riscvmodel.model import State
from riscvmodel.types import Immediate

from .variant import RV32IXotbn

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
