# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code to load instruction words into a simulator'''

# Lots of this probably belongs in the upstream riscv-python-sim simulator, but
# let's get everything working first and then try to push anything sensible
# afterwards.

import struct
from typing import List, Optional, TypeVar

from riscvmodel.insn import get_insns  # type: ignore
from riscvmodel.isa import Instruction, isa  # type: ignore
from riscvmodel.model import Model  # type: ignore
from riscvmodel.variant import Variant, RV32I  # type: ignore

# The riscvmodel decoder works by introspection, checking all the instruction
# classes that have been defined so far. This implicit approach only works if
# we make absolutely sure that we *have* loaded the instruction definitions we
# use. So we do this useless import to ensure it.
from .insn import InstructionLOOP  # noqa: F401

# A subclass of Instruction
_InsnSubclass = TypeVar('_InsnSubclass', bound=Instruction)


@isa(".bogus-insn", RV32I, opcode=0)
class IllegalInsn(Instruction):  # type: ignore
    '''A catch-all subclass of Instruction for bad data

    This handles anything that doesn't decode correctly. Doing so for OTBN is
    much easier than if we wanted to support compressed-mode (RV32IC), because
    we don't need to worry about whether we have 16 or 32 bits of rubbish.

    Note that we declare this with an opcode of zero. Note that this implies
    the bottom two bits are 0, which would imply a compressed instruction, so
    we know this doesn't match any real instruction.

    '''
    def __init__(self) -> None:
        self.word = None  # type: Optional[int]

    def decode(self, word: int) -> None:
        self.word = word

    def execute(self, model: Model) -> None:
        assert self.word is not None
        raise RuntimeError('Illegal instruction at {:#x}: encoding {:#010x}.'
                           .format(int(model.state.pc), self.word))


def _decode_word(word_off: int,
                 word: int,
                 insn_classes: List[_InsnSubclass]) -> Instruction:
    opcode = word & 0x7f
    insn = None
    for cls in insn_classes:
        if cls.field_opcode.value != opcode:
            continue
        if not cls.match(word):
            continue

        insn = cls()
        break

    if insn is None:
        insn = IllegalInsn()
    insn.decode(word)
    return insn


def decode_bytes(data: bytes, variant: Variant) -> List[Instruction]:
    '''Decode instruction bytes as instructions'''
    insn_classes = get_insns(variant=variant)
    assert len(data) & 3 == 0
    return [_decode_word(offset, int_val[0], insn_classes)
            for offset, int_val in enumerate(struct.iter_unpack('<I', data))]


def decode_file(path: str, variant: Variant) -> List[Instruction]:
    with open(path, 'rb') as handle:
        return decode_bytes(handle.read(), variant)
