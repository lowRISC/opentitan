# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code to load instruction words into a simulator'''

# Lots of this probably belongs in the upstream riscv-python-sim simulator, but
# let's get everything working first and then try to push anything sensible
# afterwards.

import struct
from typing import List, Optional, Tuple, Type

from .isa import OTBNInsn
from .insn import INSN_CLASSES
from .state import OTBNState

# A tuple as returned by get_insn_masks: an element (m0, m1, cls) means "if a
# word has all the bits in m0 clear and all the bits in m1 set, then you should
# decode it with the given class".
_MaskTuple = Tuple[int, int, Type[OTBNInsn]]


class IllegalInsn(OTBNInsn):
    '''A catch-all subclass of Instruction for bad data

    This handles anything that doesn't decode correctly. Doing so for OTBN is
    much easier than if we wanted to support compressed-mode (RV32IC), because
    we don't need to worry about whether we have 16 or 32 bits of rubbish.

    Note that we declare this with an opcode of zero. Note that this implies
    the bottom two bits are 0, which would imply a compressed instruction, so
    we know this doesn't match any real instruction.

    '''
    def __init__(self, word: int) -> None:
        self.word = word

    def execute(self, state: OTBNState) -> None:
        raise RuntimeError('Illegal instruction at {:#x}: encoding {:#010x}.'
                           .format(int(state.pc), self.word))


MASK_TUPLES = None  # type: Optional[List[_MaskTuple]]


def get_insn_masks() -> List[_MaskTuple]:
    '''Generate a list of zeros/ones masks for known instructions

    The result is memoized.

    '''
    global MASK_TUPLES
    if MASK_TUPLES is None:
        tuples = []
        for cls in INSN_CLASSES:
            # cls is the class for some OTBNInsn: an object that represents a
            # decoded instruction. It has a class variable called "insn", which is
            # the subclass of insn_yaml.Insn that represents that instruction
            # (without operand values).
            insn = cls.insn
            if insn.encoding is None:
                continue

            m0, m1 = insn.encoding.get_masks()

            # Encoding.get_masks sets bits that are 'x', so we have to do a
            # difference operation too.
            tuples.append((m0 & ~m1, m1 & ~m0, cls))
        MASK_TUPLES = tuples

    return MASK_TUPLES


def _decode_word(word_off: int, word: int) -> OTBNInsn:
    found_cls = None
    for m0, m1, cls in get_insn_masks():
        # If any bit is set that should be zero or if any bit is clear that
        # should be one, ignore this instruction.
        if word & m0 or (~ word) & m1:
            continue

        found_cls = cls
        break

    if found_cls is None:
        return IllegalInsn(word)

    # Decode the instruction. We know that we have an encoding (we checked in
    # get_insn_masks).
    assert cls.insn.encoding is not None
    enc_vals = cls.insn.encoding.extract_operands(word)

    # Make sense of these encoded values as "operand values" (doing any
    # shifting, sign interpretation etc.)
    op_vals = cls.insn.enc_vals_to_op_vals(4 * word_off, enc_vals)

    return cls(op_vals)


def decode_bytes(data: bytes) -> List[OTBNInsn]:
    '''Decode instruction bytes as instructions'''
    assert len(data) & 3 == 0
    return [_decode_word(offset, int_val[0])
            for offset, int_val in enumerate(struct.iter_unpack('<I', data))]


def decode_file(path: str) -> List[OTBNInsn]:
    with open(path, 'rb') as handle:
        return decode_bytes(handle.read())
