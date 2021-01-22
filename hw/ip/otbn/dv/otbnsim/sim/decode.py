# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code to load instruction words into a simulator'''

import struct
from typing import List, Optional, Tuple, Type

from .alert import Alert, ERR_CODE_ILLEGAL_INSN
from .isa import DecodeError, OTBNInsn
from .insn import INSN_CLASSES
from .state import OTBNState

# A tuple as returned by get_insn_masks: an element (m0, m1, cls) means "if a
# word has all the bits in m0 clear and all the bits in m1 set, then you should
# decode it with the given class".
_MaskTuple = Tuple[int, int, Type[OTBNInsn]]


class IllegalInsnError(Alert):
    '''Raised on a bad instruction'''
    err_code = ERR_CODE_ILLEGAL_INSN

    def __init__(self, word: int, msg: str):
        self.word = word
        self.msg = msg

    def __str__(self) -> str:
        return ('Illegal instruction {:#010x}: {}'.format(self.word, self.msg))


class IllegalInsn(OTBNInsn):
    '''A catch-all subclass of Instruction for bad data

    This handles anything that doesn't decode correctly. Doing so for OTBN is
    much easier than if we wanted to support compressed-mode (RV32IC), because
    we don't need to worry about whether we have 16 or 32 bits of rubbish.

    Note that we declare this with an opcode of zero. Note that this implies
    the bottom two bits are 0, which would imply a compressed instruction, so
    we know this doesn't match any real instruction.

    '''
    def __init__(self, pc: int, raw: int, msg: str) -> None:
        super().__init__(raw, {})
        self.msg = msg

        # Override the memoized disassembly for the instruction, avoiding us
        # disassembling the underlying DummyInsn.
        self._disasm = (pc, '?? 0x{:08x}'.format(raw))

    def execute(self, state: OTBNState) -> None:
        raise IllegalInsnError(self.raw, self.msg)


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


def _decode_word(pc: int, word: int) -> OTBNInsn:
    found_cls = None
    for m0, m1, cls in get_insn_masks():
        # If any bit is set that should be zero or if any bit is clear that
        # should be one, ignore this instruction.
        if word & m0 or (~ word) & m1:
            continue

        found_cls = cls
        break

    if found_cls is None:
        return IllegalInsn(pc, word, 'No legal decoding')

    # Decode the instruction. We know that we have an encoding (we checked in
    # get_insn_masks).
    assert cls.insn.encoding is not None
    enc_vals = cls.insn.encoding.extract_operands(word)

    # Make sense of these encoded values as "operand values" (doing any
    # shifting, sign interpretation etc.)
    op_vals = cls.insn.enc_vals_to_op_vals(pc, enc_vals)

    # Catch any decode errors raised by the instruction constructor. This lets
    # us generate errors if an instruction encoding has extra constraints that
    # can't be captured by the logic in the Encoding class.
    try:
        return cls(word, op_vals)
    except DecodeError as err:
        return IllegalInsn(pc, word, str(err))


def decode_bytes(base_addr: int, data: bytes) -> List[OTBNInsn]:
    '''Decode instruction bytes as instructions'''
    assert len(data) & 3 == 0
    return [_decode_word(base_addr + 4 * offset, int_val[0])
            for offset, int_val in enumerate(struct.iter_unpack('<I', data))]


def decode_file(base_addr: int, path: str) -> List[OTBNInsn]:
    with open(path, 'rb') as handle:
        return decode_bytes(base_addr, handle.read())
