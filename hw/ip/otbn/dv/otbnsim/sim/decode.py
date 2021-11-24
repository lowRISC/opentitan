# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code to load instruction words into a simulator'''

import struct
from typing import Iterator, List, Optional, Tuple

from .constants import ErrBits
from .isa import INSNS_FILE, OTBNInsn
from .insn import INSN_CLASSES
from .state import OTBNState

MNEM_TO_CLASS = {cls.insn.mnemonic: cls for cls in INSN_CLASSES}


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

    def execute(self, state: OTBNState) -> Optional[Iterator[None]]:
        state.stop_at_end_of_cycle(ErrBits.ILLEGAL_INSN)
        return None


class EmptyInsn(OTBNInsn):
    '''A subclass of Instruction that represents non-existent data

    This is what we generate on a fetch error, where we don't really have any
    instruction data at all.

    '''
    # We don't have any instruction data
    has_bits = False

    def __init__(self, pc: int) -> None:
        super().__init__(0, {})

        # Override the memoized disassembly for the instruction, avoiding us
        # disassembling the underlying DummyInsn.
        self._disasm = (pc, '?? (no instruction data)')

    def execute(self, state: 'OTBNState') -> Optional[Iterator[None]]:
        state.stop_at_end_of_cycle(ErrBits.IMEM_INTG_VIOLATION)
        return None


def _decode_word(pc: int, word: int) -> OTBNInsn:
    mnem = INSNS_FILE.mnem_for_word(word)
    if mnem is None:
        return IllegalInsn(pc, word, 'No legal decoding')

    cls = MNEM_TO_CLASS.get(mnem)
    if cls is None:
        return IllegalInsn(pc, word, f'No insn class for mnemonic {mnem}')

    # Decode the instruction. We know that we have an encoding (we checked in
    # get_insn_masks).
    assert cls.insn.encoding is not None
    enc_vals = cls.insn.encoding.extract_operands(word)

    # Make sense of these encoded values as "operand values" (doing any
    # shifting, sign interpretation etc.)
    op_vals = cls.insn.enc_vals_to_op_vals(pc, enc_vals)

    return cls(word, op_vals)


def decode_words(base_addr: int,
                 data: List[Tuple[bool, int]]) -> List[OTBNInsn]:
    '''Decode instruction bytes as instructions'''
    ret = []
    for idx, (vld, w32) in enumerate(data):
        pc = 4 * idx
        ret.append(_decode_word(pc, w32) if vld else EmptyInsn(pc))
    return ret


def decode_file(base_addr: int, path: str) -> List[OTBNInsn]:
    with open(path, 'rb') as handle:
        raw_bytes = handle.read()

    # Each 32-bit word is represented by a 5 bytes, consisting of a validity
    # byte (0 or 1) followed by 4 bytes for the word itself.
    if len(raw_bytes) % 5:
        raise ValueError('Trying to load {} bytes of data from {}, '
                         'which is not a multiple of 5.'
                         .format(path, len(raw_bytes)))

    data = []
    for idx32, (vld, u32) in enumerate(struct.iter_unpack('<BI', raw_bytes)):
        if vld not in [0, 1]:
            raise ValueError('The validity byte for 32-bit word {} '
                             'at {} is {}, not 0 or 1.'
                             .format(idx32, path, vld))

        data.append((vld == 1, u32))

    return decode_words(base_addr, data)
