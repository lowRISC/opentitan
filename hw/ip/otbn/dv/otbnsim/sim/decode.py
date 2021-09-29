# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code to load instruction words into a simulator'''

import struct
from typing import List, Optional, Iterator

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


def decode_bytes(base_addr: int, data: bytes) -> List[OTBNInsn]:
    '''Decode instruction bytes as instructions'''
    assert len(data) & 3 == 0
    return [_decode_word(base_addr + 4 * offset, int_val[0])
            for offset, int_val in enumerate(struct.iter_unpack('<I', data))]


def decode_file(base_addr: int, path: str) -> List[OTBNInsn]:
    with open(path, 'rb') as handle:
        return decode_bytes(base_addr, handle.read())
