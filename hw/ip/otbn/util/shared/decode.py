#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import struct
import sys
from typing import Dict, List

from shared.elf import read_elf
from shared.insn_yaml import Insn, load_insns_yaml

# Load the insns.yml file at module load time.
try:
    INSNS_FILE = load_insns_yaml()
except RuntimeError as err:
    sys.stderr.write('{}\n'.format(err))
    sys.exit(1)


class OTBNProgram:
    def __init__(self, symbols: Dict[str, int], insns: Dict[int, int],
                 data: Dict[int, int]):
        self.symbols = symbols  # label -> PC
        self.data = data  # addr -> data (32b word)

        self.insns = {}
        for pc, opcode in insns.items():
            mnem = INSNS_FILE.mnem_for_word(opcode)
            if mnem is None:
                raise ValueError(
                    'No legal decoding for mnemonic: {}'.format(mnem))
            insn = INSNS_FILE.mnemonic_to_insn[mnem]
            assert insn.encoding is not None
            enc_vals = insn.encoding.extract_operands(opcode)
            op_vals = insn.enc_vals_to_op_vals(pc, enc_vals)
            self.insns[pc] = (insn, op_vals)

    def min_pc(self) -> int:
        return min(self.insns.keys())

    def max_pc(self) -> int:
        return max(self.insns.keys())

    def get_pc_at_symbol(self, symbol: str) -> int:
        if symbol not in self.symbols:
            raise ValueError(
                'Symbol {} not found in program. Available symbols: {}'.format(
                    symbol, ', '.join(self.symbols.keys())))
        return self.symbols[symbol]

    def get_symbols_for_pc(self, pc: int) -> List[str]:
        return [s for s, addr in self.symbols.items() if addr == pc]

    def get_data_at_addr(self, addr: int) -> int:
        return self.data[addr]

    def get_insn(self, pc: int) -> Insn:
        return self.insns[pc][0]

    def get_operands(self, pc: int) -> Dict[str, int]:
        return self.insns[pc][1]


def _decode_mem(base_addr: int, data: bytes) -> Dict[int, int]:
    '''Interpret memory bytes as a dictionary indexed by address/PC'''
    assert len(data) & 3 == 0
    return {(base_addr + 4 * offset): int_val[0]
            for offset, int_val in enumerate(struct.iter_unpack('<I', data))}


def decode_elf(path: str) -> OTBNProgram:
    '''Read ELF file at path and decode contents into an OTBNProgram instance

    Returns the OTBNProgram instance representing the program in the ELF file.
    '''
    (imem_bytes, dmem_bytes, symbols) = read_elf(path)

    insns = _decode_mem(0, imem_bytes)
    data = _decode_mem(0, dmem_bytes)

    return OTBNProgram(symbols, insns, data)
