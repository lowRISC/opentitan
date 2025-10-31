#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
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
                 data: Dict[int, int], nop_subfuncs: List[str]):
        self.symbols = symbols  # label -> PC
        self.data = data        # addr -> data (32b word)

        # For each function name in nop_subfuncs, we assume that it will have
        # control flow limited in the following way. If the function starts at
        # address A and the first JALR instruction after A is at address B,
        # then execution will not leave the interval [A, B] until the function
        # returns by executing the JALR at B.
        #
        # With this assumption, we can imagine replacing the instructions in
        # that interval with a "nop sled". The ranges of the these sleds are
        # stored in the nop_ranges list, as pairs (A, B).
        nop_ranges: list[tuple[int, int]] = []

        for symbol in nop_subfuncs:
            # Get the start address of the function. If the function dosen't
            # appear in the list of symbols, there's nothing to do for it.
            start_addr = symbols.get(symbol)
            if start_addr is None:
                continue

            for pc in range(start_addr, 1 << 32, 4):
                opcode = insns.get(pc)
                if opcode is None:
                    raise RuntimeError("Fell off the end of the binary "
                                       "when searching for a JALR for a "
                                       f"function with symbol {symbol}, "
                                       f"starting at {start_addr:#x}")

                # Check whether we just found 'B' (see note above nop_ranges)
                if INSNS_FILE.mnem_for_word(opcode) == 'jalr':
                    nop_ranges.append((start_addr, pc))
                    break

        self.insns = {}
        for pc, opcode in insns.items():
            # Check if PC lies within one of the NOP ranges (equal to or after
            # the start of a nop subfunc and strictly before the JALR
            # instruction at the end).
            in_nop_region = any(a <= pc < b for a, b in nop_ranges)

            # If the PC *is* in a NOP region, interpret the opcode at PC as a
            # NOP (addi x0, x0, x0). If not, decode the opcode and find the
            # appropriate instruction and operands.
            if in_nop_region:
                insn = INSNS_FILE.mnemonic_to_insn["addi"]
                enc_vals = {'imm': 0, 'grs1': 0, 'grd': 0}
            else:
                mnem = INSNS_FILE.mnem_for_word(opcode)
                if mnem is None:
                    raise ValueError(f'No mnemonic for opcode {opcode:#08x}')

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


def decode_elf(path: str, nop_subfuncs: List[str]) -> OTBNProgram:
    '''Read ELF file at path and decode contents into an OTBNProgram instance

    Returns the OTBNProgram instance representing the program in the ELF file.
    '''
    (imem_bytes, dmem_bytes, symbols) = read_elf(path)

    insns = _decode_mem(0, imem_bytes)
    data = _decode_mem(0, dmem_bytes)

    return OTBNProgram(symbols, insns, data, nop_subfuncs)
