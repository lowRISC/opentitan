#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Tool for generating updatemem-compatible MEM files for ROM or OTP splicing.

This script takes a .vmem file as input and converts that into a format usable
by Vivado for splicing FPGA bitstreams via updatemem. For details on the
required file format, refer to UG898 (Chapter 7, "Using UpdateMEM to Update BIT
files with MMI and ELF Data"):
https://www.xilinx.com/support/documentation/sw_manuals/xilinx2020_2/ug898-vivado-embedded-design.pdf#page=165

Typical usage:
>>> ./gen_vivado_mem_image.py test_rom.scr.32.vmem test_rom.updatemem.mem
'''

import argparse
import sys
import math
import re
import logging
from typing import List

from mem import MemFile

logger = logging.getLogger('gen_vivado_mem_image')


class UpdatememSimulator:
    """Simulate the externally-visible behavior of updatemem."""

    def __init__(self, num_bitlanes: int, width: int):
        self.num_bitlanes_ = num_bitlanes
        self.brams_ = [[0 for _ in range(num_bitlanes)] for _ in range(width)]
        self.lane_index_ = 0
        self.block_index_ = 0
        self.bit_index_ = 0

    def write_updatemem_hex_string(self, hex_word: str) -> None:
        """Simulate consuming a data column from a MEM file."""

        for nibble in hex_word:
            value = int(nibble, base=16)

            for _ in range(4):
                bit = 1 if value & 0b1000 else 0
                value <<= 1
                assert bit in [0, 1]
                assert self.block_index_ != self.num_bitlanes_
                self.brams_[self.lane_index_][self.block_index_] |= bit << self.bit_index_

                self.lane_index_ += 1
                if self.lane_index_ == len(self.brams_):
                    self.lane_index_ = 0

                    self.bit_index_ += 1
                    if self.bit_index_ == 64 * 4:
                        self.bit_index_ = 0

                        self.block_index_ += 1

    def render_init_lines(self) -> List[List[str]]:
        """Render INIT_XX lines like the ones that updatemem would print."""

        line_groups = []
        for i, bram in enumerate(self.brams_):
            group = []
            for j, row in enumerate(bram):
                group.append(f"simulated INIT_{j:02X}: 256'h{row:064X}")
            line_groups.append(group)

        return line_groups


def parse_otp_init_strings(init_line_groups: List[List[str]]) -> List[int]:
    """Parse a sequence of 22-bit OTP words from Vivado INIT_XX lines.

    The data layout was determined by running a full Vivado bitstream build and
    comparing the OTP image (//hw/ip/otp_ctrl/data:img_rma) with the INIT_XX
    strings that Vivado produces (see the otp_init_strings.txt artifact).
    """

    out = []
    brams = []

    for i, lines in enumerate(init_line_groups):
        bram_scratch = []
        for line in lines:
            match = re.search('INIT_.*h([0-9a-fA-F]+)$', line)
            if not match:
                continue

            data = match.group(1)
            bits = []
            while len(data) > 0:
                chunk = data[:4]
                data = data[4:]
                if chunk == '0000':
                    bits.append(0)
                elif chunk == '0001':
                    bits.append(1)
                else:
                    raise Exception("Unexpected chunk in OTP init string:", chunk)

            bram_scratch.append(bits)
        brams.append(bram_scratch)

    for i in range(1024):
        # Slice off the first 22 bits.
        bits = []
        for bram in brams:
            if bram[0] == []:
                bram.pop(0)
            bits.append(bram[0].pop())

        value = 0
        for bit in reversed(bits):
            value = (value << 1) | bit

        logger.debug(f'@{i:06x}: {value:06x} = {bits}')
        out.append(value)

    return out


def otp_words_to_updatemem_pieces(words: List[int]) -> List[str]:
    """Transform `words` into pieces of an updatemem-compatible MEM file."""

    assert len(words) % 4 == 0
    assert len(words) <= 1024
    mask_22_bits = (1 << 22) - 1
    assert all(word == (word & mask_22_bits) for word in words)

    # The first line indicates that we're starting from the zero address. For
    # simplicity, we will not print any subsequent addresses.
    mem_pieces = ['@0']
    for word in words:
        # Examining the INIT_XX strings from a full Vivado bitstream build, it
        # appears that each 22-bit word has its bits reversed and is padded with
        # 15 zeroes. As a result, the hexadecimal init strings will only contain
        # '0' and '1' characters.
        rev = 0
        for _ in range(22):
            rev = (rev << 1) | (word & 1)
            word >>= 1

        words_to_write = [rev] + [0] * 15

        # Concatenate sequential pairs of OTP words before emitting a hex
        # string. If we naively encoded each 22-bit OTP word as a 6-digit hex
        # string, updatemem would dutifully write two unwanted zero bits. To
        # work around this, we concatenate two words for each hex string; 11 hex
        # digits cleanly represent 44 bits.
        #
        # Note that this complexity cannot be avoided by concatenating all the
        # words and emitting a single hex string because updatemem rejects long
        # hex strings, saying that they exceed data limits.
        while len(words_to_write) > 0:
            word1, word2 = words_to_write[:2]
            words_to_write = words_to_write[2:]

            # Write 44 bits in hexadecimal.
            value = word1 << 22 | word2
            col_string = f'{value:011X}'
            mem_pieces.append(col_string)

    # Self-check: test the correctness of `mem_pieces` by feeding into a model
    # of updatemem's behavior. The model can predict the INIT_XX strings that
    # the real updatemem would print. We also know how to recover OTP memory
    # contents from INIT_XX strings. Composing these two functions should bring
    # us back to the original `words` input.
    updatemem_sim = UpdatememSimulator(0x40, 22)
    for piece in mem_pieces[1:]:
        updatemem_sim.write_updatemem_hex_string(piece)
    init_lines = updatemem_sim.render_init_lines()

    reconstructed = parse_otp_init_strings(init_lines)
    if len(reconstructed) < len(words) or reconstructed[:len(words)] != words:
        raise Exception("Generated updatemem data for OTP failed self-check")

    return mem_pieces


def swap_bytes(width: int, orig: int, swap_nibbles: bool) -> int:
    num_bytes = math.ceil(width / 8)
    swapped = 0
    for i in range(num_bytes):
        byte_value = ((orig >> (i * 8)) & 0xFF)
        if swap_nibbles:
            byte_value = ((byte_value << 4) | (byte_value >> 4)) & 0xFF
        swapped |= (byte_value << ((num_bytes - i - 1) * 8))
    return swapped


def main() -> int:
    logging.basicConfig(format='%(asctime)s [%(filename)s] %(message)s')
    logger.setLevel(logging.INFO)

    parser = argparse.ArgumentParser()
    parser.add_argument('infile', type=argparse.FileType('rb'))
    parser.add_argument('outfile', type=argparse.FileType('w'))
    parser.add_argument('--swap-nibbles', dest='swap_nibbles', action='store_true')

    args = parser.parse_args()

    # Extract width from ROM file name.
    match = re.search(r'([0-9]+)(\.scr)?\.vmem', args.infile.name)
    if not match:
        raise ValueError('Cannot extract ROM word width from file name ' +
                         args.infile.name)
    else:
        width = int(match.group(1))

    # Load the input vmem file.
    vmem = MemFile.load_vmem(width, args.infile)

    # OpenTitan vmem files should always contain one single contiguous chunk.
    assert len(vmem.chunks) == 1
    words = vmem.chunks[0].words

    if width == 24:
        logger.info("Generating updatemem-compatible MEM file for OTP image.")
        updatemem_pieces = otp_words_to_updatemem_pieces(words)
        updatemem_line = ' '.join(updatemem_pieces)
        args.outfile.write(updatemem_line + '\n')
        return 0

    logger.info("Generating updatemem-compatible MEM file for ROM.")
    # Loop over all words, and:
    # 1) Generate the address,
    # 2) convert the endianness, and
    # 3) write this to the output file.
    addr_chars = 8
    word_chars = math.ceil(width / 4)
    for idx, word in enumerate(words):
        # Generate the address.
        addr = idx * math.ceil(width / 8)
        # Convert endianness.
        data = swap_bytes(width, word, args.swap_nibbles)
        # Write to file.
        toks = [f'@{addr:0{addr_chars}X}']
        toks.append(f'{data:0{word_chars}X}')
        args.outfile.write(' '.join(toks) + '\n')

    return 0


if __name__ == '__main__':
    sys.exit(main())
