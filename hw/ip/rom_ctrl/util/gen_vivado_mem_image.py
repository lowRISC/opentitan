#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Script for generating a splicable Vivado ROM image

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

from mem import MemFile


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

    # Loop over all words, and:
    # 1) Generate the address,
    # 2) convert the endianness, and
    # 3) write this to the output file.
    addr_chars = 8
    word_chars = math.ceil(width / 4)
    for idx, word in enumerate(vmem.chunks[0].words):
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
