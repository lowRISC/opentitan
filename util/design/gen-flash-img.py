#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Takes a compiled VMEM image and processes it for loading into flash.

    Specifically, this takes a raw flash image and adds both layers of ECC
    (integrity and reliablity), and optionally, scrambles the data using the
    same XEX scrambling scheme used in the flash controller. This enables
    backdoor loading the flash on simulation platforms (e.g., DV and Verilator).
"""

import argparse
import functools
import logging
import re
import sys
from pathlib import Path
from typing import List

from pyfinite import ffield

import prince
import secded_gen

FLASH_WORD_SIZE = 64  # bits
FLASH_ADDR_SIZE = 16  # bits
FLASH_INTEGRITY_ECC_SIZE = 4  # bits
FLASH_RELIABILITY_ECC_SIZE = 8  # bits
GF_OPERAND_B_MASK = (2**FLASH_WORD_SIZE) - 1
GF_OPERAND_A_MASK = (GF_OPERAND_B_MASK &
                     ~(0xffff <<
                       (FLASH_WORD_SIZE - FLASH_ADDR_SIZE))) << FLASH_WORD_SIZE
PRINCE_NUM_HALF_ROUNDS = 5

# Create GF(2^64) with irreducible_polynomial = x^64 + x^4 + x^3 + x + 1
GF_2_64 = ffield.FField(64,
                        gen=((0x1 << 64) | (0x1 << 4) | (0x1 << 3) |
                             (0x1 << 1) | 0x1))


@functools.lru_cache(maxsize=None)
def _xex_scramble(data: int, word_addr: int, flash_addr_key: int,
                  flash_data_key: int) -> int:
    operand_a = ((flash_addr_key & GF_OPERAND_A_MASK) >>
                 (FLASH_WORD_SIZE - FLASH_ADDR_SIZE)) | word_addr
    operand_b = flash_addr_key & GF_OPERAND_B_MASK
    mask = GF_2_64.Multiply(operand_a, operand_b)
    masked_data = data ^ mask
    return prince.prince(masked_data, flash_data_key,
                         PRINCE_NUM_HALF_ROUNDS) ^ mask


def main(argv: List[str]):
    # Parse command line args.
    parser = argparse.ArgumentParser()
    parser.add_argument("--infile",
                        "-i",
                        type=str,
                        help="Input VMEM file to reformat.")
    parser.add_argument("--outfile", "-o", type=str, help="Output VMEM file.")
    parser.add_argument("--scramble",
                        "-s",
                        action="store_true",
                        help="Whether to scramble data or not.")
    parser.add_argument("--address-key",
                        type=str,
                        help="Flash address scrambling key.")
    parser.add_argument("--data-key",
                        type=str,
                        help="Flash address scrambling key.")
    args = parser.parse_args(argv)

    # Validate command line args.
    if args.scramble:
        if args.address_key is None or args.data_key is None:
            logging.error(
                "Address and data keys must be provided when scrambling is"
                "requested.")

    # Open original VMEM for processing.
    try:
        orig_vmem = Path(args.infile).read_text()
    except IOError:
        raise Exception(f"Unable to open {args.infile}")

    # Search for lines that contain data, skipping other comment lines.
    orig_vmem_lines = re.findall(r"^@.*$", orig_vmem, flags=re.MULTILINE)

    # Load project SECDED configuration.
    config = secded_gen.load_secded_config()

    reformatted_vmem_lines = []
    for line in orig_vmem_lines:
        line_items = line.split()
        reformatted_line = ""
        address = None
        data = None
        for item in line_items:
            # Process the address first.
            if re.match(r"^@", item):
                reformatted_line += item
                address = int(item.lstrip("@"), 16)
            # Process the data words.
            else:
                data = int(item, 16)
                # `data_w_intg_ecc` will be in format {ECC bits, data bits}.
                data_w_intg_ecc, _ = secded_gen.ecc_encode(
                    config, "hamming", FLASH_WORD_SIZE, data)
                # Due to storage constraints the first nibble of ECC is dropped.
                data_w_intg_ecc &= 0xFFFFFFFFFFFFFFFFF
                if args.scramble:
                    intg_ecc = data_w_intg_ecc & (0xF << FLASH_WORD_SIZE)
                    data = _xex_scramble(data, address, args.flash_addr_key,
                                         args.flash_data_key)
                    data_w_intg_ecc = intg_ecc | data
                # `data_w_full_ecc` will be in format {reliablity ECC bits,
                # integrity ECC bits, data bits}.
                data_w_full_ecc, _ = secded_gen.ecc_encode(
                    config, "hamming",
                    FLASH_WORD_SIZE + FLASH_INTEGRITY_ECC_SIZE,
                    data_w_intg_ecc)
                reformatted_line += f" {data_w_full_ecc:x}"

        # Append reformatted line to what will be the new output VMEM file.
        reformatted_vmem_lines.append(reformatted_line)

    # Write re-formatted output file.
    with open(args.outfile, "w") as of:
        of.writelines(reformatted_vmem_lines)


if __name__ == "__main__":
    main(sys.argv[1:])
