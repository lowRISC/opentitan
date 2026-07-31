#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Takes a compiled VMEM image and processes it for loading into the RRAM.

    Specifically, this takes a raw RRAM image, adds address infection and scrambles
    the data using the same XEX scrambling scheme used in the RRAM controller. This
    enables backdoor loading the RRAM on simulation platforms (e.g., DV and Verilator).
"""

import argparse
import re
import sys
from pathlib import Path
from typing import List

import hjson
from pyfinite import ffield
from lib.common import validate_data_perm_option, vmem_permutation_string
from lib.otp_scrambling_keys import (OTP_WORD_SIZE_WECC, ScramblingConfigs,
                                     compute_scrambling_keys,
                                     get_otp_ctrl_netlist_consts,
                                     get_scrambling_configs_from_otp)

import prince

OTP_RRAM_DATA_DEFAULT_CFG_RE = re.compile(
    r"CREATOR_SW_CFG: CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG")

# RRAM data / scrambling parameters.
RRAM_ADDR_KEY_SIZE = 128  # bits
RRAM_DATA_KEY_SIZE = 128  # bits
RRAM_WORD_SIZE = 128  # bits
# rram_ctrl_pkg::AddrW = clog2(2MiB/(128/8))
RRAM_ADDR_SIZE = 17  # bits
RRAM_PRINCE_NUM_HALF_ROUNDS = 5

# First RRAM word address in the OTP partition, i.e. the exclusive upper bound
# of the data partition. rram_ctrl_pkg::OtpStartPage * WordsPerPage
# = (TotalPages - OtpPages) * WordsPerPage = (4096 - 5) * 32.
RRAM_OTP_START_WORD_ADDR = 4091 * 32

# ------------------------------------------------------------------------------
# DO NOT EDIT: edit fixed parameters above instead.
# ------------------------------------------------------------------------------
RRAM_GF_OPERAND_B_MASK = (2**RRAM_WORD_SIZE) - 1
RRAM_GF_OPERAND_A_MASK = (2**RRAM_ADDR_SIZE) - 1
# Create GF(2^128) with irreducible_polynomial = x^128 + x^7 + x^2 + x + 1
RRAM_GF_2_128 = ffield.FField(128,
                              gen=((0x1 << 128) | (0x1 << 7) | (0x1 << 2) |
                                   (0x1 << 1) | 0x1))

# Format string for generating new VMEM file.
RRAM_VMEM_WORD_SIZE = (RRAM_WORD_SIZE)
VMEM_FORMAT_STR = " {:0" + f"{RRAM_VMEM_WORD_SIZE // 4}" + "X}"
# ------------------------------------------------------------------------------


def _interleave_split(data: int):
    """
    Splits a 128-bit integer into two 64-bit operands.
    operand_a: bits [127, 125, ..., 1]
    operand_b: bits [126, 124, ..., 0]
    """
    operand_a = 0
    operand_b = 0

    # We loop 64 times because we are pulling 64 pairs of bits
    for i in range(64):
        # Extract bit at position (2*i + 1) for operand_a
        bit_a = (data >> (2 * i + 1)) & 1
        operand_a |= (bit_a << i)

        # Extract bit at position (2*i) for operand_b
        bit_b = (data >> (2 * i)) & 1
        operand_b |= (bit_b << i)

    return operand_a, operand_b


def _interleave_combine(operand_a, operand_b):
    """
    Combines two 64-bit operands into a 128-bit integer.
    operand_a provides bits [1, 3, 5, ..., 127]
    operand_b provides bits [0, 2, 4, ..., 126]
    """
    result = 0

    for i in range(64):
        # Place bit i from operand_b at the even position (2*i)
        bit_b = (operand_b >> i) & 1
        result |= (bit_b << (2 * i))

        # Place bit i from operand_a at the odd position (2*i + 1)
        bit_a = (operand_a >> i) & 1
        result |= (bit_a << (2 * i + 1))

    return result


def _xex_scramble(data: int, word_addr: int, rram_addr_key: int,
                  rram_data_key: int) -> int:
    operand_a = word_addr & RRAM_GF_OPERAND_A_MASK
    operand_b = rram_addr_key & RRAM_GF_OPERAND_B_MASK
    mask = RRAM_GF_2_128.Multiply(operand_a, operand_b)
    masked_data = data ^ mask
    # interleave data in two chunks
    masked_data_0, masked_data_1 = _interleave_split(masked_data)
    data_0 = prince.prince(masked_data_0, rram_data_key,
                           RRAM_PRINCE_NUM_HALF_ROUNDS)
    data_1 = prince.prince(masked_data_1, rram_data_key,
                           RRAM_PRINCE_NUM_HALF_ROUNDS)
    # return combined data
    return _interleave_combine(data_0, data_1) ^ mask


def _reformat_rram_vmem(
        rram_vmem_file: str,
        scrambling_configs: ScramblingConfigs) -> List[str]:
    # Open (raw) RRAM VMEM file and read into memory, skipping comment lines.
    try:
        rram_vmem = Path(rram_vmem_file).read_text()
    except IOError:
        raise Exception(f"Unable to open {rram_vmem_file}")
    rram_vmem_lines = re.findall(r"^@.*$", rram_vmem, flags=re.MULTILINE)

    # Add addr-infection and potentially scramble, each RRAM word.
    reformatted_vmem_lines = []
    for line in rram_vmem_lines:
        line_items = line.split()
        reformatted_line = ""
        address = None
        address_offset = 0
        data = None
        for item in line_items:
            # Process the address first.
            if re.match(r"^@", item):
                reformatted_line += item
                address = int(item.lstrip("@"), 16)
                address_offset = 0
            # Process the data words.
            else:
                rram_word_addr = address + address_offset
                if rram_word_addr >= RRAM_OTP_START_WORD_ADDR:
                    raise ValueError(
                        f"RRAM word address 0x{rram_word_addr:x} falls in the "
                        "OTP partition (starting at word address "
                        f"0x{RRAM_OTP_START_WORD_ADDR:x}), which this script "
                        "does not address-infect or scramble. Check "
                        "--in-rram-vmem's word size and offsets.")
                data = int(item, 16)
                # addr infection with word address
                new_data = 0
                for word_idx in range(RRAM_WORD_SIZE // 32):
                    chunk = (data >> (32 * word_idx)) & 0xFFFFFFFF
                    word_addr = ((address + address_offset) * 4) + word_idx
                    new_data |= ((chunk ^ word_addr) << (32 * word_idx))
                data = new_data
                if scrambling_configs.scrambling_enabled:
                    data = _xex_scramble(data, address + address_offset,
                                         scrambling_configs.addr_key,
                                         scrambling_configs.data_key)
                reformatted_line += str.format(VMEM_FORMAT_STR,
                                               data)
                address_offset += 1

        # Append reformatted line to what will be the new output VMEM file.
        reformatted_vmem_lines.append(reformatted_line)

    return reformatted_vmem_lines


def main(argv: List[str]):
    # Parse command line args.
    parser = argparse.ArgumentParser()
    parser.add_argument("--in-rram-vmem",
                        type=str,
                        required=True,
                        help="Input VMEM file to reformat.")

    parser.add_argument("--in-otp-vmem",
                        type=str,
                        help="Input OTP (VMEM) file to retrieve data from.")
    parser.add_argument('--top-secret-cfg',
                        type=Path,
                        metavar='<path>',
                        required=True,
                        help='''
                        Path to the top secret configuration in Hjson format.
                        ''')
    parser.add_argument("--out-rram-vmem",
                        type=str,
                        required=True,
                        help="Output VMEM file.")
    parser.add_argument("--otp-data-perm",
                        type=vmem_permutation_string,
                        metavar="<map>",
                        default=[],
                        help="""
                        This is a post-processing option and allows permuting
                        the bit positions before writing the memfile. The bit
                        mapping needs to be supplied as a comma separated list
                        of bit slices, where the numbers refer to the bit
                        positions in the original data word before remapping,
                        for example:

                        "[7:0],[15:8]".

                        The mapping must be bijective - otherwise this will
                        generate an error.
                        """)
    args = parser.parse_args(argv)
    scrambling_configs = ScramblingConfigs()

    # Validate OTP bit permutation configuration.
    if args.otp_data_perm:
        validate_data_perm_option(OTP_WORD_SIZE_WECC, args.otp_data_perm)

    # Read RRAM scrambling configurations (including: enablement, otp_ctrl
    # netlist consts, address and data key seeds) directly from OTP VMEM file.
    if args.in_otp_vmem:
        with open(args.top_secret_cfg, 'r') as infile:
            top_secret_cfg = hjson.load(infile)

        get_otp_ctrl_netlist_consts(top_secret_cfg, scrambling_configs)
        get_scrambling_configs_from_otp(args.in_otp_vmem, args.otp_data_perm,
                                        OTP_RRAM_DATA_DEFAULT_CFG_RE,
                                        scrambling_configs)

    # Compute RRAM scrambling keys from seeds.
    if scrambling_configs.scrambling_enabled:
        compute_scrambling_keys(scrambling_configs)

    # Reformat RRAM VMEM file to add address infection and scrambling.
    reformatted_vmem_lines = _reformat_rram_vmem(args.in_rram_vmem,
                                                 scrambling_configs)

    # Write re-formatted output file. Use binary mode and a large buffer size
    # to improve performance.
    with open(args.out_rram_vmem, "wb", buffering=2097152) as of:
        of.write("\n".join(reformatted_vmem_lines).encode('utf-8'))


if __name__ == "__main__":
    main(sys.argv[1:])
