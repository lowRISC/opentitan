#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Takes a compiled VMEM image and processes it for loading into flash.

    Specifically, this takes a raw flash image and adds both layers of ECC
    (integrity and reliability), and optionally, scrambles the data using the
    same XEX scrambling scheme used in the flash controller. This enables
    backdoor loading the flash on simulation platforms (e.g., DV and Verilator).
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
import secded_gen

OTP_NVM_DATA_DEFAULT_CFG_RE = re.compile(
    r"CREATOR_SW_CFG: CREATOR_SW_CFG_NVM_DATA_DEFAULT_CFG")

# Flash data / scrambling parameters.
FLASH_ADDR_KEY_SIZE = 128  # bits
FLASH_DATA_KEY_SIZE = 128  # bits
FLASH_WORD_SIZE = 64  # bits
FLASH_ADDR_SIZE = 16  # bits
FLASH_INTEGRITY_ECC_SIZE = 4  # bits
FLASH_RELIABILITY_ECC_SIZE = 8  # bits
FLASH_PRINCE_NUM_HALF_ROUNDS = 5

# ------------------------------------------------------------------------------
# DO NOT EDIT: edit fixed parameters above instead.
# ------------------------------------------------------------------------------
FLASH_GF_OPERAND_B_MASK = (2**FLASH_WORD_SIZE) - 1
FLASH_GF_OPERAND_A_MASK = (
    FLASH_GF_OPERAND_B_MASK &
    ~(0xffff << (FLASH_WORD_SIZE - FLASH_ADDR_SIZE))) << FLASH_WORD_SIZE
# Create GF(2^64) with irreducible_polynomial = x^64 + x^4 + x^3 + x + 1
FLASH_GF_2_64 = ffield.FField(64,
                              gen=((0x1 << 64) | (0x1 << 4) | (0x1 << 3) |
                                   (0x1 << 1) | 0x1))

# Format string for generating new VMEM file.
FLASH_VMEM_WORD_SIZE = (FLASH_WORD_SIZE + FLASH_INTEGRITY_ECC_SIZE +
                        FLASH_RELIABILITY_ECC_SIZE)
VMEM_FORMAT_STR = " {:0" + f"{FLASH_VMEM_WORD_SIZE // 4}" + "X}"
# ------------------------------------------------------------------------------


def _xex_scramble(data: int, word_addr: int, flash_addr_key: int,
                  flash_data_key: int) -> int:
    operand_a = ((flash_addr_key & FLASH_GF_OPERAND_A_MASK) >>
                 (FLASH_WORD_SIZE - FLASH_ADDR_SIZE)) | word_addr
    operand_b = flash_addr_key & FLASH_GF_OPERAND_B_MASK
    mask = FLASH_GF_2_64.Multiply(operand_a, operand_b)
    masked_data = data ^ mask
    return prince.prince(masked_data, flash_data_key,
                         FLASH_PRINCE_NUM_HALF_ROUNDS) ^ mask


def _reformat_flash_vmem(
        flash_vmem_file: str,
        scrambling_configs: ScramblingConfigs) -> List[str]:
    # Open (raw) flash VMEM file and read into memory, skipping comment lines.
    try:
        flash_vmem = Path(flash_vmem_file).read_text()
    except IOError:
        raise Exception(f"Unable to open {flash_vmem_file}")
    flash_vmem_lines = re.findall(r"^@.*$", flash_vmem, flags=re.MULTILINE)

    # Load project SECDED configuration.
    ecc_configs = secded_gen.load_secded_config()

    # Add integrity/reliability ECC, and potentially scramble, each flash word.
    reformatted_vmem_lines = []
    for line in flash_vmem_lines:
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
                data = int(item, 16)
                # `data_w_intg_ecc` will be in format {ECC bits, data bits}.
                data_w_intg_ecc, _ = secded_gen.ecc_encode(
                    ecc_configs, "hamming", FLASH_WORD_SIZE, data)
                # Due to storage constraints the first nibble of ECC is dropped.
                data_w_intg_ecc &= 0xF_FFFF_FFFF_FFFF_FFFF
                if scrambling_configs.scrambling_enabled:
                    intg_ecc = data_w_intg_ecc & (0xF << FLASH_WORD_SIZE)
                    data = _xex_scramble(data, address + address_offset,
                                         scrambling_configs.addr_key,
                                         scrambling_configs.data_key)
                    data_w_intg_ecc = intg_ecc | data
                # `data_w_full_ecc` will be in format {reliability ECC bits,
                # integrity ECC bits, data bits}.
                data_w_full_ecc, _ = secded_gen.ecc_encode(
                    ecc_configs, "hamming",
                    FLASH_WORD_SIZE + FLASH_INTEGRITY_ECC_SIZE,
                    data_w_intg_ecc)
                reformatted_line += str.format(VMEM_FORMAT_STR,
                                               data_w_full_ecc)
                address_offset += 1

        # Append reformatted line to what will be the new output VMEM file.
        reformatted_vmem_lines.append(reformatted_line)

    return reformatted_vmem_lines


def main(argv: List[str]):
    # Parse command line args.
    parser = argparse.ArgumentParser()
    parser.add_argument("--in-flash-vmem",
                        type=str,
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
    parser.add_argument("--out-flash-vmem", type=str, help="Output VMEM file.")
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

    # Read flash scrambling configurations (including: enablement, otp_ctrl
    # netlist consts, address and data key seeds) directly from OTP VMEM file.
    if args.in_otp_vmem:
        with open(args.top_secret_cfg, 'r') as infile:
            top_secret_cfg = hjson.load(infile)

        get_otp_ctrl_netlist_consts(top_secret_cfg, scrambling_configs)
        get_scrambling_configs_from_otp(args.in_otp_vmem, args.otp_data_perm,
                                        OTP_NVM_DATA_DEFAULT_CFG_RE,
                                        scrambling_configs)

    # Compute flash scrambling keys from seeds.
    if scrambling_configs.scrambling_enabled:
        compute_scrambling_keys(scrambling_configs)

    # Reformat flash VMEM file to add integrity/reliability ECC and scrambling.
    reformatted_vmem_lines = _reformat_flash_vmem(args.in_flash_vmem,
                                                  scrambling_configs)

    # Write re-formatted output file. Use binary mode and a large buffer size
    # to improve performance.
    with open(args.out_flash_vmem, "wb", buffering=2097152) as of:
        of.write("\n".join(reformatted_vmem_lines).encode('utf-8'))


if __name__ == "__main__":
    main(sys.argv[1:])
