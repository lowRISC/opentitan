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
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import List

import hjson
from pyfinite import ffield
from lib.common import (check_int,
                        inverse_permute_bits,
                        validate_data_perm_option,
                        vmem_permutation_string)
from lib.Present import Present

import prince

MUBI4_TRUE = 0x6

# Fixed OTP data / scrambling parameters.
OTP_WORD_SIZE = 16  # bits
OTP_WORD_SIZE_WECC = 24  # bits
OTP_RRAM_DATA_DEFAULT_CFG_RE = re.compile(
    r"CREATOR_SW_CFG: CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG")
OTP_RRAM_DATA_DEFAULT_CFG_BLOCK_SIZE = 32  # bits
OTP_SECRET1_RE = re.compile(r"SECRET1")
OTP_SECRET1_BLOCK_SIZE = 64  # bits
OTP_SECRET1_PRESENT_KEY_LENGTH = 128  # bits
OTP_SECRET1_PRESENT_NUM_ROUNDS = 32
OTP_RRAM_ADDR_KEY_SEED_SIZE = 256  # bits
OTP_RRAM_DATA_KEY_SEED_SIZE = 256  # bits
OTP_SECRET1_RRAM_ADDR_KEY_SEED_START = 0

# RRAM data / scrambling parameters.
RRAM_ADDR_KEY_SIZE = 128  # bits
RRAM_DATA_KEY_SIZE = 128  # bits
RRAM_WORD_SIZE = 128  # bits
RRAM_ADDR_SIZE = 17  # bits
RRAM_PRINCE_NUM_HALF_ROUNDS = 5


class RramScramblingKeyType(Enum):
    ADDRESS = 1
    DATA = 2


# RRAM scrambling key computation parameters.
# ------------------------------------------------------------------------------
# DO NOT EDIT: edit fixed parameters above instead.
# ------------------------------------------------------------------------------
# Computed OTP data / scrambling parameters.
OTP_SECRET1_RRAM_ADDR_KEY_SEED_STOP = (OTP_RRAM_ADDR_KEY_SEED_SIZE // OTP_SECRET1_BLOCK_SIZE)
OTP_SECRET1_RRAM_DATA_KEY_SEED_START = (OTP_RRAM_ADDR_KEY_SEED_SIZE // OTP_SECRET1_BLOCK_SIZE)
OTP_SECRET1_RRAM_DATA_KEY_SEED_STOP = OTP_SECRET1_RRAM_DATA_KEY_SEED_START + (
    OTP_RRAM_DATA_KEY_SEED_SIZE // OTP_SECRET1_BLOCK_SIZE)

# Computed RRAM data / scrambling parameters.
RRAM_KEY_COMPUTATION_KEY_SIZE = OTP_RRAM_ADDR_KEY_SEED_SIZE // 2
RRAM_KEY_COMPUTATION_KEY_MASK = (2**RRAM_KEY_COMPUTATION_KEY_SIZE) - 1
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


@dataclass
class RramScramblingConfigs:
    scrambling_enabled: bool = False
    otp_secret1_key: int = None
    addr_key_iv: int = None
    data_key_iv: int = None
    addr_key_final_const: int = None
    data_key_final_const: int = None
    addr_key_seed: int = None
    data_key_seed: int = None
    addr_key: int = None
    data_key: int = None

    def get_iv(self, key_type: RramScramblingKeyType):
        if key_type == RramScramblingKeyType.ADDRESS:
            return self.addr_key_iv
        else:
            return self.data_key_iv

    def get_final_cnst(self, key_type: RramScramblingKeyType):
        if key_type == RramScramblingKeyType.ADDRESS:
            return self.addr_key_final_const
        else:
            return self.data_key_final_const


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


def _convert_array_2_int(data_array: List[int],
                         data_size: int,
                         little_endian=True) -> int:
    """Converts array of data blocks to an int."""
    reformatted_data = 0
    if not little_endian:
        data_array.reverse()
    for i, data in enumerate(data_array):
        reformatted_data |= (data << (i * data_size))
    return reformatted_data


def _get_otp_ctrl_netlist_consts(top_secret_cfg: dict, scrambling_configs: RramScramblingConfigs):

    for module in top_secret_cfg["module"]:
        if module.get("template_type") == "otp_ctrl":
            otp_map = module["otp_mmap"]
            break
    else:
        raise RuntimeError("OTP memory map configuration not found in top secret configuration")

    # Extract OTP secret1 partition scrambling key.
    for key in otp_map["scrambling"]["keys"]:
        if key["name"] == "Secret1Key":
            scrambling_configs.otp_secret1_key = check_int(key["value"])

    # Extract OTP NVM scrambling key IVs.
    for digest in otp_map["scrambling"]["digests"]:
        if digest["name"] == "NvmAddrKey":
            scrambling_configs.addr_key_iv = check_int(digest["iv_value"])
            scrambling_configs.addr_key_final_const = check_int(digest["cnst_value"])
        if digest["name"] == "NvmDataKey":
            scrambling_configs.data_key_iv = check_int(digest["iv_value"])
            scrambling_configs.data_key_final_const = check_int(digest["cnst_value"])


def _get_rram_scrambling_configs(otp_vmem_file: str, otp_data_perm: list,
                                 configs: RramScramblingConfigs) -> None:
    # Open OTP VMEM file and read into memory, skipping comment lines.
    try:
        otp_vmem = Path(otp_vmem_file).read_text()
    except IOError:
        raise Exception(f"Unable to open {otp_vmem_file}")
    otp_vmem_lines = re.findall(r"^@.*$", otp_vmem, flags=re.MULTILINE)

    # Retrieve OTP data from the following partitions:
    # - CREATOR_SW_CFG: which contains the RRAM scramble enablement flag, and
    # - SECRET1: which contains the RRAM scrambling key seeds.
    # Note, we strip ECC bits from each data word when processing.
    rram_data_default_cfg = None
    secret1_data_blocks = []
    otp_data_block = 0
    idx = 0
    for line in otp_vmem_lines:
        if (OTP_RRAM_DATA_DEFAULT_CFG_RE.search(line) or
                OTP_SECRET1_RE.search(line)):
            # Convert OTP VMEM word from string to int.
            otp_data_word_w_ecc = int(line.split()[1], 16)
            # Un-permute bits if necessary.
            if otp_data_perm:
                otp_data_word_as_str = format(
                    otp_data_word_w_ecc, "0" + str(OTP_WORD_SIZE_WECC) + "b")
                otp_data_word_w_ecc = int(
                    inverse_permute_bits(otp_data_word_as_str, otp_data_perm),
                    2)
            # Drop ECC bits.
            otp_data_word = otp_data_word_w_ecc & (2**OTP_WORD_SIZE - 1)
            otp_data_block |= otp_data_word << (idx * OTP_WORD_SIZE)
            idx += 1
            if OTP_RRAM_DATA_DEFAULT_CFG_RE.search(line):
                if idx == (OTP_RRAM_DATA_DEFAULT_CFG_BLOCK_SIZE //
                           OTP_WORD_SIZE):
                    rram_data_default_cfg = otp_data_block & 0xff
                    # If RRAM data scrambling is disabled, then we can return
                    # early to save execution time.
                    if rram_data_default_cfg != MUBI4_TRUE:
                        configs.scrambling_enabled = False
                        return
                    configs.scrambling_enabled = True
                    otp_data_block = 0
                    idx = 0
            if OTP_SECRET1_RE.search(line):
                if idx == (OTP_SECRET1_BLOCK_SIZE // OTP_WORD_SIZE):
                    secret1_data_blocks.append(otp_data_block)
                    otp_data_block = 0
                    idx = 0

    # Check we found the data we were looking for in the OTP image.
    if rram_data_default_cfg is None:
        raise RuntimeError(
            "Cannot read RRAM scrambling enablement state from OTP.")
    if not secret1_data_blocks:
        raise RuntimeError("Cannot read RRAM scrambling key seeds from OTP.")

    # Descramble SECRET1 partition data blocks and extract RRAM scrambling key
    # seeds. The SECRET1 partition layout looks like:
    # {RRAM_ADDR_KEY_SEED, RRAM_DATA_KEY_SEED, SRAM_DATA_KEY_SEED, DIGEST}
    otp_secret1_present_cipher = Present(configs.otp_secret1_key,
                                         rounds=OTP_SECRET1_PRESENT_NUM_ROUNDS,
                                         keylen=OTP_SECRET1_PRESENT_KEY_LENGTH)
    descrambled_secret1_blocks = list(
        map(otp_secret1_present_cipher.decrypt, secret1_data_blocks))
    configs.addr_key_seed = _convert_array_2_int(
        descrambled_secret1_blocks[OTP_SECRET1_RRAM_ADDR_KEY_SEED_START:
                                   OTP_SECRET1_RRAM_ADDR_KEY_SEED_STOP],
        OTP_SECRET1_BLOCK_SIZE)
    configs.data_key_seed = _convert_array_2_int(
        descrambled_secret1_blocks[OTP_SECRET1_RRAM_DATA_KEY_SEED_START:
                                   OTP_SECRET1_RRAM_DATA_KEY_SEED_STOP],
        OTP_SECRET1_BLOCK_SIZE)


def _compute_rram_scrambling_key(scrambling_configs: RramScramblingConfigs,
                                 key_type: RramScramblingKeyType) -> int:
    if key_type == RramScramblingKeyType.ADDRESS:
        key_seed = scrambling_configs.addr_key_seed
    else:
        key_seed = scrambling_configs.data_key_seed
    full_key = 0
    for i in range(2):
        round_1_present_key = (key_seed >>
                               (RRAM_KEY_COMPUTATION_KEY_SIZE *
                                i)) & RRAM_KEY_COMPUTATION_KEY_MASK
        key_half = 0
        for j in range(2):
            if j == 0:
                cipher = Present(round_1_present_key)
                key_half = cipher.encrypt(scrambling_configs.get_iv(
                    key_type)) ^ scrambling_configs.get_iv(key_type)
            else:
                cipher = Present(scrambling_configs.get_final_cnst(key_type))
                key_half = cipher.encrypt(key_half) ^ key_half
        full_key |= key_half << (64 * i)
    return full_key


def _compute_rram_scrambling_keys(
        scrambling_configs: RramScramblingConfigs) -> None:
    scrambling_configs.addr_key = _compute_rram_scrambling_key(
        scrambling_configs, RramScramblingKeyType.ADDRESS)
    scrambling_configs.data_key = _compute_rram_scrambling_key(
        scrambling_configs, RramScramblingKeyType.DATA)


def _reformat_rram_vmem(
        rram_vmem_file: str,
        scrambling_configs: RramScramblingConfigs) -> List[str]:
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
    parser.add_argument("--out-rram-vmem", type=str, help="Output VMEM file.")
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
    scrambling_configs = RramScramblingConfigs()

    # Validate OTP bit permutation configuration.
    if args.otp_data_perm:
        validate_data_perm_option(OTP_WORD_SIZE_WECC, args.otp_data_perm)

    # Read RRAM scrambling configurations (including: enablement, otp_ctrl
    # netlist consts, address and data key seeds) directly from OTP VMEM file.
    if args.in_otp_vmem:
        with open(args.top_secret_cfg, 'r') as infile:
            top_secret_cfg = hjson.load(infile)

        _get_otp_ctrl_netlist_consts(top_secret_cfg, scrambling_configs)
        _get_rram_scrambling_configs(args.in_otp_vmem, args.otp_data_perm,
                                     scrambling_configs)

    # Compute RRAM scrambling keys from seeds.
    if scrambling_configs.scrambling_enabled:
        _compute_rram_scrambling_keys(scrambling_configs)

    # Reformat RRAM VMEM file to add integrity/reliability ECC and scrambling.
    reformatted_vmem_lines = _reformat_rram_vmem(args.in_rram_vmem,
                                                 scrambling_configs)

    # Write re-formatted output file. Use binary mode and a large buffer size
    # to improve performance.
    with open(args.out_rram_vmem, "wb", buffering=2097152) as of:
        of.write("\n".join(reformatted_vmem_lines).encode('utf-8'))


if __name__ == "__main__":
    main(sys.argv[1:])
