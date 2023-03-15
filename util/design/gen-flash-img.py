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
import re
import sys
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import List

from pyfinite import ffield
from util.design.lib.Present import Present

import prince
import secded_gen

# Fixed OTP data / scrambling parameters.
OTP_WORD_SIZE = 16  # bits
OTP_SECRET1_RE = re.compile(r"SECRET1")
OTP_SECRET1_BLOCK_SIZE = 64  # bits
OTP_SECRET1_PRESENT_KEY = 0x5703C3EB2BB563689E00A67814EFBDE8
OTP_SECRET1_PRESENT_KEY_LENGTH = 128  # bits
OTP_SECRET1_PRESENT_NUM_ROUNDS = 32
OTP_FLASH_ADDR_KEY_SEED_SIZE = 256  # bits
OTP_FLASH_DATA_KEY_SEED_SIZE = 256  # bits

# Computed OTP data / scrambling parameters.
# ------------------------------------------------------------------------------
# DO NOT EDIT: edit fixed parameters above instead.
# ------------------------------------------------------------------------------
OTP_SECRET1_PRESENT_CIPHER = Present(OTP_SECRET1_PRESENT_KEY,
                                     rounds=OTP_SECRET1_PRESENT_NUM_ROUNDS,
                                     keylen=OTP_SECRET1_PRESENT_KEY_LENGTH)
OTP_SECRET1_FLASH_ADDR_KEY_SEED_START = 0
OTP_SECRET1_FLASH_ADDR_KEY_SEED_STOP = (OTP_FLASH_ADDR_KEY_SEED_SIZE //
                                        OTP_SECRET1_BLOCK_SIZE)
OTP_SECRET1_FLASH_DATA_KEY_SEED_START = (OTP_FLASH_ADDR_KEY_SEED_SIZE //
                                         OTP_SECRET1_BLOCK_SIZE)
OTP_SECRET1_FLASH_DATA_KEY_SEED_STOP = OTP_SECRET1_FLASH_DATA_KEY_SEED_START + (
    OTP_FLASH_DATA_KEY_SEED_SIZE // OTP_SECRET1_BLOCK_SIZE)
# ------------------------------------------------------------------------------

# Flash data / scrambling parameters.
FLASH_ADDR_KEY_SIZE = 128  # bits
FLASH_DATA_KEY_SIZE = 128  # bits
FLASH_WORD_SIZE = 64  # bits
FLASH_ADDR_SIZE = 16  # bits
FLASH_INTEGRITY_ECC_SIZE = 4  # bits
FLASH_RELIABILITY_ECC_SIZE = 8  # bits
FLASH_PRINCE_NUM_HALF_ROUNDS = 5

# Computed flash data / scrambling parameters.
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
# ------------------------------------------------------------------------------


class FlashScramblingKeyType(Enum):
    ADDRESS = 1
    DATA = 2


# Flash scrambling key computation parameters.
KEY_TYPE_2_IV = {
    FlashScramblingKeyType.ADDRESS: 0x97883548F536F544,
    FlashScramblingKeyType.DATA: 0xC5F5C1D8AEF35040,
}
KEY_TYPE_2_FINALIZATION_CONST = {
    FlashScramblingKeyType.ADDRESS: 0x39AED01B4B2277312E9480868216A281,
    FlashScramblingKeyType.DATA: 0x1D888AC88259C44AAB06CB4A4C65A7EA,
}
FLASH_KEY_COMPUTATION_KEY_SIZE = OTP_FLASH_ADDR_KEY_SEED_SIZE // 2
FLASH_KEY_COMPUTATION_KEY_MASK = (2**FLASH_KEY_COMPUTATION_KEY_SIZE) - 1


@dataclass
class FlashScramblingConfigs:
    scrambling_enabled: bool = False
    addr_key_seed: int = None
    data_key_seed: int = None
    addr_key: int = None
    data_key: int = None


@functools.lru_cache(maxsize=None)
def _xex_scramble(data: int, word_addr: int, flash_addr_key: int,
                  flash_data_key: int) -> int:
    operand_a = ((flash_addr_key & FLASH_GF_OPERAND_A_MASK) >>
                 (FLASH_WORD_SIZE - FLASH_ADDR_SIZE)) | word_addr
    operand_b = flash_addr_key & FLASH_GF_OPERAND_B_MASK
    mask = FLASH_GF_2_64.Multiply(operand_a, operand_b)
    masked_data = data ^ mask
    return prince.prince(masked_data, flash_data_key,
                         FLASH_PRINCE_NUM_HALF_ROUNDS) ^ mask


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


def _get_flash_scrambling_configs(otp_vmem_file: str,
                                  configs: FlashScramblingConfigs) -> None:
    # Open OTP VMEM file and read into memory, skipping comment lines.
    try:
        otp_vmem = Path(otp_vmem_file).read_text()
    except IOError:
        raise Exception(f"Unable to open {otp_vmem}")
    otp_vmem_lines = re.findall(r"^@.*$", otp_vmem, flags=re.MULTILINE)

    # TODO: Retrieve partition with the flash scrambling enablement flags.
    configs.scrambling_enabled = False

    # Retrieve SECRET1 partition which contains the flash scrambling key seeds,
    # stripping ECC bits from each data word when processing.
    data_blocks_64bit = []
    data_block_64bit = 0
    idx = 0
    for line in otp_vmem_lines:
        if OTP_SECRET1_RE.search(line):
            otp_data_word_w_ecc = int(line.split()[1], 16)
            otp_data_word = otp_data_word_w_ecc & (2**OTP_WORD_SIZE - 1)
            data_block_64bit |= otp_data_word << (idx * OTP_WORD_SIZE)
            idx += 1
            if idx == (64 // OTP_WORD_SIZE):
                data_blocks_64bit.append(data_block_64bit)
                data_block_64bit = 0
                idx = 0

    # Descramble SECRET1 partition data blocks and extract flash scrambling key
    # seeds. The SECRET1 partition layout looks like:
    # {FLASH_ADDR_KEY_SEED, FLASH_DATA_KEY_SEED, SRAM_DATA_KEY_SEED, DIGEST}
    descrambled_data_blocks = list(
        map(OTP_SECRET1_PRESENT_CIPHER.decrypt, data_blocks_64bit))
    configs.addr_key_seed = _convert_array_2_int(
        descrambled_data_blocks[OTP_SECRET1_FLASH_ADDR_KEY_SEED_START:
                                OTP_SECRET1_FLASH_ADDR_KEY_SEED_STOP],
        OTP_SECRET1_BLOCK_SIZE)
    configs.data_key_seed = _convert_array_2_int(
        descrambled_data_blocks[OTP_SECRET1_FLASH_DATA_KEY_SEED_START:
                                OTP_SECRET1_FLASH_DATA_KEY_SEED_STOP],
        OTP_SECRET1_BLOCK_SIZE)


def _compute_flash_scrambling_key(scrambling_configs: FlashScramblingConfigs,
                                  key_type: FlashScramblingKeyType) -> int:
    if key_type == FlashScramblingKeyType.ADDRESS:
        key_seed = scrambling_configs.addr_key_seed
    else:
        key_seed = scrambling_configs.data_key_seed
    full_key = 0
    for i in range(2):
        round_1_present_key = (key_seed >>
                               (FLASH_KEY_COMPUTATION_KEY_SIZE *
                                i)) & FLASH_KEY_COMPUTATION_KEY_MASK
        key_half = 0
        for j in range(2):
            if j == 0:
                cipher = Present(round_1_present_key)
                key_half = cipher.encrypt(
                    KEY_TYPE_2_IV[key_type]) ^ KEY_TYPE_2_IV[key_type]
            else:
                cipher = Present(KEY_TYPE_2_FINALIZATION_CONST[key_type])
                key_half = cipher.encrypt(key_half) ^ key_half
        full_key |= key_half << (64 * i)
    return full_key


def _compute_flash_scrambling_keys(
        scrambling_configs: FlashScramblingConfigs) -> None:
    scrambling_configs.addr_key = _compute_flash_scrambling_key(
        scrambling_configs, FlashScramblingKeyType.ADDRESS)
    scrambling_configs.data_key = _compute_flash_scrambling_key(
        scrambling_configs, FlashScramblingKeyType.DATA)


def _reformat_flash_vmem(
        flash_vmem_file: str,
        scrambling_configs: FlashScramblingConfigs) -> List[str]:
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
                    ecc_configs, "hamming", FLASH_WORD_SIZE, data)
                # Due to storage constraints the first nibble of ECC is dropped.
                data_w_intg_ecc &= 0xF_FFFF_FFFF_FFFF_FFFF
                if scrambling_configs.scrambling_enabled:
                    intg_ecc = data_w_intg_ecc & (0xF << FLASH_WORD_SIZE)
                    data = _xex_scramble(data, address,
                                         scrambling_configs.addr_key,
                                         scrambling_configs.data_key)
                    data_w_intg_ecc = intg_ecc | data
                # `data_w_full_ecc` will be in format {reliablity ECC bits,
                # integrity ECC bits, data bits}.
                data_w_full_ecc, _ = secded_gen.ecc_encode(
                    ecc_configs, "hamming",
                    FLASH_WORD_SIZE + FLASH_INTEGRITY_ECC_SIZE,
                    data_w_intg_ecc)
                reformatted_line += f" {data_w_full_ecc:x}"

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
    parser.add_argument("--out-flash-vmem", type=str, help="Output VMEM file.")
    args = parser.parse_args(argv)

    # Read flash scrambling configurations (including: enablement, address and
    # data key seeds) directly from OTP VMEM file.
    scrambling_configs = FlashScramblingConfigs()
    if args.in_otp_vmem:
        _get_flash_scrambling_configs(args.in_otp_vmem, scrambling_configs)

    # Compute flash scrambling keys from seeds.
    if scrambling_configs.scrambling_enabled:
        _compute_flash_scrambling_keys(scrambling_configs)

    # Reformat flash VMEM file to add integrity/reliablity ECC and scrambling.
    reformatted_vmem_lines = _reformat_flash_vmem(args.in_flash_vmem,
                                                  scrambling_configs)

    # Write re-formatted output file.
    with open(args.out_flash_vmem, "w") as of:
        of.writelines(reformatted_vmem_lines)


if __name__ == "__main__":
    main(sys.argv[1:])
