# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Shared OTP scrambling-key derivation code.

Reads a technology's scrambling-enablement flag and SECRET1 key seeds from an
OTP VMEM image (plus the Present cipher key/IVs from the OTP netlist config),
then derives the two Present scrambling keys from them. This is the
tech-agnostic first half shared by gen-flash-img.py and gen-rram-img.py; what
happens to the derived keys afterwards (the XEX operand construction, which
depends on the technology's GF field size) diverges per technology and stays
in each script.
"""

import re
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import List

from lib.common import check_int, inverse_permute_bits
from lib.Present import Present

MUBI4_TRUE = 0x6

# Fixed OTP data / scrambling parameters. Identical for flash and RRAM today:
# both read the same OTP hardware fields and Present-decrypt them the same
# way.
OTP_WORD_SIZE = 16  # bits
OTP_WORD_SIZE_WECC = 24  # bits
OTP_DATA_DEFAULT_CFG_BLOCK_SIZE = 32  # bits
OTP_SECRET1_RE = re.compile(r"SECRET1")
OTP_SECRET1_BLOCK_SIZE = 64  # bits
OTP_SECRET1_PRESENT_KEY_LENGTH = 128  # bits
OTP_SECRET1_PRESENT_NUM_ROUNDS = 32
OTP_ADDR_KEY_SEED_SIZE = 256  # bits
OTP_DATA_KEY_SEED_SIZE = 256  # bits
OTP_SECRET1_ADDR_KEY_SEED_START = 0

# Scrambling key computation parameters.
# ------------------------------------------------------------------------------
# DO NOT EDIT: edit fixed parameters above instead.
# ------------------------------------------------------------------------------
OTP_SECRET1_ADDR_KEY_SEED_STOP = (OTP_ADDR_KEY_SEED_SIZE //
                                  OTP_SECRET1_BLOCK_SIZE)
OTP_SECRET1_DATA_KEY_SEED_START = (OTP_ADDR_KEY_SEED_SIZE //
                                   OTP_SECRET1_BLOCK_SIZE)
OTP_SECRET1_DATA_KEY_SEED_STOP = OTP_SECRET1_DATA_KEY_SEED_START + (
    OTP_DATA_KEY_SEED_SIZE // OTP_SECRET1_BLOCK_SIZE)

KEY_COMPUTATION_KEY_SIZE = OTP_ADDR_KEY_SEED_SIZE // 2
KEY_COMPUTATION_KEY_MASK = (2**KEY_COMPUTATION_KEY_SIZE) - 1
# ------------------------------------------------------------------------------


class ScramblingKeyType(Enum):
    ADDRESS = 1
    DATA = 2


@dataclass
class ScramblingConfigs:
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

    def get_iv(self, key_type: ScramblingKeyType):
        if key_type == ScramblingKeyType.ADDRESS:
            return self.addr_key_iv
        else:
            return self.data_key_iv

    def get_final_cnst(self, key_type: ScramblingKeyType):
        if key_type == ScramblingKeyType.ADDRESS:
            return self.addr_key_final_const
        else:
            return self.data_key_final_const


def convert_array_2_int(data_array: List[int],
                        data_size: int,
                        little_endian=True) -> int:
    """Converts array of data blocks to an int."""
    reformatted_data = 0
    if not little_endian:
        data_array.reverse()
    for i, data in enumerate(data_array):
        reformatted_data |= (data << (i * data_size))
    return reformatted_data


def get_otp_ctrl_netlist_consts(top_secret_cfg: dict,
                                scrambling_configs: ScramblingConfigs) -> None:
    for module in top_secret_cfg["module"]:
        if module.get("template_type") == "otp_ctrl":
            otp_map = module["otp_mmap"]
            break
    else:
        raise RuntimeError(
            "OTP memory map configuration not found in top secret configuration"
        )

    # Extract OTP secret1 partition scrambling key.
    for key in otp_map["scrambling"]["keys"]:
        if key["name"] == "Secret1Key":
            scrambling_configs.otp_secret1_key = check_int(key["value"])

    # Extract OTP NVM scrambling key IVs.
    for digest in otp_map["scrambling"]["digests"]:
        if digest["name"] == "NvmAddrKey":
            scrambling_configs.addr_key_iv = check_int(digest["iv_value"])
            scrambling_configs.addr_key_final_const = check_int(
                digest["cnst_value"])
        if digest["name"] == "NvmDataKey":
            scrambling_configs.data_key_iv = check_int(digest["iv_value"])
            scrambling_configs.data_key_final_const = check_int(
                digest["cnst_value"])


def get_scrambling_configs_from_otp(otp_vmem_file: str, otp_data_perm: list,
                                    data_default_cfg_re: re.Pattern,
                                    configs: ScramblingConfigs) -> None:
    """Reads `configs`'s key seeds (and scrambling-enablement flag) from an OTP VMEM image.

    `data_default_cfg_re` matches the OTP VMEM comment line carrying the
    NVM scrambling-enablement flag (e.g.
    CREATOR_SW_CFG_NVM_DATA_DEFAULT_CFG); callers own this in case it comes
    to differ per top.
    """
    # Open OTP VMEM file and read into memory, skipping comment lines.
    try:
        otp_vmem = Path(otp_vmem_file).read_text()
    except IOError:
        raise Exception(f"Unable to open {otp_vmem_file}")
    otp_vmem_lines = re.findall(r"^@.*$", otp_vmem, flags=re.MULTILINE)

    # Retrieve OTP data from the following partitions:
    # - CREATOR_SW_CFG: which contains the scramble enablement flag, and
    # - SECRET1: which contains the scrambling key seeds.
    # Note, we strip ECC bits from each data word when processing.
    data_default_cfg = None
    secret1_data_blocks = []
    otp_data_block = 0
    idx = 0
    for line in otp_vmem_lines:
        if (data_default_cfg_re.search(line) or OTP_SECRET1_RE.search(line)):
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
            if data_default_cfg_re.search(line):
                if idx == (OTP_DATA_DEFAULT_CFG_BLOCK_SIZE // OTP_WORD_SIZE):
                    data_default_cfg = otp_data_block & 0xff
                    # If data scrambling is disabled, then we can return
                    # early to save execution time.
                    if data_default_cfg != MUBI4_TRUE:
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
    if data_default_cfg is None:
        raise RuntimeError("Cannot read scrambling enablement state from OTP.")
    if not secret1_data_blocks:
        raise RuntimeError("Cannot read scrambling key seeds from OTP.")

    # Descramble SECRET1 partition data blocks and extract scrambling key
    # seeds. The SECRET1 partition layout looks like:
    # {NVM_ADDR_KEY_SEED, NVM_DATA_KEY_SEED, SRAM_DATA_KEY_SEED, DIGEST}
    otp_secret1_present_cipher = Present(configs.otp_secret1_key,
                                         rounds=OTP_SECRET1_PRESENT_NUM_ROUNDS,
                                         keylen=OTP_SECRET1_PRESENT_KEY_LENGTH)
    descrambled_secret1_blocks = list(
        map(otp_secret1_present_cipher.decrypt, secret1_data_blocks))
    configs.addr_key_seed = convert_array_2_int(
        descrambled_secret1_blocks[OTP_SECRET1_ADDR_KEY_SEED_START:
                                   OTP_SECRET1_ADDR_KEY_SEED_STOP],
        OTP_SECRET1_BLOCK_SIZE)
    configs.data_key_seed = convert_array_2_int(
        descrambled_secret1_blocks[OTP_SECRET1_DATA_KEY_SEED_START:
                                   OTP_SECRET1_DATA_KEY_SEED_STOP],
        OTP_SECRET1_BLOCK_SIZE)


def compute_scrambling_key(scrambling_configs: ScramblingConfigs,
                           key_type: ScramblingKeyType) -> int:
    if key_type == ScramblingKeyType.ADDRESS:
        key_seed = scrambling_configs.addr_key_seed
    else:
        key_seed = scrambling_configs.data_key_seed
    full_key = 0
    for i in range(2):
        round_1_present_key = (key_seed >>
                               (KEY_COMPUTATION_KEY_SIZE * i)) & KEY_COMPUTATION_KEY_MASK
        key_half = 0
        for j in range(2):
            if j == 0:
                cipher = Present(round_1_present_key)
                key_half = cipher.encrypt(
                    scrambling_configs.get_iv(key_type)) ^ scrambling_configs.get_iv(
                        key_type)
            else:
                cipher = Present(scrambling_configs.get_final_cnst(key_type))
                key_half = cipher.encrypt(key_half) ^ key_half
        full_key |= key_half << (64 * i)
    return full_key


def compute_scrambling_keys(scrambling_configs: ScramblingConfigs) -> None:
    scrambling_configs.addr_key = compute_scrambling_key(
        scrambling_configs, ScramblingKeyType.ADDRESS)
    scrambling_configs.data_key = compute_scrambling_key(
        scrambling_configs, ScramblingKeyType.DATA)
