#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Takes a compiled VMEM image and processes it for loading into the RRAM.

    Specifically, this takes a raw RRAM image, adds address infection and scrambles
    the data using the same XEX scrambling scheme used in the RRAM controller. This
    enables backdoor loading the RRAM on simulation platforms (e.g., DV and Verilator).

    --in-otp-vmem supplies OTP scrambling-key seeds for the firmware image above. If
    --out-otp-vmem is also given, a *separate* VMEM image of OTP's own content (data rows plus
    the Hamming(72,64) integrity page rram_ctrl_otp.sv expects, converted from gen-otp-img.py's
    native 16b-word format) is written there - not merged into --out-rram-vmem, since the two are
    loaded independently (see rram_ctrl_otp_bkdr_util.sv and hyperdebug.py) and may not even be
    the same OTP image.
"""

import argparse
import re
import sys
from pathlib import Path
from typing import List

import hjson
from pyfinite import ffield
from lib.common import (inverse_permute_bits, validate_data_perm_option,
                        vmem_permutation_string)
from lib.otp_scrambling_keys import (OTP_WORD_SIZE, OTP_WORD_SIZE_WECC,
                                     ScramblingConfigs,
                                     compute_scrambling_keys,
                                     get_otp_ctrl_netlist_consts,
                                     get_scrambling_configs_from_otp)

import prince
import secded_gen

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
# This is also where rram_ctrl_otp.sv's per-64b-chunk integrity page starts.
RRAM_OTP_START_WORD_ADDR = 4091 * 32
# First RRAM word address of OTP's actual data (one page after
# RRAM_OTP_START_WORD_ADDR - that first page is the integrity page).
# rram_ctrl_pkg::(OtpStartPage + 1) * WordsPerPage = 4092 * 32.
RRAM_OTP_DATA_START_WORD_ADDR = 4092 * 32

# How OTP's 16b-native words pack into RRAM's 128b words and integrity bytes.
# See rram_ctrl_otp.sv (OtpIntgDataWidth, OtpIntgWidth) and
# rram_ctrl_otp_bkdr_util.sv, which does this same transform for DV.
OTP_WORDS_PER_RRAM_WORD = RRAM_WORD_SIZE // OTP_WORD_SIZE  # 8
INTG_CHUNK_SIZE = 64  # bits covered by one integrity byte
INTG_BYTES_PER_RRAM_WORD = RRAM_WORD_SIZE // 8  # 16

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


def _group_otp_field_labels(labels: List[str]) -> str:
    """Formats a row's distinct "PARTITION: FIELD" labels (see _gen_otp_rram_vmem_lines) into one
    compact comment. otp_ctrl fields aren't sized to fall on 128b (8-native-word) boundaries, so
    one RRAM row commonly spans several fields; grouping by partition and dropping each field
    name's own partition-name prefix.
    """
    fields_by_partition = {}
    for label in labels:
        partition, _, field = label.partition(": ")
        if not field:
            partition, field = None, partition
        elif field.startswith(partition + "_"):
            field = field[len(partition) + 1:]
        fields_by_partition.setdefault(partition, []).append(field)

    return "; ".join(
        ", ".join(fields) if partition is None else f"{partition}: {', '.join(fields)}"
        for partition, fields in fields_by_partition.items())


def _gen_otp_rram_vmem_lines(otp_vmem_file: str,
                             otp_data_perm: list) -> List[str]:
    """Reads an OTP VMEM image (gen-otp-img.py's native 16b-word format, with the old
    otp_macro-specific Hamming(22,16) ECC) and returns VMEM lines placing its content the way
    rram_ctrl_otp.sv expects: 128b data rows plus a separate Hamming(72,64) integrity byte per
    64b chunk in its own page.
    """
    # Open (native-format) OTP VMEM file and read into memory, skipping comment lines.
    try:
        otp_vmem = Path(otp_vmem_file).read_text()
    except IOError:
        raise Exception(f"Unable to open {otp_vmem_file}")

    # Load project SECDED configuration, for the Hamming(72,64) syndrome below.
    ecc_configs = secded_gen.load_secded_config()

    # Read every native 16b OTP word into a dict keyed by its native word address, dropping the
    # old otp_macro-specific Hamming(22,16) ECC bits. Also keep the field names.
    data_words = {}
    data_word_labels = {}
    for line in re.findall(r"^@.*$", otp_vmem, flags=re.MULTILINE):
        addr_str, val_str = line.split()[:2]
        word_addr = int(addr_str.lstrip("@"), 16)
        word_w_ecc = int(val_str, 16)
        if otp_data_perm:
            # Undo --data-perm before slicing out the data bits below - otherwise they aren't
            # contiguous at word_w_ecc's low end any more.
            word_as_str = format(word_w_ecc, "0" + str(OTP_WORD_SIZE_WECC) + "b")
            word_w_ecc = int(inverse_permute_bits(word_as_str, otp_data_perm), 2)
        data_words[word_addr] = word_w_ecc & (2**OTP_WORD_SIZE - 1)
        label_match = re.search(r"//\s*(.*\S)\s*$", line)
        if label_match:
            data_word_labels[word_addr] = label_match.group(1)

    # One RRAM row holds OTP_WORDS_PER_RRAM_WORD native OTP words.
    num_rows = (max(data_words, default=-1) + OTP_WORDS_PER_RRAM_WORD) // OTP_WORDS_PER_RRAM_WORD

    rows = {}
    comments = {}
    intg_row_data_addrs = {}
    for row_idx in range(num_rows):
        # Pack OTP_WORDS_PER_RRAM_WORD consecutive native OTP words into one 128b data row.
        row = 0
        row_labels = []
        for k in range(OTP_WORDS_PER_RRAM_WORD):
            native_addr = row_idx * OTP_WORDS_PER_RRAM_WORD + k
            row |= data_words.get(native_addr, 0) << (k * OTP_WORD_SIZE)
            label = data_word_labels.get(native_addr)
            if label and label not in row_labels:
                row_labels.append(label)
        data_row_addr = RRAM_OTP_DATA_START_WORD_ADDR + row_idx
        rows[data_row_addr] = row
        # Name the row after the distinct field(s) its 8 packed OTP words came from - usually one,
        # but a row can straddle several fields when their sizes aren't a multiple of 8 words.
        comments[data_row_addr] = _group_otp_field_labels(row_labels) if row_labels else None

        # Each 128b data row covers two 64b integrity chunks (half 0 = low 64b, half 1 = high
        # 64b). Compute their Hamming(72,64) syndrome and place it in the integrity page.
        for half in range(RRAM_WORD_SIZE // INTG_CHUNK_SIZE):
            chunk = (row >> (half * INTG_CHUNK_SIZE)) & ((1 << INTG_CHUNK_SIZE) - 1)
            # ecc_encode returns {ECC bits, data bits}; the syndrome is the top 8 bits.
            codeword, _ = secded_gen.ecc_encode(ecc_configs, "hamming", INTG_CHUNK_SIZE, chunk)
            intg = (codeword >> INTG_CHUNK_SIZE) & 0xFF
            # chunk_idx counts 64b chunks from the start of OTP data; it doubles as the byte
            # offset into the integrity page, since that page stores exactly one byte per chunk.
            chunk_idx = row_idx * (RRAM_WORD_SIZE // INTG_CHUNK_SIZE) + half
            intg_row = RRAM_OTP_START_WORD_ADDR + chunk_idx // INTG_BYTES_PER_RRAM_WORD
            byte_idx = chunk_idx % INTG_BYTES_PER_RRAM_WORD
            # Multiple chunks land in the same integrity row - OR the new byte in rather than
            # overwrite, so earlier bytes placed in this same row survive.
            rows[intg_row] = rows.get(intg_row, 0) | (intg << (byte_idx * 8))
            # Track the range of data rows this integrity row protects.
            lo, _ = intg_row_data_addrs.get(intg_row, (data_row_addr, data_row_addr))
            intg_row_data_addrs[intg_row] = (lo, data_row_addr)

    for intg_row, (lo_addr, hi_addr) in intg_row_data_addrs.items():
        comments[intg_row] = f"integrity for data rows 0x{lo_addr:06x}-0x{hi_addr:06x}"

    # Zero-fill the integrity page's unused tail so the file covers the OTP region contiguously.
    # rram_ctrl_otp_bkdr_util.sv skips verifying these rows, so asserting 0 here is safe.
    last_data_row_addr = RRAM_OTP_DATA_START_WORD_ADDR + num_rows - 1
    for addr in range(RRAM_OTP_START_WORD_ADDR, last_data_row_addr + 1):
        if addr not in rows:
            rows[addr] = 0
            comments[addr] = "unused"

    # Emit one VMEM line per RRAM word address touched above (data rows and integrity rows,
    # interleaved in address order since integrity rows sit before the data they cover).
    lines = []
    for addr, val in sorted(rows.items()):
        line = f"@{addr:06x}" + str.format(VMEM_FORMAT_STR, val)
        if comments.get(addr):
            line += f"  // {comments[addr]}"
        lines.append(line)
    return lines


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
                        help="""
                        Input VMEM file to reformat. Required together with --out-rram-vmem
                        unless this invocation is only generating --out-otp-vmem.
                        """)

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
                        help="Output VMEM file. Required together with --in-rram-vmem.")
    parser.add_argument("--out-otp-vmem",
                        type=str,
                        help="""
                        Optional output VMEM file for OTP's own content (data rows plus the
                        Hamming(72,64) integrity page rram_ctrl_otp.sv expects), separate from
                        --out-rram-vmem. Requires --in-otp-vmem. Deliberately not merged into
                        --out-rram-vmem: the firmware image and OTP's image are loaded through
                        different paths and at different times (see rram_ctrl_otp_bkdr_util.sv
                        and hyperdebug.py), and --in-otp-vmem here may not even be the same OTP
                        image a given test actually selects at runtime - it is only meant to
                        supply scrambling-key seeds for the firmware image.
                        """)
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

    # Reformat RRAM VMEM file to add address infection and scrambling, unless this invocation is
    # only generating --out-otp-vmem.
    if args.in_rram_vmem or args.out_rram_vmem:
        if not (args.in_rram_vmem and args.out_rram_vmem):
            raise ValueError("--in-rram-vmem and --out-rram-vmem must be given together.")

        reformatted_vmem_lines = _reformat_rram_vmem(args.in_rram_vmem,
                                                     scrambling_configs)

        # Write re-formatted output file. Use binary mode and a large buffer size
        # to improve performance.
        with open(args.out_rram_vmem, "wb", buffering=2097152) as of:
            of.write("\n".join(reformatted_vmem_lines).encode('utf-8'))

    # Separately, generate OTP's own image (data + integrity page) if requested.
    if args.out_otp_vmem:
        if not args.in_otp_vmem:
            raise ValueError("--out-otp-vmem requires --in-otp-vmem.")
        otp_vmem_lines = _gen_otp_rram_vmem_lines(args.in_otp_vmem, args.otp_data_perm)
        with open(args.out_otp_vmem, "wb", buffering=2097152) as of:
            of.write("\n".join(otp_vmem_lines).encode('utf-8'))


if __name__ == "__main__":
    main(sys.argv[1:])
