#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Generate immutable ROM_EXT section data from ELF file and JSON overlay."""

import argparse
import json
import logging
import sys

import hjson
from Crypto.Hash import SHA256
from elftools.elf import elffile

_OTP_PARTITION_NAME = "CREATOR_SW_CFG"

_OTTF_START_OFFSET_SYMBOL_NAME = "_ottf_start_address"
_ROM_EXT_IMMUTABLE_SECTION_NAME = ".rom_ext_immutable"

_START_OFFSET_FIELD_NAME = "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_START_OFFSET"
_SIZE_FIELD_NAME = "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_LENGTH"
_HASH_FIELD_NAME = "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_SHA256_HASH"


class RomExtImmutableSectionOtpFields:

    def __init__(self, rom_ext_elf, json_data):
        self.rom_ext_elf = rom_ext_elf
        self.json_data = json_data
        self.immutable_section_idx = None
        self.manifest_offset = None
        self.start_offset = None
        self.size_in_bytes = None
        self.hash = None
        with open(self.rom_ext_elf, 'rb') as f:
            elf = elffile.ELFFile(f)
            # Find the offset of the current slot we are in.
            for symbol in elf.get_section_by_name(".symtab").iter_symbols():
                if symbol.name == _OTTF_START_OFFSET_SYMBOL_NAME:
                    self.manifest_offset = symbol.entry["st_value"]
            assert self.manifest_offset, "Manifest start address not found."

            # Find the immutable section and compute the OTP values.
            for section_idx in range(elf.num_sections()):
                section = elf.get_section(section_idx)
                if section.name == _ROM_EXT_IMMUTABLE_SECTION_NAME:
                    self.immutable_section_idx = section_idx
                    self.start_offset = (int(section.header['sh_addr']) -
                                         self.manifest_offset)
                    self.size_in_bytes = int(section.header['sh_size'])
                    assert self.size_in_bytes == len(section.data())
                    # Prepend the start offset and length to section data
                    data_to_hash = bytearray()
                    data_to_hash += self.start_offset.to_bytes(
                        4, byteorder='little')
                    data_to_hash += self.size_in_bytes.to_bytes(
                        4, byteorder='little')
                    data_to_hash += section.data()
                    self.hash = bytearray(SHA256.new(data_to_hash).digest())

    def insert_key_value(self, item_name: str, value: str):
        """Insert the value of the item if it does not exist.
        Args:
            item_name: The name of the item to insert.
            value: The value to insert the item with.
        Returns:
            None
        """
        for partition in self.json_data["partitions"]:
            if partition["name"] == _OTP_PARTITION_NAME:
                for item in partition["items"]:
                    if item["name"] == item_name:
                        return
                partition["items"].append({"name": item_name, "value": value})

    def update_json_with_immutable_rom_ext_section_data(self):
        """Update the JSON with the ROM_EXT immutable section data.
        Args:
            None
        Returns:
            None
        """
        self.insert_key_value(_START_OFFSET_FIELD_NAME,
                              f"{hex(self.start_offset)}")
        self.insert_key_value(_SIZE_FIELD_NAME, f"{hex(self.size_in_bytes)}")
        self.insert_key_value(_HASH_FIELD_NAME, f"0x{self.hash.hex()}")


def main():
    parser = argparse.ArgumentParser(
        prog="gen-otp-immutable-rom-ext-json",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('-i',
                        '--input',
                        type=str,
                        metavar='<path>',
                        help='Input JSON file path.')
    parser.add_argument('-e',
                        '--elf',
                        type=str,
                        metavar='<path>',
                        help='Input ELF file path.')
    parser.add_argument('-o',
                        '--output',
                        type=str,
                        metavar='<path>',
                        help='Output JSON file path.')
    args = parser.parse_args()

    # Read in the OTP fields (encoded in JSON) we will be updating.
    json_in = None
    with open(args.input, 'r') as f:
        json_in = hjson.load(f)

    # Extract the immutable ROM_EXT section data, compute hash, and update OTP
    # CREATOR_SW_CFG partition fields.
    imm_section_otp = RomExtImmutableSectionOtpFields(args.elf, json_in)
    if not imm_section_otp.immutable_section_idx:
        logging.error("Cannot find {} section in ROM_EXT ELF {}.".format(
            _ROM_EXT_IMMUTABLE_SECTION_NAME, args.elf))
        sys.exit(1)
    imm_section_otp.update_json_with_immutable_rom_ext_section_data()

    # Write out the OTP fields to a JSON file.
    with open(args.output, 'w') as f:
        f.write(json.dumps(imm_section_otp.json_data, indent=4))


if __name__ == "__main__":
    main()
