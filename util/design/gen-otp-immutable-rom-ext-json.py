#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Generate immutable ROM_EXT section data from ELF file and JSON overlay."""

import argparse
import json

import hjson
from lib.ImmutableSectionProcessor import ImmutableSectionProcessor
from typing import Optional

_OTP_PARTITION_NAME = "CREATOR_SW_CFG"

_ENABLE_FIELD_NAME = "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN"
_START_OFFSET_FIELD_NAME = "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_START_OFFSET"
_SIZE_FIELD_NAME = "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_LENGTH"
_HASH_FIELD_NAME = "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_SHA256_HASH"
_CREATOR_MANUF_STATE_FIELD_NAME = "CREATOR_SW_CFG_MANUF_STATE"

# This must match the definitions in hardened.h.
_HARDENED_TRUE = 0x739


class RomExtImmutableSectionOtpFields(ImmutableSectionProcessor):

    def __init__(self, rom_ext_elf, json_data):
        super().__init__(rom_ext_elf, json_data)

    def insert_key_value(self, item_name: str, value: str) -> None:
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

    def get_key_value(self, item_name: str) -> Optional[str]:
        """Get the value of the item if it exists.
        Args:
            item_name: The name of the item to insert.
        Returns:
            The value of the item if found, otherwise None.
        """
        for partition in self.json_data["partitions"]:
            if partition["name"] == _OTP_PARTITION_NAME:
                for item in partition["items"]:
                    if item["name"] == item_name:
                        return str(item["value"])
        return None

    def update_json_with_immutable_rom_ext_section_data(self) -> None:
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

    def update_json_with_creator_manuf_state_data(self) -> None:
        """Update the JSON with the CREATOR_SW_CFG_MANUF_STATE data.
        Args:
            None
        Returns:
            None
        """

        new_creator_manuf_state = self.update_creator_manuf_state_data(
            f"0x{self.hash.hex()}"
        )
        self.insert_key_value(
            _CREATOR_MANUF_STATE_FIELD_NAME, new_creator_manuf_state
        )

    def immutable_rom_ext_enable(self) -> bool:
        """Checks if immutable ROM extension is enabled.

        This method retrieves the value of the enable field from the OTP
        partition and compares it with the hardened true value.

        Returns:
            True if immutable ROM extension is enabled, False otherwise.
        """
        immutable_rom_ext_en = self.get_key_value(_ENABLE_FIELD_NAME)
        if immutable_rom_ext_en is None:
            return False
        immutable_rom_ext_en_value = int(immutable_rom_ext_en, 0)
        return immutable_rom_ext_en_value == _HARDENED_TRUE


def main() -> None:
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

    if imm_section_otp.immutable_rom_ext_enable():
        imm_section_otp.update_json_with_immutable_rom_ext_section_data()
        imm_section_otp.update_json_with_creator_manuf_state_data()

    # Write out the OTP fields to a JSON file.
    with open(args.output, 'w') as f:
        f.write(json.dumps(imm_section_otp.json_data, indent=4))


if __name__ == "__main__":
    main()
