#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Update the creator_manuf_state in a ROM_EXT manifest."""

import argparse
import json

import hjson

from lib.ImmutableSectionProcessor import ImmutableSectionProcessor

_USAGE_CONSTRAINTS_NAME = "usage_constraints"
_MANUF_STATE_CREATOR_NAME = "manuf_state_creator"
_SELECTOR_BITS_NAME = "selector_bits"
_IDENTIFIER_NAME = "identifier"

_SEL_MANUF_STATE_CREATOR = (1 << 8)

# This must match the definitions in chip.h.
_CHIP_ROM_EXT_IDENTIFIER = 0x4552544f


class RomExtImmutableSection(ImmutableSectionProcessor):

    def __init__(self, rom_ext_elf, json_data):
        super().__init__(rom_ext_elf, json_data)

    def update_manifest_with_creator_manuf_state_data(self) -> None:
        """Update the manifest with the manuf_state_creator data.
        Args:
            None
        Returns:
            None
        """

        selector_bits = self.json_data[_USAGE_CONSTRAINTS_NAME][
            _SELECTOR_BITS_NAME]

        # Ensure the selector bit of `manuf_state_creator` field is set.
        new_selector_bits = selector_bits | _SEL_MANUF_STATE_CREATOR

        new_creator_manuf_state = self.update_creator_manuf_state_data(
            f"0x{self.hash.hex()}")

        self.json_data[_USAGE_CONSTRAINTS_NAME][
            _MANUF_STATE_CREATOR_NAME] = new_creator_manuf_state

        self.json_data[_USAGE_CONSTRAINTS_NAME][
            _SELECTOR_BITS_NAME] = new_selector_bits

    def is_rom_ext_manifest(self) -> bool:
        """Check if the loaded manifest is for a ROM_EXT image.

        This function determines if the loaded JSON manifest data corresponds to
        a ROM_EXT image by checking the identifier field in the manifest.

        Returns:
            True if the manifest is for a ROM_EXT image, False otherwise.
        """
        identifier = self.json_data[_IDENTIFIER_NAME]
        identifier_value = int(identifier, 0)
        return identifier_value == _CHIP_ROM_EXT_IDENTIFIER


def main() -> None:
    parser = argparse.ArgumentParser(
        prog="update-manifest-json",
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

    # Read in the manifest fields (encoded in JSON) we will be updating.
    json_in = None
    with open(args.input, 'r') as f:
        json_in = hjson.load(f)

    # Extract the immutable ROM_EXT section data, compute hash, and update
    # manifest `manuf_state_creator` binding field
    rom_ext_immutable_section = RomExtImmutableSection(args.elf, json_in)

    if rom_ext_immutable_section.is_rom_ext_manifest():
        rom_ext_immutable_section.update_manifest_with_creator_manuf_state_data(
        )

    # Write out the new `manuf_state_creator` field to a JSON file.
    with open(args.output, 'w') as f:
        f.write(json.dumps(rom_ext_immutable_section.json_data, indent=4))


if __name__ == "__main__":
    main()
