#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Extract the immutable ROM_EXT section data from ELF file."""

import logging
import sys

from Crypto.Hash import SHA256
from elftools.elf import elffile

_OTTF_START_OFFSET_SYMBOL_NAME = "_ottf_start_address"
_ROM_EXT_SATRT_OFFSET_SYMBOL_NAME = "_rom_ext_start_address"
_ROM_EXT_IMMUTABLE_SECTION_NAME = ".rom_ext_immutable"

_PREFIX_FOR_HEX = "0x"


class ImmutableSectionProcessor:

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
                if symbol.name in [
                    _OTTF_START_OFFSET_SYMBOL_NAME,
                    _ROM_EXT_SATRT_OFFSET_SYMBOL_NAME,
                ]:
                    if self.manifest_offset is not None:
                        raise ValueError(
                            f"More than one manifest start address exists. "
                            f"Current offset: {self.manifest_offset}, "
                            f"new offset: {symbol.entry['st_value']}"
                        )
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

        if not self.immutable_section_idx:
            logging.error("Cannot find {} section in ROM_EXT ELF {}.".format(
                _ROM_EXT_IMMUTABLE_SECTION_NAME, self.rom_ext_elf))
            sys.exit(1)

    def update_creator_manuf_state_data(self, im_ext_hash) -> None:
        """Update the creator's manufacturing state with the immutable ROM_EXT hash.
        Args:
            im_ext_hash: The immutable ROM_EXT hash as a hexadecimal string.
        Returns:
            The updated manufacturing state as a hexadecimal string.
        Raises:
            ValueError: If the immutable ROM_EXT hash are all zeros in the
                        first four bytes.
        """

        # Check if the hash value starts with the hexadecimal prefix.
        if im_ext_hash[:2] == _PREFIX_FOR_HEX:
            # Remove the hexadecimal prefix.
            im_ext_hash = im_ext_hash[2:]
        # Pad with leading zeros to ensure 4 bytes long.
        im_ext_hash = im_ext_hash.zfill(8)

        # Ensure the hash is different from the `PERSO_INITIAL` defined in
        # rules/const.bzl.
        if im_ext_hash[:8] == "0" * 8:
            raise ValueError("The hash value are all zeros.")

        # Embed the first four bytes of `IMMUTABLE_ROM_EXT_SHA256_HASH` into
        # `CREATOR_MANUF_STATE`
        creator_manuf_state = (
            _PREFIX_FOR_HEX + im_ext_hash[:8]
        )

        return creator_manuf_state
