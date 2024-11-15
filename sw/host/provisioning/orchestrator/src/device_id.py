# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Module for computing OpenTitan device IDs."""

import binascii
import struct
from dataclasses import dataclass

from sku_config import SkuConfig
from util import bytes_to_int, format_hex

_RESERVED_WORD = 0


@dataclass
class DeviceIdentificationNumber:
    """Class for storing Device Identification Number portion of Device ID."""
    year: int = 0  # valid range: [0, 9]
    week: int = 0  # valid range: [0, 51]
    lot: int = 0  # valid range: [0, 999]
    wafer: int = 0  # valid range: [0,99]
    wafer_x_coord: int = 0  # valid range: [0, 999]
    wafer_y_coord: int = 0  # valid range: [0, 999]

    def __post_init__(self):
        self.validate()

    def validate(self) -> None:
        """Validates this object's attributes."""
        # Validate year.
        if not 0 <= self.year <= 9:
            raise ValueError("Year ({}) must be in [0, 9].".format(self.year))
        # Validate week.
        if not 0 <= self.week <= 51:
            raise ValueError("Week ({}) must be in [0, 51].".format(self.week))
        # Validate lot.
        if not 0 <= self.lot <= 999:
            raise ValueError("Lot ({}) must be in [0, 999].".format(self.lot))
        # Validate wafer.
        if not 0 <= self.wafer <= 99:
            raise ValueError("Wafer ({}) must be in [0, 99].".format(
                self.wafer))
        # Validate wafer X coordinate.
        if not 0 <= self.wafer_x_coord <= 999:
            raise ValueError(
                "Wafer X coordinate ({}) must be in [0, 999].".format(
                    self.wafer_x_coord))
        # Validate wafer Y coordinate.
        if not 0 <= self.wafer_y_coord <= 999:
            raise ValueError(
                "Wafer Y coordinate ({}) must be in [0, 999].".format(
                    self.wafer_y_coord))

    def to_int(self) -> int:
        din = 0
        din |= self.wafer_y_coord << 44
        din |= self.wafer_x_coord << 32
        din |= self.wafer << 24
        din |= self.lot << 12
        din |= self.week << 4
        din |= self.year
        return din


class DeviceId():
    """An OpenTitan device ID.

    This object can generate different encodings of the device ID, including:
      - hex string, and
      - int.

    Attributes:
        si_creator_id: A 16-bit number assigned by the OpenTitan project.
        product_id: A 16-bit number assigned by the OpenTitan project.
        din: A 64-bit unique identifier.
        crc32: A CRC32 over the above 96-bits.
        package_id: A 16-bit number indicating which package the chip is in.
        sku_id: A 32-bit string indicating the SKU the chip was provisioned for.
    """

    def __init__(self, sku_config: SkuConfig, din: DeviceIdentificationNumber):
        # Save string keys for easier printing.
        self._product = sku_config.product
        self._si_creator = sku_config.si_creator
        self._package = sku_config.package
        self._sku = sku_config.name

        # Build HW origin with:
        # - 16 bits SiliconCreator ID
        # - 16 bits Product ID
        self.si_creator_id = sku_config.si_creator_id
        self.product_id = sku_config.product_id
        self._hw_origin = bytes_to_int(
            struct.pack("<HH", self.si_creator_id, self.product_id))

        # Build Device Identification Number with:
        # - Year
        # - Week
        # - Lot #
        # - Wafer #
        # - Wafer X coord.
        # - Wafer Y coord.
        self.din = din

        # Build CRC32 over HW origin + DIN.
        self.crc32 = binascii.crc32(
            struct.pack("<IQ", self._hw_origin, self.din.to_int()))

        # Build base unique ID.
        self._base_uid = bytes_to_int(
            struct.pack("<IQI", self._hw_origin, self.din.to_int(),
                        self.crc32))

        # Build SKU specific field.
        self.package_id = sku_config.package_id
        self.sku_id = bytes_to_int(self._sku.upper()[:4].encode("utf-8")[::-1])
        self._sku_specific = bytes_to_int(
            struct.pack(
                "<HHIQ",
                self.package_id,
                _RESERVED_WORD,
                self.sku_id,
                _RESERVED_WORD,
            ))

        # Build full device ID.
        self.device_id = (self._sku_specific << 128) | self._base_uid

    def to_hexstr(self) -> str:
        """Returns the device ID as a hex string."""
        return format_hex(self.device_id, width=64)

    def to_int(self) -> int:
        """Returns the device ID as an int."""
        return self.device_id

    def pretty_print(self):
        print("> Device ID:       {}".format(self))
        print("SiliconCreator ID: {} ({})".format(
            format_hex(self.si_creator_id, width=4), self._si_creator))
        print("Product ID:        {} ({})".format(
            format_hex(self.product_id, width=4), self._product))
        print("DIN Year:          {}".format(self.din.year))
        print("DIN Week:          {}".format(self.din.week))
        print("DIN Lot:           {}".format(self.din.lot))
        print("DIN Wafer:         {}".format(self.din.wafer))
        print("DIN Wafer X Coord: {}".format(self.din.wafer_x_coord))
        print("DIN Wafer Y Coord: {}".format(self.din.wafer_y_coord))
        print("SKU ID:            {} ({})".format(
            format_hex(self.sku_id),
            self.sku_id.to_bytes(length=4, byteorder="big").decode("utf-8")))
        print("Package ID:        {} ({})".format(self.package_id,
                                                  self._package))
        print("CRC32:             {}".format(hex(self.crc32)))

    def __str__(self):
        return self.to_hexstr()
