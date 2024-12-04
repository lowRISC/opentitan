# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Module for computing OpenTitan device IDs."""

import struct
from dataclasses import dataclass
from typing import Optional

import util
from sku_config import SkuConfig

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
        din |= util.bcd_encode(self.wafer_y_coord) << 44
        din |= util.bcd_encode(self.wafer_x_coord) << 32
        din |= util.bcd_encode(self.wafer) << 24
        din |= util.bcd_encode(self.lot) << 12
        din |= util.bcd_encode(self.week) << 4
        din |= self.year
        return din

    @staticmethod
    def from_int(din: int) -> "DeviceIdentificationNumber":
        year = util.bcd_decode(din & 0xF)
        week = util.bcd_decode((din >> 4) & 0xFF)
        lot = util.bcd_decode((din >> 12) & 0xFFF)
        wafer = util.bcd_decode((din >> 24) & 0xFF)
        wafer_x_coord = util.bcd_decode((din >> 32) & 0xFFF)
        wafer_y_coord = util.bcd_decode((din >> 44) & 0xFFF)
        return DeviceIdentificationNumber(year=year,
                                          week=week,
                                          lot=lot,
                                          wafer=wafer,
                                          wafer_x_coord=wafer_x_coord,
                                          wafer_y_coord=wafer_y_coord)


class DeviceId():
    """An OpenTitan device ID.

    This object can generate different encodings of the device ID, including:
      - hex string, and
      - int.

    Attributes:
        si_creator_id: A 16-bit number assigned by the OpenTitan project.
        product_id: A 16-bit number assigned by the OpenTitan project.
        din: A 64-bit unique identifier.
        package_id: A 16-bit number indicating which package the chip is in.
        sku_id: A 32-bit string indicating the SKU the chip was provisioned for.
    """

    def __init__(self, sku_config: SkuConfig,
                 din: Optional[DeviceIdentificationNumber]):
        # Save string keys for easier printing.
        self._product = sku_config.product
        self._si_creator = sku_config.si_creator
        self._package = sku_config.package
        self.sku = sku_config.name

        # Build HW origin with:
        # - 16 bits SiliconCreator ID
        # - 16 bits Product ID
        self.si_creator_id = sku_config.si_creator_id
        self.product_id = sku_config.product_id
        self._hw_origin = util.bytes_to_int(
            struct.pack("<HH", self.si_creator_id, self.product_id))

        # Build Device Identification Number with:
        # - Year
        # - Week
        # - Lot #
        # - Wafer #
        # - Wafer X coord.
        # - Wafer Y coord.
        self.din = din

        din_as_int = 0
        if self.din is not None:
            din_as_int = self.din.to_int()

        # Build base unique ID.
        self._base_uid = util.bytes_to_int(
            struct.pack("<IQI", self._hw_origin, din_as_int, 0))

        # Build SKU specific field.
        self.package_id = sku_config.package_id
        self.sku_id = util.bytes_to_int(
            self.sku.upper()[:4].encode("utf-8")[::-1])
        self.sku_specific = util.bytes_to_int(
            struct.pack(
                "<HHIQ",
                self.package_id,
                _RESERVED_WORD,
                self.sku_id,
                _RESERVED_WORD,
            ))

        # Build full device ID.
        self.device_id = (self.sku_specific << 128) | self._base_uid

    def update_base_id(self, other: "DeviceId") -> None:
        """Updates the base unique ID with another DeviceId object.

        Updates the base_id with another DeviceId object's base_id as well as
        the HW origin, SiliconCreator ID, and Product ID.

        Args:
            other: The other DeviceId object to update with.
        """
        self.si_creator_id = other.si_creator_id
        self.product_id = other.product_id
        self._hw_origin = other._hw_origin

        self.din = other.din
        self._base_uid = other._base_uid
        self.device_id = (self.sku_specific << 128) | self._base_uid

    @staticmethod
    def from_hexstr(hexstr: str) -> "DeviceId":
        """Creates a DeviceId object from a hex string."""
        cp_device_id = util.parse_hexstring_to_int(hexstr)
        return DeviceId.from_int(cp_device_id)

    @staticmethod
    def from_int(device_id: int) -> "DeviceId":
        """Creates a DeviceId object from an int."""
        # Extract SKU specific field.
        sku_specific = device_id >> 128
        package_id = sku_specific & 0xFFFF
        sku_id = (sku_specific >> 32) & 0xFFFFFFFF

        # Extract base unique ID.
        mask = (1 << 128) - 1
        base_uid = device_id & mask
        # Extract HW origin.
        hw_origin = base_uid & 0xFFFFFFFF
        si_creator_id = hw_origin & 0xFFFF
        product_id = (hw_origin >> 16) & 0xFFFF

        # Extract SKU config.
        sku_config = SkuConfig.from_ids(product_id, si_creator_id, package_id)

        try:
            sku_name = struct.pack('>I', sku_id).decode('ascii')
        except UnicodeDecodeError:
            sku_name = "Unknown"
        sku_config.name = sku_name

        # Extract DIN.
        mask_din = (1 << 64) - 1
        din = DeviceIdentificationNumber.from_int((base_uid >> 32) & mask_din)

        return DeviceId(sku_config, din)

    def to_hexstr(self) -> str:
        """Returns the device ID as a hex string."""
        return util.format_hex(self.device_id, width=64)

    def to_int(self) -> int:
        """Returns the device ID as an int."""
        return self.device_id

    def pretty_print(self):
        print("> Device ID:       {}".format(self))
        print("SiliconCreator ID: {} ({})".format(
            util.format_hex(self.si_creator_id, width=4), self._si_creator))
        print("Product ID:        {} ({})".format(
            util.format_hex(self.product_id, width=4), self._product))
        if self.din is not None:
            print("DIN Year:          {}".format(self.din.year))
            print("DIN Week:          {}".format(self.din.week))
            print("DIN Lot:           {}".format(self.din.lot))
            print("DIN Wafer:         {}".format(self.din.wafer))
            print("DIN Wafer X Coord: {}".format(self.din.wafer_x_coord))
            print("DIN Wafer Y Coord: {}".format(self.din.wafer_y_coord))
        else:
            print("DIN:               <unset>")
        print("Reserved:          {}".format(hex(0)))
        print("SKU ID:            {} ({})".format(
            util.format_hex(self.sku_id),
            self.sku_id.to_bytes(length=4, byteorder="big").decode("utf-8")))
        print("Package ID:        {} ({})".format(self.package_id,
                                                  self._package))

    def __str__(self):
        return self.to_hexstr()
