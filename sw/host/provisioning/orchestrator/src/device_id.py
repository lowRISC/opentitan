# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Module for computing OpenTitan device IDs."""

import struct
from dataclasses import dataclass

import util
from sku_config import SkuConfig

_RESERVED_VALUE = 0

# This defines the format of the "sku_specific" portion of the device ID. This
# should be updated everytime the the "sku_specific" portion of the device ID is
# updated.
_SKU_SPECIFIC_FORMAT_VERSION = 1


@dataclass
class DeviceIdentificationNumber:
    """Class for storing Device Identification Number portion of Device ID.

    DINs for blind assembly parts have all values set to -1 or (UINT*_MAX).
    """
    year: int = 0  # valid range: [0, 9]
    week: int = 0  # valid range: [0, 51]
    lot: int = 0  # valid range: [0, 999]
    wafer: int = 0  # valid range: [0,99]
    wafer_x_coord: int = 0  # valid range: [0, 999]
    wafer_y_coord: int = 0  # valid range: [0, 999]
    blind_asm: bool = False  # boolean indicating if blind assembly part

    def __post_init__(self):
        # Check if blind assembly part, if so, we skip field validation.
        if (self.year == -1 and self.week == -1 and self.lot == -1 and
                self.wafer == -1 and self.wafer_x_coord == -1 and
                self.wafer_y_coord == -1):
            self.blind_asm = True
        else:
            self.blind_asm = False
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
        """Convert DIN to an int."""
        # If blind assembly part, the DIN is UINT64_MAX.
        if self.blind_asm:
            return 2**64 - 1
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

    @staticmethod
    def blind_asm() -> "DeviceIdentificationNumber":
        return DeviceIdentificationNumber(year=-1,
                                          week=-1,
                                          lot=-1,
                                          wafer=-1,
                                          wafer_x_coord=-1,
                                          wafer_y_coord=-1)


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

    def __init__(self, sku_config: SkuConfig, din: DeviceIdentificationNumber):
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
        din_as_int = self.din.to_int()

        # Build base unique ID (i.e., CP device ID).
        self._base_uid = util.bytes_to_int(
            struct.pack("<IQI", self._hw_origin, din_as_int, 0))

        # Build SKU specific field (i.e., FT device ID).
        self.package_id = sku_config.package_id
        self.ast_cfg_version = sku_config.ast_cfg_version
        self.otp_id = util.bytes_to_int(
            sku_config.otp.upper()[0:2].encode("utf-8")[::-1])
        self.otp_version = sku_config.otp_version
        self.sku_id = util.bytes_to_int(
            self.sku.upper()[:4].encode("utf-8")[::-1])
        self.sku_specific_version = _SKU_SPECIFIC_FORMAT_VERSION
        self.sku_specific = util.bytes_to_int(
            struct.pack(
                "<BBHBBHIHBB",
                self.package_id,
                self.ast_cfg_version,
                self.otp_id,
                self.otp_version,
                _RESERVED_VALUE,
                _RESERVED_VALUE,
                self.sku_id,
                _RESERVED_VALUE,
                _RESERVED_VALUE,
                self.sku_specific_version,
            ))

        # Build full device ID.
        self.device_id = (self.sku_specific << 128) | self._base_uid

    def update_din(self, other: "DeviceIdentificationNumber") -> None:
        """Updates the DIN component of the device ID with another DIN object.

        Updates the DeviceIdentificationNumber (DIN) component of the device ID.

        Args:
            other: The other DeviceIdentificationNumber object to update with.
        """
        self.din = other

        # Build base unique ID.
        self._base_uid = util.bytes_to_int(
            struct.pack("<IQI", self._hw_origin, self.din.to_int(), 0))
        self.device_id = (self.sku_specific << 128) | self._base_uid

    @staticmethod
    def from_hexstr(hexstr: str) -> "DeviceId":
        """Creates a DeviceId object from a hex string."""
        device_id_int = util.parse_hexstring_to_int(hexstr)
        return DeviceId.from_int(device_id_int)

    @staticmethod
    def from_int(device_id: int) -> "DeviceId":
        """Creates a DeviceId object from an int."""
        # Extract base unique ID.
        mask = (1 << 128) - 1
        base_uid = device_id & mask
        # Extract HW origin.
        hw_origin = base_uid & 0xFFFFFFFF
        si_creator_id = hw_origin & 0xFFFF
        product_id = (hw_origin >> 16) & 0xFFFF

        # Extract SKU specific field.
        sku_specific = device_id >> 128
        package_id = sku_specific & 0xFF
        ast_cfg_version = (sku_specific >> 8) & 0xFF
        otp_id = (sku_specific >> 16) & 0xFFFF
        otp_version = (sku_specific >> 32) & 0xFF
        sku_id = (sku_specific >> 64) & 0xFFFFFFFF

        # Unpack OTP name.
        try:
            otp = (struct.pack('>H', otp_id).decode('ascii') +
                   f"{otp_version:02x}")
        except UnicodeDecodeError:
            otp = "Invalid"

        # Extract SKU config.
        sku_config = SkuConfig.from_ids(product_id, si_creator_id, package_id,
                                        otp, ast_cfg_version)

        # Unpack SKU name.
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
        print("> Device ID:          {}".format(self))
        print("SiliconCreator ID:    {} ({})".format(
            util.format_hex(self.si_creator_id, width=4), self._si_creator))
        print("Product ID:           {} ({})".format(
            util.format_hex(self.product_id, width=4), self._product))
        if self.din is not None:
            print("DIN Year:             {}".format(self.din.year))
            print("DIN Week:             {}".format(self.din.week))
            print("DIN Lot:              {}".format(self.din.lot))
            print("DIN Wafer:            {}".format(self.din.wafer))
            print("DIN Wafer X Coord:    {}".format(self.din.wafer_x_coord))
            print("DIN Wafer Y Coord:    {}".format(self.din.wafer_y_coord))
        else:
            print("DIN:               <unset>")
        print("Reserved (40 bits):   {}".format(hex(_RESERVED_VALUE)))
        print("Package ID:           {} ({})".format(self.package_id,
                                                     self._package))
        print("AST Config Version:   {}".format(self.ast_cfg_version))
        print("OTP ID:               {} ({})".format(
            hex(self.otp_id),
            self.otp_id.to_bytes(length=4, byteorder="big").decode("utf-8")))
        print("OTP Version:          {}".format(self.otp_version))
        print("Reserved (24 bits):   {}".format(hex(_RESERVED_VALUE)))
        print("SKU ID:               {} ({})".format(
            util.format_hex(self.sku_id),
            self.sku_id.to_bytes(length=4, byteorder="big").decode("utf-8")))
        print("Reserved (24 bits):   {}".format(hex(_RESERVED_VALUE)))
        print("SKU Specific Version: {}".format(self.sku_specific_version))

    def __str__(self):
        return self.to_hexstr()

    def __eq__(self, other):
        return self.device_id == other.device_id
