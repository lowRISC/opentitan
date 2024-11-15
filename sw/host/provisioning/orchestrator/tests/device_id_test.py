# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Unittests for device_id.py module."""

import binascii
import unittest

import hjson
from device_id import DeviceId, DeviceIdentificationNumber
from sku_config import SkuConfig
from util import bytes_to_int, format_hex

_SIVAL_SKU_CONFIG = "sw/host/provisioning/orchestrator/configs/skus/sival.hjson"


class TestDeviceId(unittest.TestCase):

    def setUp(self):
        # Create SKU config object.
        with open(_SIVAL_SKU_CONFIG, "r") as fp:
            sku_config_args = hjson.load(fp)
        self.sku_config = SkuConfig(**sku_config_args)

        # Create DIN object.
        self.din = DeviceIdentificationNumber(year=4,
                                              week=49,
                                              lot=343,
                                              wafer=72,
                                              wafer_x_coord=635,
                                              wafer_y_coord=242)

        # Create DeviceId object.
        self.device_id = DeviceId(sku_config=self.sku_config, din=self.din)

    def test_si_creator_id_field(self):
        expected_field = 0x4001
        actual_field = self.device_id.to_int() & 0xffff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=4),
                format_hex(expected_field, width=4)))

    def test_product_id_field(self):
        expected_field = 0x0002
        actual_field = (self.device_id.to_int() >> 16) & 0xffff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=4),
                format_hex(expected_field, width=4)))

    def test_din_year_field(self):
        expected_field = 4
        actual_field = (self.device_id.to_int() >> 32) & 0xf
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=1),
                format_hex(expected_field, width=1)))

    def test_din_week_field(self):
        expected_field = 49
        actual_field = (self.device_id.to_int() >> 36) & 0xff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=2),
                format_hex(expected_field, width=2)))

    def test_din_lot_field(self):
        expected_field = 343
        actual_field = (self.device_id.to_int() >> 44) & 0xfff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=3),
                format_hex(expected_field, width=3)))

    def test_din_wafer_field(self):
        expected_field = 72
        actual_field = (self.device_id.to_int() >> 56) & 0xff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=2),
                format_hex(expected_field, width=2)))

    def test_din_wafer_x_coord_field(self):
        expected_field = 635
        actual_field = (self.device_id.to_int() >> 64) & 0xfff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=3),
                format_hex(expected_field, width=3)))

    def test_din_wafer_y_coord_field(self):
        expected_field = 242
        actual_field = (self.device_id.to_int() >> 76) & 0xfff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=3),
                format_hex(expected_field, width=3)))

    def test_din_reserved_field(self):
        expected_field = 0
        actual_field = (self.device_id.to_int() >> 88) & 0xff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=2),
                format_hex(expected_field, width=2)))

    def test_crc32_field(self):
        expected_field = binascii.crc32(
            ((self.din.to_int() << 32) | 0x00024001).to_bytes(
                length=12, byteorder="little"))
        actual_field = (self.device_id.to_int() >> 96) & 0xffffffff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=8),
                format_hex(expected_field, width=8)))

    def test_package_id_field(self):
        expected_field = 0x0
        actual_field = (self.device_id.to_int() >> 128) & 0xffff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=4),
                format_hex(expected_field, width=4)))

    def test_sku_specific_reserved_field_0(self):
        expected_field = 0
        actual_field = (self.device_id.to_int() >> 144) & 0xffff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=4),
                format_hex(expected_field, width=4)))

    def test_sku_id_field(self):
        expected_field = bytes_to_int("AVIS".encode("utf-8"))
        actual_field = (self.device_id.to_int() >> 160) & 0xffffffff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=8),
                format_hex(expected_field, width=8)))

    def test_sku_specific_reserved_field_1(self):
        expected_field = 0
        actual_field = (self.device_id.to_int() >> 224) & 0xffffffff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=8),
                format_hex(expected_field, width=8)))

    def test_pretty_print(self):
        self.device_id.pretty_print()


if __name__ == '__main__':
    unittest.main()
