# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Unittests for device_id.py module."""

import unittest

import hjson
from device_id import DeviceId, DeviceIdentificationNumber
from sku_config import SkuConfig
from util import bcd_encode, bytes_to_int, format_hex

_SIVAL_SKU_CONFIG = "sw/host/provisioning/orchestrator/configs/skus/emulation.hjson"


class TestDeviceId(unittest.TestCase):

    def setUp(self):
        # Create SKU config object.
        with open(_SIVAL_SKU_CONFIG, "r") as fp:
            sku_config_args = hjson.load(fp)
        self.sku_config = SkuConfig(ast_cfg_version=7, **sku_config_args)

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
        expected_field = bcd_encode(49)
        actual_field = (self.device_id.to_int() >> 36) & 0xff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=2),
                format_hex(expected_field, width=2)))

    def test_din_lot_field(self):
        expected_field = bcd_encode(343)
        actual_field = (self.device_id.to_int() >> 44) & 0xfff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=3),
                format_hex(expected_field, width=3)))

    def test_din_wafer_field(self):
        expected_field = bcd_encode(72)
        actual_field = (self.device_id.to_int() >> 56) & 0xff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=2),
                format_hex(expected_field, width=2)))

    def test_din_wafer_x_coord_field(self):
        expected_field = bcd_encode(635)
        actual_field = (self.device_id.to_int() >> 64) & 0xfff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=3),
                format_hex(expected_field, width=3)))

    def test_din_wafer_y_coord_field(self):
        expected_field = bcd_encode(242)
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

    def test_uid_reserved_field(self):
        expected_field = 0
        actual_field = (self.device_id.to_int() >> 96) & 0xffffffff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=8),
                format_hex(expected_field, width=8)))

    def test_package_id_field(self):
        expected_field = 0x0
        actual_field = (self.device_id.to_int() >> 128) & 0xff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=2),
                format_hex(expected_field, width=2)))

    def test_ast_cfg_version_field(self):
        expected_field = 0x7
        actual_field = (self.device_id.to_int() >> 136) & 0xff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=2),
                format_hex(expected_field, width=2)))

    def test_otp_id_field(self):
        expected_field = bytes_to_int("ME".encode("utf-8"))
        actual_field = (self.device_id.to_int() >> 144) & 0xffff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=2),
                format_hex(expected_field, width=2)))

    def test_otp_version_field(self):
        expected_field = 0
        actual_field = (self.device_id.to_int() >> 160) & 0xff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=2),
                format_hex(expected_field, width=2)))

    def test_sku_specific_reserved_field0(self):
        expected_field = 0
        actual_field = (self.device_id.to_int() >> 168) & 0xffffff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=4),
                format_hex(expected_field, width=4)))

    def test_sku_id_field(self):
        expected_field = bytes_to_int("LUME".encode("utf-8"))
        actual_field = (self.device_id.to_int() >> 192) & 0xffffffff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=8),
                format_hex(expected_field, width=8)))

    def test_sku_specific_reserved_field1(self):
        expected_field = 0
        actual_field = (self.device_id.to_int() >> 224) & 0xffffff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=4),
                format_hex(expected_field, width=4)))

    def test_sku_specific_version_field(self):
        expected_field = 1
        actual_field = (self.device_id.to_int() >> 248) & 0xff
        self.assertEqual(
            actual_field, expected_field, "actual: {}, expected: {}.".format(
                format_hex(actual_field, width=4),
                format_hex(expected_field, width=4)))

    def test_pretty_print(self):
        self.device_id.pretty_print()

    def test_from_hexstr(self):
        # Simulate getting a different base ID from CP stage.
        din = DeviceIdentificationNumber(year=5,
                                         week=12,
                                         lot=398,
                                         wafer=12,
                                         wafer_x_coord=200,
                                         wafer_y_coord=100)
        expected = DeviceId(sku_config=self.sku_config, din=din)
        hexstr = expected.to_hexstr()
        actual = DeviceId.from_hexstr(hexstr)
        self.assertEqual(expected.to_int(), actual.to_int())


if __name__ == '__main__':
    unittest.main()
