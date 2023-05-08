# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Unit tests for const.bzl"""

load("//rules:const.bzl", "CONST", "get_lc_items", "hex", "hex_digits", "lcv_hw_to_sw")
load("@bazel_skylib//lib:unittest.bzl", "asserts", "unittest")
load("@bazel_skylib//lib:sets.bzl", "sets")

def _get_lc_items_test(ctx):
    env = unittest.begin(ctx)

    # Get one entry
    asserts.new_set_equals(
        env,
        sets.make([
            ("test_unlocked0", CONST.LCV.TEST_UNLOCKED0),
        ]),
        sets.make(get_lc_items(CONST.LCV.TEST_UNLOCKED0)),
    )

    # Get multiple entries
    asserts.new_set_equals(
        env,
        sets.make([
            ("dev", CONST.LCV.DEV),
            ("prod_end", CONST.LCV.PROD_END),
            ("test_unlocked5", CONST.LCV.TEST_UNLOCKED5),
        ]),
        sets.make(
            get_lc_items(
                CONST.LCV.DEV,
                CONST.LCV.PROD_END,
                CONST.LCV.TEST_UNLOCKED5,
            ),
        ),
    )

    # Get default entries
    asserts.new_set_equals(
        env,
        sets.make([
            ("test_unlocked0", CONST.LCV.TEST_UNLOCKED0),
            ("dev", CONST.LCV.DEV),
            ("prod", CONST.LCV.PROD),
            ("prod_end", CONST.LCV.PROD_END),
            ("rma", CONST.LCV.RMA),
        ]),
        sets.make(get_lc_items()),
    )

    return unittest.end(env)

get_lc_items_test = unittest.make(_get_lc_items_test)

def _lcv_hw_to_sw_test(ctx):
    env = unittest.begin(ctx)

    asserts.equals(env, CONST.LCV_SW.DEV, lcv_hw_to_sw(CONST.LCV.DEV))
    asserts.equals(env, CONST.LCV_SW.PROD, lcv_hw_to_sw(CONST.LCV.PROD))
    asserts.equals(env, CONST.LCV_SW.PROD_END, lcv_hw_to_sw(CONST.LCV.PROD_END))
    asserts.equals(env, CONST.LCV_SW.RMA, lcv_hw_to_sw(CONST.LCV.RMA))
    asserts.equals(env, CONST.LCV_SW.TEST, lcv_hw_to_sw(CONST.LCV.TEST_UNLOCKED0))

    return unittest.end(env)

lcv_hw_to_sw_test = unittest.make(_lcv_hw_to_sw_test)

def _hex_digits_test(ctx):
    env = unittest.begin(ctx)

    asserts.equals(env, "00000123", hex_digits(0x123))
    asserts.equals(env, "00000000", hex_digits(0x0))
    asserts.equals(env, "ffffffff", hex_digits(0xffffffff))

    return unittest.end(env)

hex_digits_test = unittest.make(_hex_digits_test)

def _hex_test(ctx):
    env = unittest.begin(ctx)

    asserts.equals(env, "0x00000123", hex(0x123))
    asserts.equals(env, "0x00000000", hex(0x0))
    asserts.equals(env, "0xffffffff", hex(0xffffffff))

    return unittest.end(env)

hex_test = unittest.make(_hex_test)

def const_test_suite():
    """Create test targets and test suite for const.bzl."""
    unittest.suite(
        "const_tests",
        get_lc_items_test,
        lcv_hw_to_sw_test,
        hex_digits_test,
        hex_test,
    )
