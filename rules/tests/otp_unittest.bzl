# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Unit tests for otp.bzl"""

load(
    "//rules:otp.bzl",
    "otp_alert_classification",
    "otp_bytestring",
    "otp_hex",
    "otp_per_class_bytes",
    "otp_per_class_ints",
    "otp_per_class_lists",
)
load("@bazel_skylib//lib:unittest.bzl", "asserts", "unittest")

def _otp_hex_test(ctx):
    env = unittest.begin(ctx)

    asserts.equals(env, "0x00000000", otp_hex(0x0))
    asserts.equals(env, "0x00000a03", otp_hex(0xa03))
    asserts.equals(env, "0xffffffff", otp_hex(0xffffffff))

    return unittest.end(env)

otp_hex_test = unittest.make(_otp_hex_test)

def _otp_bytestring_test(ctx):
    env = unittest.begin(ctx)

    # 1-byte tests
    asserts.equals(env, "0x00", otp_bytestring([0x00]))
    asserts.equals(env, "0x10", otp_bytestring([0x10]))
    asserts.equals(env, "0xff", otp_bytestring([0xff]))

    # 4-byte tests
    asserts.equals(env, "0x00000000", otp_bytestring([0x00] * 4))
    asserts.equals(env, "0xbbaa0201", otp_bytestring([0x01, 0x02, 0xaa, 0xbb]))
    asserts.equals(env, "0xffffffff", otp_bytestring([0xff] * 4))

    # 8-byte tests
    asserts.equals(env, "0x0000000000000000", otp_bytestring([0x00] * 8))
    asserts.equals(
        env,
        "0xffeebbaa11100201",
        otp_bytestring([0x01, 0x02, 0x10, 0x11, 0xaa, 0xbb, 0xee, 0xff]),
    )
    asserts.equals(env, "0xffffffffffffffff", otp_bytestring([0xff] * 8))

    return unittest.end(env)

otp_bytestring_test = unittest.make(_otp_bytestring_test)

def _otp_alert_classification_test(ctx):
    env = unittest.begin(ctx)

    TEST_ALERT_LIST = [
        "alert0",
        "alert1",
        "alert2",
        "alert3",
        "alert4",
    ]

    # All default test
    asserts.equals(
        env,
        ["0x3294ee94"] * 5,
        otp_alert_classification(
            alert_list = TEST_ALERT_LIST,
            default = "X, A, X, D",
        ),
    )

    # String spacing test
    asserts.equals(
        env,
        ["0x3294ee94"] * 5,
        otp_alert_classification(
            alert_list = TEST_ALERT_LIST,
            default = "  X   , A,X, D   ",
        ),
    )

    # Some alerts specified test
    asserts.equals(
        env,
        ["0x3294ee94", "0x64646464", "0x94a794a7", "0x32a764ee", "0x3294ee94"],
        otp_alert_classification(
            alert_list = TEST_ALERT_LIST,
            default = "X, A, X, D",
            alert3 = " A, B, C, D",
            alert1 = " B, B, B, B",
            alert2 = " C, X, C, X",
        ),
    )

    # All alerts specified (with and without defaults) tests
    asserts.equals(
        env,
        ["0x94949494", "0x64646464", "0x94a794a7", "0x32a764ee", "0xee64a732"],
        otp_alert_classification(
            alert_list = TEST_ALERT_LIST,
            default = "X, A, X, D",
            alert0 = " X, X, X, X",
            alert3 = " A, B, C, D",
            alert1 = " B, B, B, B",
            alert2 = " C, X, C, X",
            alert4 = " D, C, B, A",
        ),
    )

    asserts.equals(
        env,
        ["0x94949494", "0x64646464", "0x94a794a7", "0x32a764ee", "0xee64a732"],
        otp_alert_classification(
            alert_list = TEST_ALERT_LIST,
            alert0 = "X, X, X, X",
            alert3 = "A, B, C, D",
            alert1 = "B, B, B, B",
            alert2 = "C, X, C, X",
            alert4 = "D, C, B, A",
        ),
    )

    return unittest.end(env)

otp_alert_classification_test = unittest.make(_otp_alert_classification_test)

def _otp_per_class_bytes_test(ctx):
    env = unittest.begin(ctx)

    # Kwarg tests
    asserts.equals(env, "0xb4a30201", otp_per_class_bytes(A = 0x01, B = 0x02, C = 0xa3, D = 0xb4))
    asserts.equals(env, "0xffffffff", otp_per_class_bytes(A = 0xff, B = 0xff, C = 0xff, D = 0xff))

    # Positional arg tests
    asserts.equals(env, "0xb4a30201", otp_per_class_bytes(0x01, 0x02, 0xa3, 0xb4))
    asserts.equals(env, "0xffffffff", otp_per_class_bytes(0xff, 0xff, 0xff, 0xff))

    return unittest.end(env)

otp_per_class_bytes_test = unittest.make(_otp_per_class_bytes_test)

def _otp_per_class_ints_test(ctx):
    env = unittest.begin(ctx)

    # Kwarg tests
    asserts.equals(
        env,
        ["0x00000123", "0x00000000", "0x0000ffff", "0xffffffff"],
        otp_per_class_ints(A = 0x123, B = 0x0, C = 0xffff, D = 0xffffffff),
    )

    # Positonal arg tests
    asserts.equals(
        env,
        ["0x00000123", "0x00000000", "0x0000ffff", "0xffffffff"],
        otp_per_class_ints(0x123, 0x0, 0xffff, 0xffffffff),
    )

    return unittest.end(env)

otp_per_class_ints_test = unittest.make(_otp_per_class_ints_test)

def _otp_per_class_lists_test(ctx):
    env = unittest.begin(ctx)

    # Basic integer test
    asserts.equals(
        env,
        [
            "0x00000001",
            "0x00000002",
            "0x00000003",
            "0x00000004",
            "0xffffffff",
            "0xffffffff",
            "0xffffffff",
            "0xffffffff",
            "0x00000001",
            "0x00000002",
            "0x00000003",
            "0x00000004",
            "0x0000000a",
            "0x0000000b",
            "0x0000000c",
            "0x0000000d",
        ],
        otp_per_class_lists(
            A = "0x1, 0x2, 0x3, 0x4",
            B = "0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff",
            C = "1, 2, 3, 4",
            D = "0xa, 0xb, 0xc, 0xd",
        ),
    )

    # Extra spacing test
    asserts.equals(
        env,
        [
            "0x00000001",
            "0x00000002",
            "0x00000003",
            "0x00000004",
            "0xffffffff",
            "0xffffffff",
            "0xffffffff",
            "0xffffffff",
            "0x00000001",
            "0x00000002",
            "0x00000003",
            "0x00000004",
            "0x0000000a",
            "0x0000000b",
            "0x0000000c",
            "0x0000000d",
        ],
        otp_per_class_lists(
            A = " 0x1,0x2,    0x3,              0x4",
            B = "0xffffffff,   0xffffffff,     0xffffffff,0xffffffff       ",
            C = "1,2,3,4",
            D = "   0xa,   0xb,   0xc,   0xd   ",
        ),
    )

    return unittest.end(env)

otp_per_class_lists_test = unittest.make(_otp_per_class_lists_test)

def otp_test_suite():
    """Create test targets and test suite for const.bzl."""
    unittest.suite(
        "otp_tests",
        otp_hex_test,
        otp_bytestring_test,
        otp_alert_classification_test,
        otp_per_class_bytes_test,
        otp_per_class_ints_test,
        otp_per_class_lists_test,
    )
