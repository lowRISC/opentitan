# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//lib:structs.bzl", "structs")

CONST = struct(
    # Must match the definitions in hardened.h.
    TRUE = 0x739,
    FALSE = 0x1d4,
    # Must match the definitions in chip.h.
    ROM_EXT = 0x4552544f,
    OWNER = 0x3042544f,
    MANIFEST_SIZE = 896,
    ROM_EXT_SIZE_MIN = 896,
    ROM_EXT_SIZE_MAX = 0x10000,
    BL0_SIZE_MIN = 896,
    BL0_SIZE_MAX = 0x70000,
    DEFAULT_USAGE_CONSTRAINTS = 0xa5a5a5a5,
    # Must match the definitions in lc_ctrl_regs.h.
    LCV = struct(
        TEST_UNLOCKED0 = 0x02108421,
        DEV = 0x21084210,
        PROD = 0x2318c631,
        PROD_END = 0x25294a52,
        RMA = 0x2739ce73,
    ),
    # Must match the definitions in error.h.
    BFV = struct(
        INTERRUPT = struct(
            INSTRUCTION_ACCESS = 0x01495202,
            ILLEGAL_INSTRUCTION = 0x02495202,
            STORE_ACCESS = 0x07495202,
        ),
        SIGVERIFY = struct(
            BAD_ENCODED_MSG = 0x01535603,
            BAD_KEY = 0x02535603,
        ),
        BOOT_POLICY = struct(
            BAD_IDENTIFIER = 0x0142500d,
            BAD_LENGTH = 0x0242500d,
            ROLLBACK = 0x0342500d,
        ),
        MANIFEST = struct(
            BAD_ENTRY_POINT = 0x014d410d,
            BAD_CODE_REGION = 0x024d410d,
        ),
        UNKNOWN = 0xffffffff,
        OK = 0x739,
    ),
    # Must match the definitions in shutdown.h.
    SHUTDOWN = struct(
        PREFIX = struct(
            LCV = "LCV:",
            BFV = "BFV:",
        ),
        REDACT = struct(
            NONE = 0xe2290aa5,
            ERROR = 0x3367d3d4,
            MODULE = 0x1e791123,
            ALL = 0x48eb4bd9,
        ),
    ),
)

_HEX_MAP = "0123456789abcdef"

def hex(v):
    # First "cast" `v` to a 32-bit unsigned int
    v &= 0xffffffff
    hex_digits = [_HEX_MAP[(v >> i) & 0xf] for i in range(0, 32, 4)]
    return "".join(reversed(hex_digits))

_REDACTION_MAP = {
    CONST.SHUTDOWN.REDACT.NONE: 0xffffffff,
    CONST.SHUTDOWN.REDACT.ERROR: 0x00ffffff,
    CONST.SHUTDOWN.REDACT.MODULE: 0x000000ff,
}

_REDACTION_LC_STATES = [CONST.LCV.DEV, CONST.LCV.PROD, CONST.LCV.PROD_END]

def error_redact(error, lc_state, redact):
    if lc_state not in _REDACTION_LC_STATES:
        return error
    if redact == CONST.SHUTDOWN.REDACT.ALL or redact not in _REDACTION_MAP:
        return CONST.BFV.UNKNOWN
    return error & _REDACTION_MAP.get(redact)
