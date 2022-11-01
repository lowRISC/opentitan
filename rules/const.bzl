# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

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
)

_HEX_MAP = "0123456789abcdef"

def hex(v):
    # First "cast" `v` to a 32-bit unsigned int
    v &= 0xffffffff
    hex_digits = [_HEX_MAP[(v >> i) & 0xf] for i in range(0, 32, 4)]
    return "".join(reversed(hex_digits))
