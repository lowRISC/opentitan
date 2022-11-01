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
)
