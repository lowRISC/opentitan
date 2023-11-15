# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

OPENTITANTOOL_OPENOCD_DATA_DEPS = [
    "//third_party/openocd:jtag_olimex_cfg",
    "//third_party/openocd:openocd_bin",
]

OPENTITANTOOL_OPENOCD_SI_TEST_CMD = """
    --openocd="$(rootpath //third_party/openocd:openocd_bin)"
    --openocd-adapter-config="$(rootpath //third_party/openocd:jtag_olimex_cfg)"
"""

OPENTITANTOOL_OPENOCD_TEST_CMD = OPENTITANTOOL_OPENOCD_SI_TEST_CMD + """
    --clear-bitstream
    --bitstream={bitstream}
"""
