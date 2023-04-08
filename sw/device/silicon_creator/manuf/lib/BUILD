# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules:opentitan_test.bzl", "cw310_params", "opentitan_functest")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "provisioning",
    srcs = ["provisioning.c"],
    hdrs = [
        "provisioning.h",
    ],
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing:lc_ctrl_testutils",
        "//sw/device/lib/testing:otp_ctrl_testutils",
    ],
)

opentitan_functest(
    name = "provisioning_functest",
    srcs = ["provisioning_functest.c"],
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_otp_dev",
    ),
    targets = [
        "cw310_rom",
    ],
    deps = [
        ":provisioning",
        "//hw/ip/flash_ctrl/data:flash_ctrl_regs",
        "//hw/ip/lc_ctrl/data:lc_ctrl_regs",
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/dif:lc_ctrl",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
