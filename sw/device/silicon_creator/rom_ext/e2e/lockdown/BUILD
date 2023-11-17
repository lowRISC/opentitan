# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

opentitan_test(
    name = "otp_creator_lockdown",
    srcs = ["otp_creator_lockdown.c"],
    cw310 = cw310_params(
        exit_failure = "PASS|FAIL|BFV:.*\r\n",
        # Make sure we get to the correct point in the test program before the fault.
        exit_success = "OTP CreatorSwCfg:\r\n.*FAULT: Load Access Fault.*\r\n",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "otp_dai_lockdown",
    srcs = ["otp_dai_lockdown.c"],
    cw310 = cw310_params(
        exit_failure = "PASS|FAIL|BFV:.*\r\n",
        # Make sure we get to the correct point in the test program before the fault.
        exit_success = "dif_otp_ctrl_configure:\r\n.*FAULT: Load Access Fault.*\r\n",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:otp_ctrl",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "sram_lockdown",
    srcs = ["sram_lockdown.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    deps = [
        "//hw/ip/sram_ctrl/data:sram_ctrl_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "epmp_rlb_lockdown",
    srcs = ["epmp_rlb_lockdown.c"],
    cw310 = cw310_params(
        exit_failure = "(PASS|FAIL|BFV|FAULT).*\r\n",
        # Make sure the test program failed to modify the ePMP.
        exit_success = "6: 40130000 NAPOT L--- sz=00001000\r\n",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:dbg_print",
    ],
)
