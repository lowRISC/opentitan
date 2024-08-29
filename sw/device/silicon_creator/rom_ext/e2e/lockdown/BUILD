# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

opentitan_test(
    name = "otp_creator_lockdown",
    srcs = ["otp_creator_lockdown.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    fpga = fpga_params(
        exit_failure = "PASS|FAIL|BFV:.*\r\n",
        # Make sure we get to the correct point in the test program before the fault.
        # The MTVAL is the location of the access fault.  The address below
        # corresponds to the OTP controller at
        # OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET + OTP_CTRL_PARAM_CREATOR_SW_CFG_OFFSET.
        exit_success = "FAULT: Load Access Fault.*MTVAL=40131040\r\n",
    ),
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
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    fpga = fpga_params(
        exit_failure = "PASS|FAIL|BFV:.*\r\n",
        # Make sure we get to the correct point in the test program before the fault.
        # The OTP DIF first checks to see if the OTP controller is locked.
        # Since we've disabled access to the OTP controller completely, reading
        # the REGWEN register will fail and cause a fault.
        # The address below # corresponds to the OTP controller at
        # OTP_CTRL_CHECK_REGWEN_REG_OFFSET.
        exit_success = "FAULT: Load Access Fault.*MTVAL=4013003c\r\n",
    ),
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
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
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
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:dbg_print",
    ],
)
