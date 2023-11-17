# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "hyper310_params",
    "opentitan_test",
    "rsa_key_for_lc_state",
    "verilator_params",
)
load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
)
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)

package(default_visibility = ["//visibility:public"])

[
    opentitan_test(
        name = "epmp_init_otp_" + lc_state,
        srcs = ["epmp_init_test.c"],
        cw310 = cw310_params(
            otp = "//hw/ip/otp_ctrl/data:img_" + lc_state,
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:sim_verilator": None,
        },
        hyper310 = hyper310_params(
            bitstream = "//hw/bitstream/hyperdebug:rom_with_fake_keys_otp_" + lc_state,
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        local_defines = [
            "EXPECT_DEBUG={}".format(1 if lc_state_val in [
                CONST.LCV.TEST_UNLOCKED0,
                CONST.LCV.DEV,
                CONST.LCV.RMA,
            ] else 0),
        ],
        manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
        rsa_key = rsa_key_for_lc_state(
            RSA_ONLY_KEY_STRUCTS,
            lc_state_val,
        ),
        verilator = verilator_params(
            timeout = "eternal",
            otp = "//hw/ip/otp_ctrl/data:img_" + lc_state,
            rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
        ),
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:csr",
            "//sw/device/lib/dif:lc_ctrl",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing:lc_ctrl_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/lib/testing/test_framework:status",
            "//sw/device/silicon_creator/lib:epmp_defs",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
]

test_suite(
    name = "rom_e2e_epmp_init",
    tags = ["manual"],
    tests = ["epmp_init_otp_" + lc_state for lc_state, _ in get_lc_items()],
)
