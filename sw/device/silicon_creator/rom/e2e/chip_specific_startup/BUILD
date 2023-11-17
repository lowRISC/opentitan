# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "hyper310_params",
    "opentitan_test",
    "rsa_key_for_lc_state",
)
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
)
load(
    "//rules:const.bzl",
    "get_lc_items",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)

package(default_visibility = ["//visibility:public"])

[
    opentitan_test(
        name = "e2e_chip_specific_startup_{}".format(lc_state),
        srcs = ["chip_specific_startup.c"],
        cw310 = cw310_params(
            otp = "//sw/device/silicon_creator/rom/e2e/rom_e2e_bootstrap_entry:otp_img_e2e_bootstrap_entry_{}".format(lc_state),
            tags = maybe_skip_in_ci(lc_state_val),
            test_cmd = """
                --bitstream="{bitstream}"
                --bootstrap="{firmware}"
                --otp-unprogrammed
            """,
            test_harness = "//sw/host/tests/rom/e2e_chip_specific_startup",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys": None,
        },
        hyper310 = hyper310_params(
            otp = "//sw/device/silicon_creator/rom/e2e/rom_e2e_bootstrap_entry:otp_img_e2e_bootstrap_entry_{}".format(lc_state),
            tags = maybe_skip_in_ci(lc_state_val),
            test_cmd = """
                --bitstream="{bitstream}"
                --bootstrap="{firmware}"
                --otp-unprogrammed
            """,
            test_harness = "//sw/host/tests/rom/e2e_chip_specific_startup",
        ),
        manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
        rsa_key = rsa_key_for_lc_state(
            RSA_ONLY_KEY_STRUCTS,
            lc_state_val,
        ),
        deps = [
            "//hw/ip/csrng/data:csrng_regs",
            "//hw/ip/edn/data:edn_regs",
            "//hw/ip/entropy_src/data:entropy_src_regs",
            "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
            "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:mmio",
            "//sw/device/lib/dif:clkmgr",
            "//sw/device/lib/dif:lc_ctrl",
            "//sw/device/lib/dif:otp_ctrl",
            "//sw/device/lib/dif:sram_ctrl",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/json:chip_specific_startup",
            "//sw/device/lib/testing/json:command",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/lib/testing/test_framework:ujson_ottf",
            "//sw/device/lib/ujson",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
]

test_suite(
    name = "e2e_chip_specific_startup",
    tags = ["manual"],
    tests = [
        "e2e_chip_specific_startup_{}".format(lc_state)
        for lc_state, _ in get_lc_items()
    ],
)
