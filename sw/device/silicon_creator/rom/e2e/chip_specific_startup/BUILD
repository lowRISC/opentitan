# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
)
load(
    "//rules:const.bzl",
    "get_lc_items",
)
load(
    "//rules:opentitan.bzl",
    "get_key_structs_for_lc_state",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)
load(
    "//rules:splice.bzl",
    "bitstream_splice",
)

package(default_visibility = ["//visibility:public"])

[
    bitstream_splice(
        name = "bitstream_chip_specific_startup_{}".format(lc_state),
        src = "//hw/bitstream:rom_with_fake_keys",
        data = "//sw/device/silicon_creator/rom/e2e/rom_e2e_bootstrap_entry:otp_img_e2e_bootstrap_entry_{}".format(lc_state),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = maybe_skip_in_ci(lc_state_val),
        update_usr_access = True,
    )
    for lc_state, lc_state_val in get_lc_items()
]

[
    opentitan_functest(
        name = "e2e_chip_specific_startup_{}".format(lc_state),
        srcs = ["chip_specific_startup.c"],
        args = [],
        cw310 = cw310_params(
            bitstream = ":bitstream_chip_specific_startup_{}".format(lc_state),
            tags = maybe_skip_in_ci(lc_state_val),
            test_cmds = [
                "--bitstream=\"$(location {bitstream})\"",
                "--bootstrap=\"$(location {flash})\"",
                "--otp-unprogrammed",
            ],
        ),
        key_struct = get_key_structs_for_lc_state(
            lc_state_val,
            spx = None,
        )[0],
        signed = True,
        targets = ["cw310_rom_with_fake_keys"],
        test_harness = "//sw/host/tests/rom/e2e_chip_specific_startup",
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
