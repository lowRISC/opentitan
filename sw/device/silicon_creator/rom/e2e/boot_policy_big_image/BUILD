# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:const.bzl",
    "get_lc_items",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)
load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

BOOT_POLICY_BIG_IMAGE_CASES = [
    {
        "suffix": "bigger_than_64k",
        "array_size": 65000,
    },
]

[
    opentitan_test(
        name = "boot_policy_big_image_{}_{}".format(
            lc_state,
            t["suffix"],
        ),
        srcs = ["resizable_test.c"],
        # Use the prod key because it is valid in every LC state.
        ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            otp = "//hw/ip/otp_ctrl/data:img_{}".format(lc_state),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        local_defines = ["ARRAY_SIZE={}".format(t["array_size"])],
        deps = [
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/rom:boot_policy_ptrs",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
    for t in BOOT_POLICY_BIG_IMAGE_CASES
]

test_suite(
    name = "boot_policy_big_image",
    tags = ["manual"],
    tests = [
        "boot_policy_big_image_{}_{}".format(
            lc_state,
            t["suffix"],
        )
        for lc_state, _ in get_lc_items()
        for t in BOOT_POLICY_BIG_IMAGE_CASES
    ],
)
