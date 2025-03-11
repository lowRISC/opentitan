# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

opentitan_binary(
    name = "ate_gpio_toggle_test",
    testonly = True,
    srcs = ["ate_gpio_toggle_test.c"],
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
        "//hw/top_earlgrey:silicon_creator": None,
        "//hw/top_earlgrey:sim_dv": None,
    },
    spx_key = {},
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:manifest_def",
    ],
)

opentitan_test(
    name = "ate_smoketest",
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_sival": None,
    },
    fpga = fpga_params(
        binaries = {
            ":ate_gpio_toggle_test": "firmware",
        },
    ),
)
