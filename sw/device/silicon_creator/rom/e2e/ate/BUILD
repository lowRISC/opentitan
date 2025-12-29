# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@lowrisc_opentitan//rules:signing.bzl", "offline_presigning_artifacts", "offline_signature_attach")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
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
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:ecdsa_keyset": "prod_key_0"},
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
            "//sw/device/silicon_creator/rom/e2e/ate/binaries:ate_gpio_toggle_test_bins": "firmware",
        },
        otp = "//hw/ip/otp_ctrl/data/earlgrey_skus/sival:otp_img_dev_manuf_personalized",
    ),
)

offline_presigning_artifacts(
    name = "ate_gpio_toggle_test_presigning",
    testonly = True,
    srcs = [":ate_gpio_toggle_test"],
    ecdsa_key = {"//hw/ip/otp_ctrl/data/earlgrey_skus/sival/keys:keyset": "sv00-earlgrey-a1-root-ecdsa-prod-0"},
    manifest = "//sw/device/silicon_creator/rom_ext:manifest",
    spx_key = {},
    tags = ["manual"],
)

pkg_tar(
    name = "digests",
    testonly = True,
    srcs = [":ate_gpio_toggle_test_presigning"],
    mode = "0644",
    tags = ["manual"],
)

offline_signature_attach(
    name = "signed",
    testonly = True,
    srcs = [":ate_gpio_toggle_test_presigning"],
    ecdsa_signatures = ["//sw/device/silicon_creator/rom/e2e/ate/signatures:ecdsa_signatures"],
    spx_signatures = [],
    tags = ["manual"],
)
