# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
)
load(
    "//rules/opentitan:defs.bzl",
    "dv_params",
    "fpga_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

otp_image(
    name = "otp_img_sigverify_spx_rma",
    src = "//hw/ip/otp_ctrl/data:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [
        "//sw/device/silicon_creator/rom/e2e/sigverify_spx:otp_json_sigverify_spx_enabled_true",
    ],
    visibility = ["//visibility:private"],
)

opentitan_test(
    name = "rom_e2e_self_hash_test",
    srcs = ["rom_e2e_self_hash_test.c"],
    dv = dv_params(
        otp = ":otp_img_sigverify_spx_rma",
        rom = "//sw/device/silicon_creator/rom:mask_rom",
    ),
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
        "//hw/top_earlgrey:sim_dv": None,
    },
    fpga = fpga_params(
        otp = ":otp_img_sigverify_spx_rma",
    ),
    spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx": "prod_key_0"},
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:chip_info",
        "//sw/device/silicon_creator/lib/drivers:hmac",
    ],
)
