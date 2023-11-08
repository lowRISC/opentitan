# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "dv_params",
    "opentitan_test",
    "rsa_key_for_lc_state",
)
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
)
load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
    "hex",
    "hex_digits",
)
load(
    "//rules:manifest.bzl",
    "manifest",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)
load(
    "//rules:splice.bzl",
    "bitstream_splice",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "MSG_PASS",
    "MSG_TEMPLATE_BFV_LCV",
)

package(default_visibility = ["//visibility:public"])

[
    otp_image(
        name = "otp_img_shutdown_output_{}".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS,
    )
    for lc_state, _ in get_lc_items()
]

[
    bitstream_splice(
        name = "bitstream_shutdown_output_{}".format(lc_state),
        src = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
        data = ":otp_img_shutdown_output_{}".format(lc_state),
        meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
        update_usr_access = True,
    )
    for lc_state, _ in get_lc_items()
]

manifest(
    d = {
        "name": "manifest_bad_identifier",
        "address_translation": hex(CONST.HARDENED_FALSE),
        "identifier": "0",
    },
)

[
    opentitan_test(
        name = "shutdown_output_{}".format(lc_state),
        cw310 = cw310_params(
            binaries = {"//sw/device/silicon_creator/rom/e2e:new_empty_test_slot_a": "firmware"},
            bitstream = ":bitstream_shutdown_output_{}".format(lc_state),
            exit_failure = MSG_PASS,
            exit_success = MSG_TEMPLATE_BFV_LCV.format(
                hex_digits(CONST.BFV.BOOT_POLICY.BAD_IDENTIFIER),
                hex_digits(lc_state_val),
            ),
            otp = ":otp_img_shutdown_output_{}".format(lc_state),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        dv = dv_params(
            binaries = {"//sw/device/silicon_creator/rom/e2e:new_empty_test_slot_a": "firmware"},
            otp = ":otp_img_shutdown_output_{}".format(lc_state),
            rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
        ),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:sim_dv": None,
        },
        manifest = ":manifest_bad_identifier",
        rsa_key = rsa_key_for_lc_state(
            RSA_ONLY_KEY_STRUCTS,
            lc_state_val,
        ),
    )
    for lc_state, lc_state_val in get_lc_items()
]

test_suite(
    name = "shutdown_output",
    tags = ["manual"],
    tests = ["shutdown_output_{}".format(lc_state) for lc_state, _ in get_lc_items()],
)
