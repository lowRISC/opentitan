# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "dv_params",
    "opentitan_functest",
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
    "otp_json",
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
    "MSG_TEMPLATE_BFV",
    "MSG_TEMPLATE_BFV_LCV",
)

package(default_visibility = ["//visibility:public"])

[otp_image(
    name = "otp_img_shutdown_output_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS,
) for lc_state, _ in get_lc_items()]

# Splice OTP images into bitstreams
[
    bitstream_splice(
        name = "bitstream_shutdown_output_{}".format(lc_state),
        src = "//hw/bitstream:rom_with_fake_keys",
        data = ":otp_img_shutdown_output_{}".format(lc_state),
        meminfo = "//hw/bitstream:otp_mmi",
        update_usr_access = True,
    )
    for lc_state, _ in get_lc_items()
]

manifest({
    "name": "manifest_bad_identifier",
    "address_translation": hex(CONST.HARDENED_FALSE),
    "identifier": "0",
})

[opentitan_functest(
    name = "shutdown_output_{}".format(lc_state),
    cw310 = cw310_params(
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
        otp = ":otp_img_shutdown_output_{}".format(lc_state),
        rom = "//sw/device/silicon_creator/rom:rom_with_fake_keys",
    ),
    manifest = ":manifest_bad_identifier",
    ot_flash_binary = "//sw/device/silicon_creator/rom/e2e:empty_test_slot_a",
    signed = False,
    targets = [
        "cw310_rom_with_fake_keys",
        "dv",
    ],
) for lc_state, lc_state_val in get_lc_items()]

test_suite(
    name = "shutdown_output",
    tags = ["manual"],
    tests = ["shutdown_output_{}".format(lc_state) for lc_state, _ in get_lc_items()],
)
