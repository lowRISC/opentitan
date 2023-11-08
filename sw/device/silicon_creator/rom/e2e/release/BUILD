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
    "//rules:opentitan.bzl",
    "opentitan_flash_binary",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
    "otp_json",
)
load(
    "//rules:splice.bzl",
    "bitstream_splice",
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

bitstream_splice(
    name = "bitstream_sigverify_spx_rma",
    src = "//hw/bitstream/hyperdebug:rom_with_real_keys",
    data = ":otp_img_sigverify_spx_rma",
    meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

# TODO(#19199): reactivate this test when doing a ROM release.
# opentitan_functest(
#     name = "presigned_fpga_binary",
#     cw310 = cw310_params(
#         bitstream = ":bitstream_sigverify_spx_rma",
#     ),
#     ot_flash_binary = "//sw/device/silicon_creator/rom/e2e/presigned_images:empty_test",
#     # False because we don't want this rule to do the signing; the image is already signed.
#     signed = False,
#     targets = ["cw310_rom_with_real_keys"],
# )

opentitan_flash_binary(
    name = "rom_e2e_self_hash",
    testonly = True,
    srcs = ["rom_e2e_self_hash_test.c"],
    devices = [
        "fpga_cw310",
        "sim_dv",
    ],
    # False because we don't want this rule to do the signing.
    # This image will be signed via the offline process in
    # //signing/rom_tests.
    signed = False,
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

bitstream_splice(
    name = "bitstream_rom_self_hash_test_rma_otbn_mod_exp",
    src = "//hw/bitstream/hyperdebug:rom_with_real_keys",
    data = "//sw/device/silicon_creator/rom/e2e/sigverify_mod_exp:otp_img_sigverify_mod_exp_rma_otbn",
    meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

# TODO(#19199): reactivate this test when doing a ROM release.
# opentitan_functest(
#     name = "rom_e2e_self_hash_test",
#     cw310 = cw310_params(
#         bitstream = ":bitstream_rom_self_hash_test_rma_otbn_mod_exp",
#     ),
#     dv = dv_params(
#         rom = "//sw/device/silicon_creator/rom:rom_with_real_keys",
#     ),
#     ot_flash_binary = "//sw/device/silicon_creator/rom/e2e/presigned_images:rom_e2e_self_hash",
#     # False because we don't want this rule to do the signing; the image is already signed.
#     signed = False,
#     targets = [
#         "cw310_rom_with_real_keys",
#         "dv",
#     ],
# )
