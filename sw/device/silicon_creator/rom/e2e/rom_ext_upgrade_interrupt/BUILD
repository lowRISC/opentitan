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
    "CONST",
    "get_lc_items",
    "hex",
)
load(
    "//rules:opentitan.bzl",
    "get_key_structs_for_lc_state",
)
load(
    "//rules:manifest.bzl",
    "manifest",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_hex",
    "otp_image",
    "otp_json",
    "otp_partition",
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

manifest({
    "name": "manifest_rom_ext_upgrade_interrupt",
    "address_translation": hex(CONST.HARDENED_FALSE),
    "identifier": hex(CONST.ROM_EXT),
    "security_version": hex(10),
})

otp_json(
    name = "otp_json_rom_ext_upgrade_interrupt",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_DEFAULT_BOOT_DATA_IN_PROD_EN": otp_hex(CONST.HARDENED_TRUE),
            },
        ),
    ],
)

[
    otp_image(
        name = "otp_img_rom_ext_upgrade_interrupt_{}".format(lc_state),
        src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
        overlays = STD_OTP_OVERLAYS + [":otp_json_rom_ext_upgrade_interrupt"],
        visibility = ["//visibility:private"],
    )
    for lc_state, _ in get_lc_items()
]

[
    bitstream_splice(
        name = "bitstream_rom_ext_upgrade_interrupt_{}".format(
            lc_state,
        ),
        src = "//hw/bitstream:rom_with_fake_keys",
        data = ":otp_img_rom_ext_upgrade_interrupt_{}".format(
            lc_state,
        ),
        meminfo = "//hw/bitstream:otp_mmi",
        tags = maybe_skip_in_ci(lc_state_val),
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for lc_state, lc_state_val in get_lc_items()
]

[
    opentitan_functest(
        name = "rom_ext_upgrade_interrupt_{}".format(lc_state),
        srcs = ["rom_ext_upgrade_interrupt.c"],
        cw310 = cw310_params(
            bitstream = ":bitstream_rom_ext_upgrade_interrupt_{}".format(lc_state),
            clear_bitstream = True,
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        key_struct = get_key_structs_for_lc_state(
            lc_state_val,
            spx = None,
        )[0],
        manifest = ":manifest_rom_ext_upgrade_interrupt",
        targets = [
            "cw310_rom_with_fake_keys",
        ],
        deps = [
            "//sw/device/lib/testing:flash_ctrl_testutils",
            "//sw/device/lib/testing:nv_counter_testutils",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:boot_data",
            "//sw/device/silicon_creator/lib/drivers:lifecycle",
            "//sw/device/silicon_creator/lib/drivers:rstmgr",
        ],
    )
    for lc_state, lc_state_val in get_lc_items()
]

test_suite(
    name = "rom_e2e_rom_ext_upgrade_interrupt",
    tags = ["manual"],
    tests = ["rom_ext_upgrade_interrupt_{}".format(lc_state) for lc_state, _ in get_lc_items()],
)
