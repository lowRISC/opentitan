# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "OPENTITANTOOL_OPENOCD_DATA_DEPS",
    "OPENTITANTOOL_OPENOCD_TEST_CMDS",
    "cw310_params",
    "opentitan_functest",
)
load(
    "//rules:const.bzl",
    "CONST",
    "hex",
)
load(
    "//rules:opentitan.bzl",
    "get_key_structs_for_lc_state",
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
    "//rules:splice.bzl",
    "bitstream_splice",
)

package(default_visibility = ["//visibility:public"])

otp_json(
    name = "otp_json_bootstrap_rma",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_RMA_SPIN_EN": otp_hex(CONST.HARDENED_TRUE),
                "CREATOR_SW_CFG_RMA_SPIN_CYCLES": "0x2000000",
            },
        ),
        otp_partition(
            name = "SECRET2",
            items = {
                # This RMA token is a cSHAKE128 digest. The preimage is
                # hardcoded into the test harness [0] and the tool that
                # generated this token [1].
                #
                # [0]: //sw/host/tests/rom/e2e_bootstrap_rma
                # [1]: //sw/host/tests/rom/e2e_bootstrap_rma:gen_rma_token
                "RMA_TOKEN": "0x1faf9056acde66561685549803a28bec",
                "CREATOR_ROOT_KEY_SHARE0": "<random>",
                "CREATOR_ROOT_KEY_SHARE1": "<random>",
            },
            lock = True,
        ),
    ],
    visibility = ["//visibility:private"],
)

# This OTP image is tightly coupled with the "rom_bootstrap_rma" testpoint.
# Despite its name ending with "rma", it actually puts the device into the PROD
# lifecycle state in order to test the transition from PROD to RMA.
otp_image(
    name = "otp_img_bootstrap_rma",
    src = "//hw/ip/otp_ctrl/data:otp_json_prod",
    overlays = STD_OTP_OVERLAYS + [
        ":otp_json_bootstrap_rma",
    ],
    visibility = ["//visibility:private"],
)

bitstream_splice(
    name = "bitstream_bootstrap_rma",
    src = "//hw/bitstream:rom_with_fake_keys",
    data = ":otp_img_bootstrap_rma",
    meminfo = "//hw/bitstream:otp_mmi",
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

opentitan_functest(
    name = "e2e_bootstrap_rma",
    srcs = ["rom_e2e_bootstrap_rma_test.c"],
    cw310 = cw310_params(
        bitstream = ":bitstream_bootstrap_rma",
        test_cmds = [
            # We need to clear the bitstream between consecutive runs of this
            # test since it modifies OTP state (i.e., the LC state).
            "--clear-bitstream",
            "--bitstream=\"$(rootpath {bitstream})\"",
            "--bootstrap=\"$(rootpath {flash})\"",
        ] + OPENTITANTOOL_OPENOCD_TEST_CMDS,
    ),
    data = OPENTITANTOOL_OPENOCD_DATA_DEPS,
    key_struct = get_key_structs_for_lc_state(
        CONST.LCV.PROD,
        spx = None,
    )[0],
    targets = ["cw310_rom_with_fake_keys"],
    test_harness = "//sw/host/tests/rom/e2e_bootstrap_rma",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_functest(
    name = "e2e_bootstrap_disabled",
    cw310 = cw310_params(
        bitstream = "//hw/bitstream:rom_with_fake_keys_otp_bootstrap_disabled",
        test_cmds = [
            "--bitstream=\"$(location {bitstream})\"",
        ],
    ),
    # Since the bitstream disables bootstrap, there is no firmware to
    # load into the chip.  However, opentitan_functest wants to build a
    # binary target.  We'll build an unsigned do-nothing binary.
    ot_flash_binary = "//sw/device/silicon_creator/rom/e2e:empty_test_slot_a",
    signed = False,
    targets = ["cw310_rom_with_fake_keys"],
    test_harness = "//sw/host/tests/rom/e2e_bootstrap_disabled",
)
