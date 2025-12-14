# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("@//rules:signing.bzl", "offline_presigning_artifacts", "offline_signature_attach")
load("//rules:const.bzl", "CONST", "hex")
load("//rules:manifest.bzl", "manifest")
load(
    "//rules/opentitan:defs.bzl",
    "opentitan_binary",
    "opentitan_test",
    "silicon_params",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_hex",
    "otp_image",
    "otp_json",
    "otp_partition",
)

# Building a wrongly signed BL0 binary for testing the secure boot
opentitan_binary(
    name = "bl0_firmware",
    testonly = True,
    # This can be any other source of the pentest framework
    srcs = ["//sw/device/tests/penetrationtests/firmware:firmware_cryptolib_fi_sym.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    deps = [
        "//sw/device/tests/penetrationtests/firmware/sca:trigger_sca",
        "//sw/device/tests/penetrationtests/firmware/fi:cryptolib_fi_sym",
        "//sw/device/tests/penetrationtests/firmware/lib:extclk_sca_fi",
        "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",

        # Include all JSON commands.
        "//sw/device/tests/penetrationtests/json:commands",
    ],
)

offline_presigning_artifacts(
    name = "non_signed_firmware",
    testonly = True,
    srcs = [":bl0_firmware"],
    ecdsa_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "prod_key_0"},
    manifest = "//sw/device/silicon_owner:manifest",
    spx_key = {},
    tags = ["manual"],
)

offline_signature_attach(
    name = "wrong_signed_firmware",
    testonly = True,
    srcs = [":non_signed_firmware"],
    # We provide a wrong signature
    ecdsa_signatures = ["bl0_firmware_fpga_cw340_rom_ext.ecdsa_sig"],
    spx_signatures = [],
    tags = ["manual"],
)

# For when building specialized manifests for security testing.
manifest(d = {
    "name": "rom_ext_rollback_manifest",
    "identifier": hex(CONST.OWNER),
    "security_version": "0",
    "visibility": ["//visibility:public"],
})

otp_json(
    name = "otp_json_rom_ext_fi",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_RMA_SPIN_EN": otp_hex(CONST.HARDENED_TRUE),
                # Number of Ibex cycles to spin: we set this to the highest value
                "CREATOR_SW_CFG_RMA_SPIN_CYCLES": "0xffffffff",
                # Enable SPX+ signature verification.
                # TODO: ROM_EXT is not signed with this yet
                # "CREATOR_SW_CFG_SIGVERIFY_SPX_EN": otp_hex(0x0),
                # Turn off the ROM_EXT_IMM
                "CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN": otp_hex(0x0),
                # We disable randomness since that messes with GDB
                "CREATOR_SW_CFG_RNG_EN": otp_hex(0x0),
            },
        ),
        otp_partition(
            name = "SECRET2",
            items = {
                # We set reproducible bitstreams for the tests
                "RMA_TOKEN": "0000000000000005",
                "CREATOR_ROOT_KEY_SHARE0": "1111111111111111111111111111111111111111111111111111111111111111",
                "CREATOR_ROOT_KEY_SHARE1": "2222222222222222222222222222222222222222222222222222222222222222",
            },
            lock = True,
        ),
    ],
    visibility = ["//visibility:private"],
)

otp_image(
    name = "otp_img_rom_ext_fi",
    src = "//hw/top_earlgrey/data/otp:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [
        ":otp_json_rom_ext_fi",
    ],
)

otp_json(
    name = "otp_json_rom_ext_rollback_fi",
    partitions = [
        otp_partition(
            name = "CREATOR_SW_CFG",
            items = {
                "CREATOR_SW_CFG_RMA_SPIN_EN": otp_hex(CONST.HARDENED_TRUE),
                # Number of Ibex cycles to spin: we set this to the highest value
                "CREATOR_SW_CFG_RMA_SPIN_CYCLES": "0xffffffff",
                # We set the version to a higher number to check rollback protection
                "CREATOR_SW_CFG_MIN_SEC_VER_BL0": "0x2",
                # Enable SPX+ signature verification.
                # TODO: ROM_EXT is not signed with this yet
                # "CREATOR_SW_CFG_SIGVERIFY_SPX_EN": otp_hex(0x0),
            },
        ),
        otp_partition(
            name = "SECRET2",
            items = {
                # We set reproducible bitstreams for the tests
                "RMA_TOKEN": "0000000000000005",
                "CREATOR_ROOT_KEY_SHARE0": "1111111111111111111111111111111111111111111111111111111111111111",
                "CREATOR_ROOT_KEY_SHARE1": "2222222222222222222222222222222222222222222222222222222222222222",
            },
            lock = True,
        ),
    ],
    visibility = ["//visibility:private"],
)

otp_image(
    name = "otp_img_rom_ext_rollback_fi",
    src = "//hw/top_earlgrey/data/otp:otp_json_rma",
    overlays = STD_OTP_OVERLAYS + [
        ":otp_json_rom_ext_rollback_fi",
    ],
)
