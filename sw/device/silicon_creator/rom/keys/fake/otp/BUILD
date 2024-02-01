# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST")
load(
    "//rules:otp.bzl",
    "otp_hex",
    "otp_json_rot_keys",
    "otp_partition",
)

package(default_visibility = ["//visibility:public"])

otp_json_rot_keys(
    name = "json_rot_keys",
    partitions = [
        otp_partition(
            name = "ROT_CREATOR_AUTH_CODESIGN",
            items = {
                # //sw/device/silicon_creator/rom/keys/fake/spx:test_key_0_spx
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE0": otp_hex(CONST.SIGVERIFY.KEY_TYPE.TEST),
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY0": "0x2a4994a9b25e107c5f1df0065a37ff358d45a8a94b4938e4f48a5bbe8dbf6ee6",
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG0": otp_hex(CONST.SPX_CONFIG_ID.SHAKE_128S),

                # //sw/device/silicon_creator/rom/keys/fake/spx:dev_key_0_spx
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE1": otp_hex(CONST.SIGVERIFY.KEY_TYPE.DEV),
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY1": "0xa43c44c9589428e6f3db8f5c6b8d595c805df0cfc97d480eedc286b9a896ae31",
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG1": otp_hex(CONST.SPX_CONFIG_ID.SHAKE_128S),

                # //sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE2": otp_hex(CONST.SIGVERIFY.KEY_TYPE.PROD),
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY2": "0x93672851e736e04ab5d3e60a222a5ba180a58bc322420f0eca1c0f6b3380afb7",
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG2": otp_hex(CONST.SPX_CONFIG_ID.SHAKE_128S),

                # //sw/device/silicon_creator/rom/keys/fake/spx:prod_key_1_spx
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE3": otp_hex(CONST.SIGVERIFY.KEY_TYPE.PROD),
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY3": "0xc5af6e522e268fa51b48d63e0625bcd651fddb66d0dce31b299d22ab451ff43c",
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG3": otp_hex(CONST.SPX_CONFIG_ID.SHAKE_128S),
            },
        ),
        otp_partition(
            name = "ROT_CREATOR_AUTH_STATE",
            items = {
                "ROT_CREATOR_AUTH_STATE_ECDSA_KEY0": otp_hex(CONST.SIGVERIFY.KEY_STATE.BLANK),
                "ROT_CREATOR_AUTH_STATE_ECDSA_KEY1": otp_hex(CONST.SIGVERIFY.KEY_STATE.BLANK),
                "ROT_CREATOR_AUTH_STATE_ECDSA_KEY2": otp_hex(CONST.SIGVERIFY.KEY_STATE.BLANK),
                "ROT_CREATOR_AUTH_STATE_ECDSA_KEY3": otp_hex(CONST.SIGVERIFY.KEY_STATE.BLANK),
                "ROT_CREATOR_AUTH_STATE_SPX_KEY0": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_SPX_KEY1": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_SPX_KEY2": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_SPX_KEY3": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
            },
        ),
    ],
)
