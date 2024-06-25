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
                # //sw/device/silicon_creator/rom/keys/real/spx:test_key_0_spx
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE0": otp_hex(CONST.SIGVERIFY.KEY_TYPE.TEST),
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY0": "0x2BB062EECDAFCD22015BA9BB38E0A97FFD0F8D4CD416672ABE0FA6069D629D35",
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG0": otp_hex(CONST.SPX_CONFIG_ID.SHA2_128S),

                # //sw/device/silicon_creator/rom/keys/real/spx:dev_key_0_spx
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE1": otp_hex(CONST.SIGVERIFY.KEY_TYPE.DEV),
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY1": "0x93B089AE7FCB2D37C3FB0E6C2810489E4137BCAF50FFE2F4E05226E6CE99F1C8",
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG1": otp_hex(CONST.SPX_CONFIG_ID.SHA2_128S),

                # //sw/device/silicon_creator/rom/keys/real/spx:prod_key_0_spx
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE2": otp_hex(CONST.SIGVERIFY.KEY_TYPE.PROD),
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY2": "0xAA68F9D4D64FF84C32185CB4F80EBA3924E9351B3C0A258DCE66247AC310E733",
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG2": otp_hex(CONST.SPX_CONFIG_ID.SHA2_128S),

                # //sw/device/silicon_creator/rom/keys/real/spx:prod_key_1_spx
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE3": otp_hex(CONST.SIGVERIFY.KEY_TYPE.PROD),
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY3": "0xAFE44BE7289CAD6034D51734A445AFB187FC782599E2479C1F62FEB880F14530",
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG3": otp_hex(CONST.SPX_CONFIG_ID.SHA2_128S),
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
