# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:keyutils.bzl", "key_ecdsa")
load("//rules:signing.bzl", "keyset")
load("//rules:const.bzl", "CONST")
load(
    "//rules:otp.bzl",
    "otp_hex",
    "otp_json_rot_keys",
    "otp_partition",
)

package(default_visibility = ["//visibility:public"])

key_ecdsa(
    name = "ecdsa_prod_0",
    config = "EcdsaP256",
    method = "hsmtool",
    pub_key = "sv00-earlgrey-a1-root-ecdsa-prod-0.pub.der",
    type = "ProdKey",
)

key_ecdsa(
    name = "ecdsa_prod_1",
    config = "EcdsaP256",
    method = "hsmtool",
    pub_key = "sv00-earlgrey-a1-root-ecdsa-prod-1.pub.der",
    type = "ProdKey",
)

key_ecdsa(
    name = "ecdsa_prod_2",
    config = "EcdsaP256",
    method = "hsmtool",
    pub_key = "sv00-earlgrey-a1-root-ecdsa-prod-2.pub.der",
    type = "ProdKey",
)

key_ecdsa(
    name = "ecdsa_test_0",
    config = "EcdsaP256",
    method = "hsmtool",
    pub_key = "sv00-earlgrey-a1-root-ecdsa-test-0.pub.der",
    type = "TestKey",
)

key_ecdsa(
    name = "ca_dice_0",
    config = "EcdsaP256",
    method = "hsmtool",
    pub_key = "sv00-earlgrey-a1-ca-dice-0.pub.der",
    type = "TestKey",
)

# TODO(#22155, #18313): Decide on keyset vs. keyinfo for supplying signing info to the
# offline/token signing flows.  Currently, only keyset supports tokens.
keyset(
    name = "keyset",
    build_setting_default = "",
    keys = {
        "sv00-earlgrey-a1-root-ecdsa-prod-0.pub.der": "sv00-earlgrey-a1-root-ecdsa-prod-0",
        "sv00-earlgrey-a1-root-ecdsa-prod-1.pub.der": "sv00-earlgrey-a1-root-ecdsa-prod-1",
        "sv00-earlgrey-a1-root-ecdsa-prod-2.pub.der": "sv00-earlgrey-a1-root-ecdsa-prod-2",
        "sv00-earlgrey-a1-root-ecdsa-test-0.pub.der": "sv00-earlgrey-a1-root-ecdsa-test-0",
    },
    profile = "earlgrey_a1_sival_root",
    tool = "//signing:token",
)

keyset(
    name = "endorsement",
    build_setting_default = "",
    keys = {
        "sv00-earlgrey-a1-ca-dice-0.pub.der": "sv00-earlgrey-a1-ca-dice-0",
    },
    profile = "earlgrey_a1_sival_root",
    tool = "//signing:token",
)

otp_json_rot_keys(
    name = "ecdsa_root_keys",
    partitions = [
        otp_partition(
            name = "ROT_CREATOR_AUTH_CODESIGN",
            items = {
                # sv00-earlgrey-a1-root-ecdsa-prod-0.pub.der
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE0": otp_hex(CONST.SIGVERIFY.KEY_TYPE.PROD),
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY0": "0x112eb53614cd78573bfb44005f1f81f71ad8bc614f9b1f0848650d82b6cbbebac48c696274cbb86ede569ca56444702e91e7b09d661f560151ea3f688aa047bb",

                # sv00-earlgrey-a1-root-ecdsa-prod-1.pub.der
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE1": otp_hex(CONST.SIGVERIFY.KEY_TYPE.PROD),
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY1": "0x8f522f2bcf8ca3f443d70b86f2479b3cc73d4c1384363edc38cf545ad6aaf46d2a7f529f489446e9d29e7624af46824f2964ca991cd5c4d84adc632bc436fc3d",

                # sv00-earlgrey-a1-root-ecdsa-prod-2.pub.der
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE2": otp_hex(CONST.SIGVERIFY.KEY_TYPE.PROD),
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY2": "0x1295b177eaec69f04c421e8f58bb55f89c8001ba1c3e5f45bec154fb25136e20bde6d117d7ff3af127348cb63574ccc3da8a1db44660350908384089a7948feb",

                # sv00-earlgrey-a1-root-ecdsa-test-0.pub.der
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE3": otp_hex(CONST.SIGVERIFY.KEY_TYPE.TEST),
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY3": "0x39dc04654afd697af53f530a3806de08f4d513f4e7bdb33ede83bf38960005ea3b4c161ce2acf000babd10689f8da3a3132eff0b3bbdf26acacaa3d3473d006d",
            },
        ),
        otp_partition(
            name = "ROT_CREATOR_AUTH_STATE",
            items = {
                "ROT_CREATOR_AUTH_STATE_ECDSA_KEY0": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_ECDSA_KEY1": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_ECDSA_KEY2": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_ECDSA_KEY3": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
            },
        ),
    ],
)
