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
                # //sw/device/silicon_creator/rom/keys/fake/ecdsa:test_key_0_ecdsa_p256
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE0": otp_hex(CONST.SIGVERIFY.KEY_TYPE.TEST),
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY0": "0xdeb1e092bb56aeb4a5d7eb1df773fc51012abb223c413ac2444da9ded8e17e502e66e6cb6937e2375bcb453d845024cfe9e0f4807bfccca80bba6de3ee07109a",

                # //sw/device/silicon_creator/rom/keys/fake/ecdsa:dev_key_0_ecdsa_p256
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE1": otp_hex(CONST.SIGVERIFY.KEY_TYPE.DEV),
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY1": "0xce8c4b5b70df4ad0c9dbc64bf7a103fdb1dfa2cc40529329ba9eb9172fbccaafd0b7ee1365a85787b9e7bf8aa742ec258ce157388a01ceb04f7ed1a3c11c931c",

                # //sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE2": otp_hex(CONST.SIGVERIFY.KEY_TYPE.PROD),
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY2": "0x7e571d04866f12e00a5b3c2e734ebd05611a0325ef6d90140e3cd2091ddda9bd8277988ce6557b33923499d90eeeff0028a525c10fa3a5a438daf96b9bf2dafd",

                # //sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_1_ecdsa_p256
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE3": otp_hex(CONST.SIGVERIFY.KEY_TYPE.PROD),
                "ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY3": "0xb70fd07db1c79bbb87f974e6d3ea06e1f120582d2e8abaf1ddd1167aac4d7547fbf0b76ae2838f6cec711f34204d24202fccd456ad9f2278d80fe551423e545e",

                # //sw/device/silicon_creator/rom/keys/fake/spx:test_key_0_spx
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE0": otp_hex(CONST.SIGVERIFY.KEY_TYPE.TEST),
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY0": "0xe202fb8327bfd3b24970920cf92093cb3af233b1070e42321d8088c79bd30901",
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG0": otp_hex(CONST.SPX_CONFIG_ID.SHAKE_128S),

                # //sw/device/silicon_creator/rom/keys/fake/spx:dev_key_0_spx
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE1": otp_hex(CONST.SIGVERIFY.KEY_TYPE.DEV),
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY1": "0xbdb32442347a3384bec586d69364a4ae9f60f360473ce5929e27e0db8d098a72",
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG1": otp_hex(CONST.SPX_CONFIG_ID.SHAKE_128S),

                # //sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE2": otp_hex(CONST.SIGVERIFY.KEY_TYPE.PROD),
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY2": "0x16fa2a9ca646ec95d1561e5396599d445329ec12a629c27c8542ae8669fc0e38",
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG2": otp_hex(CONST.SPX_CONFIG_ID.SHAKE_128S),

                # //sw/device/silicon_creator/rom/keys/fake/spx:prod_key_1_spx
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_TYPE3": otp_hex(CONST.SIGVERIFY.KEY_TYPE.PROD),
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY3": "0xd7aa1829d5a7158e4615c2ee4bb9d0204f58d90d42d832c85c4cee6ed89bea85",
                "ROT_CREATOR_AUTH_CODESIGN_SPX_KEY_CONFIG3": otp_hex(CONST.SPX_CONFIG_ID.SHAKE_128S),
            },
        ),
        otp_partition(
            name = "ROT_CREATOR_AUTH_STATE",
            items = {
                "ROT_CREATOR_AUTH_STATE_ECDSA_KEY0": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_ECDSA_KEY1": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_ECDSA_KEY2": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_ECDSA_KEY3": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_SPX_KEY0": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_SPX_KEY1": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_SPX_KEY2": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
                "ROT_CREATOR_AUTH_STATE_SPX_KEY3": otp_hex(CONST.SIGVERIFY.KEY_STATE.PROVISIONED),
            },
        ),
    ],
)
