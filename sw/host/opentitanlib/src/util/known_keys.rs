// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::collection;
use once_cell::sync::Lazy;
use std::collections::HashMap;

pub static KNOWN_KEYS: Lazy<HashMap<u32, &'static str>> = Lazy::new(|| {
    collection! {
        // Earlgrey A1 SiVAL sku keys.
        0x8aa047bb => "sv00-earlgrey-a1-root-ecdsa-prod-0 (ECDSA P256)",
        0xc436fc3d => "sv00-earlgrey-a1-root-ecdsa-prod-1 (ECDSA P256)",
        0xa7948feb => "sv00-earlgrey-a1-root-ecdsa-prod-2 (ECDSA P256)",
        0x473d006d => "sv00-earlgrey-a1-root-ecdsa-test-0 (ECDSA P256)",
        0x85eaf1aa => "sv00-earlgrey-a1-ca-dice-0 (ECDSA P256)",
        0x9b53344b => "sv00-app-key-prod-0 (ECDSA P256)",
        0x62d920f3 => "sv00-ownership-owner-0 (ECDSA P256)",
        0x566482ec => "sv00-ownership-unlock-0 (ECDSA P256)",
        0x7a7d6398 => "sv00-app-key-dev-0 (ECDSA P256)",
        0x62b66f69 => "sv00-app-key-test-0 (ECDSA P256)",
        0x0dcd2600 => "sv00-ownership-activate-0 (ECDSA P256)",

        // Earlgrey A1 bringup sku keys.
        0x421f9033 => "gb00-earlgrey-a1-ca-cros-sku-0 (ECDSA P256)",
        0xd9e1bbf7 => "gb00-earlgrey-a1-ca-dice-0 (ECDSA P256)",
        0x537f2f94 => "gb00-earlgrey-a1-root-ecdsa-prod-0 (ECDSA P256)",
        0x068e5abd => "gb00-earlgrey-a1-root-ecdsa-prod-2 (ECDSA P256)",
        0x80800406 => "gb00-earlgrey-a1-root-ecdsa-test-0 (ECDSA P256)",
        0xbcf347ae => "gb00-earlgrey-a1-root-ecdsa-prod-1 (ECDSA P256)",
        0x3cb98bb9 => "gb00-ownership-unlock-0 (ECDSA P256)",
        0xe68fa35b => "gb00-app-key-test-0 (ECDSA P256)",
        0x44611d1c => "gb00-app-key-dev-0 (ECDSA P256)",
        0x7f8de7c7 => "gb00-app-key-prod-0 (ECDSA P256)",
        0xd1456f6c => "gb00-ownership-activate-0 (ECDSA P256)",
        0x87a76721 => "gb00-ownership-owner-0 (ECDSA P256)",

        // Test-only keys used for FPGA and simulations.
        0xc3061a8c => "sw/device/silicon_creator/rom/keys/unauthorized/ecdsa/unauthorized_key_0_ecdsa_p256.pub.der",
        0x9bf2dafd => "sw/device/silicon_creator/rom/keys/fake/ecdsa/prod_key_0_ecdsa_p256.pub.der",
        0x423e545e => "sw/device/silicon_creator/rom/keys/fake/ecdsa/prod_key_1_ecdsa_p256.pub.der",
        0xc11c931c => "sw/device/silicon_creator/rom/keys/fake/ecdsa/dev_key_0_ecdsa_p256.pub.der",
        0xee07109a => "sw/device/silicon_creator/rom/keys/fake/ecdsa/test_key_0_ecdsa_p256.pub.der",
        0x665ff5e3 => "sw/device/silicon_creator/lib/ownership/keys/dummy/owner_ecdsa_p256.pub.der",
        0x922bc9ea => "sw/device/silicon_creator/lib/ownership/keys/dummy/activate_ecdsa_p256.pub.der",
        0xc8489315 => "sw/device/silicon_creator/lib/ownership/keys/dummy/unlock_ecdsa_p256.pub.der",
        0xe264966d => "sw/device/silicon_creator/lib/ownership/keys/dummy/app_prod_ecdsa_p256.pub.der",
        0x8e3dcb50 => "sw/device/silicon_creator/lib/ownership/keys/fake/owner_ecdsa_p256.pub.der",
        0xced1f3c1 => "sw/device/silicon_creator/lib/ownership/keys/fake/app_test_ecdsa_p256.pub.der",
        0x63a31253 => "sw/device/silicon_creator/lib/ownership/keys/fake/activate_ecdsa_p256.pub.der",
        0x113f87b2 => "sw/device/silicon_creator/lib/ownership/keys/fake/unlock_ecdsa_p256.pub.der",
        0xddd43a0c => "sw/device/silicon_creator/lib/ownership/keys/fake/app_dev_ecdsa_p256.pub.der",
        0x265b676b => "sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_ecdsa_p256.pub.der",
        0x81401b6d => "sw/device/silicon_creator/lib/ownership/keys/fake/no_owner_recovery_ecdsa_p256.pub.der",
        0xb0b5537f => "sw/device/silicon_creator/lib/ownership/keys/fake/app_unauthorized_ecdsa_p256.pub.der",
        0xbd1f2453 => "sw/device/silicon_creator/rom/keys/unauthorized/rsa/unauthorized_0_rsa_3072_exp_f4.pub.der",
        0x6a100995 => "sw/device/silicon_creator/manuf/keys/sival/rma_unlock_enc_rsa3072.pub.der",
        0xd7a68199 => "sw/device/silicon_creator/manuf/keys/fake/rma_unlock_enc_rsa3072.pub.der",

        // RSA root keys for earlgrey_es
        0xa721bf61 => "earlgrey_a0_prod_0 (RSA3072 earlgrey_es)",
        0x7b3bbe01 => "earlgrey_a0_prod_1 (RSA3072 earlgrey_es)",
        0xfd2152d1 => "earlgrey_a0_prod_2 (RSA3072 earlgrey_es)",
        0xdb6186cd => "earlgrey_a0_dev_0 (RSA3072 earlgrey_es)",
        0xd0456c25 => "earlgrey_a0_dev_1 (RSA3072 earlgrey_es)",
        0xf6ccf943 => "earlgrey_a0_test_0 (RSA3072 earlgrey_es)",
        0x5b0036ff => "earlgrey_a0_test_1 (RSA3072 earlgrey_es)",
        0xb4bc349d => "sw/device/silicon_creator/rom/keys/fake/rsa/prod_key_0_rsa_3072_exp_f4.pub.der (earlgrey_es)",
        0x84ec3a97 => "sw/device/silicon_creator/rom/keys/fake/rsa/prod_key_1_rsa_3072_exp_f4.pub.der (earlgrey_es)",
        0x57a2fc91 => "sw/device/silicon_creator/rom/keys/fake/rsa/prod_key_2_rsa_3072_exp_f4.pub.der (earlgrey_es)",
        0xad958447 => "sw/device/silicon_creator/rom/keys/fake/rsa/dev_key_0_rsa_3072_exp_f4.pub.der (earlgrey_es)",
        0xe63058b7 => "sw/device/silicon_creator/rom/keys/fake/rsa/dev_key_1_rsa_3072_exp_f4.pub.der (earlgrey_es)",
        0x5801a2bd => "sw/device/silicon_creator/rom/keys/fake/rsa/test_key_0_rsa_3072_exp_f4.pub.der (earlgrey_es)",
        0xcf9d18b3 => "sw/device/silicon_creator/rom/keys/fake/rsa/test_key_1_rsa_3072_exp_f4.pub.der (earlgrey_es)",

        // Application and owner keys for earlgrey_es application stage development.
        0x29e0c28c => "appkey_test_0 (ECDSA P256 earlgrey_es proda)",
        0xf4997f6b => "ownership_unlock_key (ECDSA P256 earlgrey_es proda)",
        0xe394fc4e => "ownership_activate_key (ECDSA P256 earlgrey_es proda)",
        0xdb20fed5 => "appkey_prod_0 (ECDSA P256 earlgrey_es proda)",
        0x791e06cd => "ownership_owner_key.de (ECDSA P256 earlgrey_es proda)r",
        0x16a849e6 => "appkey_dev_0 (ECDSA P256 earlgrey_es proda)",
        0x644e94f3 => "appkey_test_0 (ECDSA P256 earlgrey_es sival)",
        0xbba01e3e => "ownership_unlock_key (ECDSA P256 earlgrey_es sival)",
        0x722fcac6 => "ownership_activate_key (ECDSA P256 earlgrey_es sival)",
        0x03340a84 => "appkey_prod_0 (ECDSA P256 earlgrey_es sival)",
        0x25d3e660 => "ownership_owner_key (ECDSA P256 earlgrey_es sival)",
        0x471b4b2c => "appkey_dev_0 (ECDSA P256 earlgrey_es sival)",
        0xbd790453 => "appkey_test_0 (ECDSA P256 earlgrey_es prodc)",
        0xc7d8c8a4 => "ownership_unlock_key (ECDSA P256 earlgrey_es prodc)",
        0xd2c5b6be => "ownership_activate_key (ECDSA P256 earlgrey_es prodc)",
        0xc075a15f => "appkey_prod_0 (ECDSA P256 earlgrey_es prodc)",
        0xb1688268 => "ownership_owner_key (ECDSA P256 earlgrey_es prodc)",
        0x244e4e4b => "appkey_dev_0 (ECDSA P256 earlgrey_es prodc)",
    }
});
