// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

// UDS (Creator) attestation key diverisfier constants.
// Note: versions are always set to 0 so these keys are always valid from the
// perspective of the keymgr hardware.
const sc_keymgr_diversification_t kUdsKeymgrDiversifier = {
    .salt =
        {
            0xabffa6a9,
            0xc781f1ad,
            0x4c1107ad,
            0xf9210d85,
            0x0931f555,
            0x6c5aef5d,
            0xb9ba4df0,
            0x77b248d2,
        },
    .version = 0,
};
// CDI_0 (OwnerIntermediate) attestation key diverisfier constants.
const sc_keymgr_diversification_t kCdi0KeymgrDiversifier = {
    .salt =
        {
            0x3e5913c7,
            0x41156f1d,
            0x998ddb9f,
            0xfa334191,
            0x8a85380e,
            0xba76ca1a,
            0xdb17c4a7,
            0xfb8852dc,
        },
    .version = 0,
};
// CDI_1 (Owner) attestation key diverisfier constants.
const sc_keymgr_diversification_t kCdi1KeymgrDiversifier = {
    .salt =
        {
            0x2d12c2e3,
            0x6acc6876,
            0x4bfb07ee,
            0xc45fc414,
            0x5d4fa9de,
            0xf295b128,
            0x50f49882,
            0xbbdefa29,
        },
    .version = 0,
};

const sc_keymgr_ecc_key_t kDiceKeyUds = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldUdsKeySeedIdx,
    .keymgr_diversifier = &kUdsKeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateCreatorRootKey,
};

const sc_keymgr_ecc_key_t kDiceKeyCdi0 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldCdi0KeySeedIdx,
    .keymgr_diversifier = &kCdi0KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerIntermediateKey,
};

const sc_keymgr_ecc_key_t kDiceKeyCdi1 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldCdi1KeySeedIdx,
    .keymgr_diversifier = &kCdi1KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerKey,
};

// ML-DSA UDS attestation key diversifier constants.
const sc_keymgr_diversification_t kMldsaUdsKeymgrDiversifier = {
    .salt =
        {
            0xc4fb8ad2,
            0x878bfacc,
            0x54316606,
            0xb1b3fa6d,
            0x618bbe59,
            0xd5d00230,
            0x6cf238bb,
            0x856c60e4,
        },
    .version = 0,
};

// ML-DSA CDI_0 attestation key diversifier constants.
const sc_keymgr_diversification_t kMldsaCdi0KeymgrDiversifier = {
    .salt =
        {
            0xf98bbbb7,
            0x764f8423,
            0x176255bd,
            0x6c8b2427,
            0xd1b628a8,
            0x0fc92ed6,
            0xdaf741eb,
            0x36007c3c,
        },
    .version = 0,
};

// ML-DSA CDI_1 attestation key diversifier constants.
const sc_keymgr_diversification_t kMldsaCdi1KeymgrDiversifier = {
    .salt =
        {
            0xe2fe21da,
            0xa17996a4,
            0x286270ae,
            0x1d020db2,
            0x3f4d1cf9,
            0xe7b5b364,
            0x4eed9d65,
            0x4069cd9e,
        },
    .version = 0,
};

const sc_keymgr_ecc_key_t kDiceKeyMldsaUds = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldMldsaUdsKeySeedIdx,
    .keymgr_diversifier = &kMldsaUdsKeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateCreatorRootKey,
};

const sc_keymgr_ecc_key_t kDiceKeyMldsaCdi0 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldMldsaCdi0KeySeedIdx,
    .keymgr_diversifier = &kMldsaCdi0KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerIntermediateKey,
};

const sc_keymgr_ecc_key_t kDiceKeyMldsaCdi1 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldMldsaCdi1KeySeedIdx,
    .keymgr_diversifier = &kMldsaCdi1KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerKey,
};
