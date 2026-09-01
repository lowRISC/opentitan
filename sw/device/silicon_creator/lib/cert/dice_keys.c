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
const sc_keymgr_diversification_t kMldsa44UdsKeymgrDiversifier = {
    .salt =
        {
            0x80bfce96,
            0xc3cfbe88,
            0x10752242,
            0xf5f7be29,
            0x25cffa1d,
            0x91944674,
            0x28b67cff,
            0xc12824a0,
        },
    .version = 0,
};

const sc_keymgr_diversification_t kMldsa87UdsKeymgrDiversifier = {
    .salt =
        {
            0x437c0d55,
            0x000c7d4b,
            0xd3b6e181,
            0x36347dea,
            0xe60c39de,
            0x525785b7,
            0xeb75bf3c,
            0x02ebe763,
        },
    .version = 0,
};

// ML-DSA CDI_0 attestation key diversifier constants.
const sc_keymgr_diversification_t kMldsa44Cdi0KeymgrDiversifier = {
    .salt =
        {
            0xbdcffff3,
            0x320bc067,
            0x532611f9,
            0x28cf6063,
            0x95f26cec,
            0x4b8d6a92,
            0x9eb305af,
            0x72443878,
        },
    .version = 0,
};

const sc_keymgr_diversification_t kMldsa87Cdi0KeymgrDiversifier = {
    .salt =
        {
            0x7e0c3c30,
            0xf1c803a4,
            0x90e5d23a,
            0xeb0ca3a0,
            0x5631af2f,
            0x884ea951,
            0x5d70c66c,
            0xb187fbbb,
        },
    .version = 0,
};

// ML-DSA CDI_1 attestation key diversifier constants.
const sc_keymgr_diversification_t kMldsa44Cdi1KeymgrDiversifier = {
    .salt =
        {
            0xa6ba659e,
            0xe53dd2e0,
            0x6c2634ea,
            0x594649f6,
            0x7b0958bd,
            0xa3f1f720,
            0xaa9d921,
            0x42d89da,
        },
    .version = 0,
};

const sc_keymgr_diversification_t kMldsa87Cdi1KeymgrDiversifier = {
    .salt =
        {
            0x6579a65d,
            0x26fe1123,
            0xafe5f729,
            0x9a858a35,
            0xb8ca9b7e,
            0x603234e3,
            0xc96a1ae2,
            0xc7ee4a19,
        },
    .version = 0,
};

const sc_keymgr_ecc_key_t kDiceKeyMldsa44Uds = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldMldsaUdsKeySeedIdx,
    .keymgr_diversifier = &kMldsa44UdsKeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateCreatorRootKey,
};

const sc_keymgr_ecc_key_t kDiceKeyMldsa44Cdi0 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldMldsaCdi0KeySeedIdx,
    .keymgr_diversifier = &kMldsa44Cdi0KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerIntermediateKey,
};

const sc_keymgr_ecc_key_t kDiceKeyMldsa44Cdi1 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldMldsaCdi1KeySeedIdx,
    .keymgr_diversifier = &kMldsa44Cdi1KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerKey,
};

const sc_keymgr_ecc_key_t kDiceKeyMldsa87Uds = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldMldsaUdsKeySeedIdx,
    .keymgr_diversifier = &kMldsa87UdsKeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateCreatorRootKey,
};

const sc_keymgr_ecc_key_t kDiceKeyMldsa87Cdi0 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldMldsaCdi0KeySeedIdx,
    .keymgr_diversifier = &kMldsa87Cdi0KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerIntermediateKey,
};

const sc_keymgr_ecc_key_t kDiceKeyMldsa87Cdi1 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldMldsaCdi1KeySeedIdx,
    .keymgr_diversifier = &kMldsa87Cdi1KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerKey,
};
