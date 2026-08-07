// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/keymgr_dpe.h"
#include "sw/device/silicon_creator/manuf/lib/nvm_info_field.h"

/**
 * Keymgr dpe constant
 */
// TODO(#30777): Replace the hard-coded slot number
// Slot Number must match with the ones defined in dice_chain.c!
// Pre-defined slot id for the attestation / sealing key chain
enum {
  /**
   * Keymgr DPE default slot for sealing context
   */
  kKeymgrDPESealSlot = 0,
  /**
   * Keymgr DPE default slot for attestation context
   */
  kKeymgrDPEAttestSlot = 1,
};

// UDS (Creator) attestation key diversifier constants.
// Note: versions are always set to 0 so these keys are always valid from the
// perspective of the keymgr hardware.
const sc_keymgr_dpe_diversification_t kUdsKeymgrDiversifier = {
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
    // Note: The sel_src_slot has to match the const var
    // kKeymgrDPEAttestSlot in dice_chain.c
    .sel_src_slot = kKeymgrDPEAttestSlot,
};
// CDI_0 (OwnerIntermediate) attestation key diversifier constants.
const sc_keymgr_dpe_diversification_t kCdi0KeymgrDiversifier = {
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
    // Note: The sel_src_slot has to match the const var
    // kKeymgrDPEAttestSlot in dice_chain.c
    .sel_src_slot = kKeymgrDPEAttestSlot,
};
// CDI_1 (Owner) attestation key diversifier constants.
const sc_keymgr_dpe_diversification_t kCdi1KeymgrDiversifier = {
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
    // Note: The sel_src_slot has to match the const var
    // kKeymgrDPEAttestSlot in dice_chain.c
    .sel_src_slot = kKeymgrDPEAttestSlot,
};

const sc_keymgr_dpe_ecc_key_t kDiceKeyUds = {
    .keygen_seed_idx = kNvmInfoFieldUdsKeySeedIdx,
    .keymgr_dpe_diversifier = &kUdsKeymgrDiversifier,
    .required_keymgr_dpe_state = kScKeymgrDPEStateAvailable,
};

const sc_keymgr_dpe_ecc_key_t kDiceKeyCdi0 = {
    .keygen_seed_idx = kNvmInfoFieldCdi0KeySeedIdx,
    .keymgr_dpe_diversifier = &kCdi0KeymgrDiversifier,
    .required_keymgr_dpe_state = kScKeymgrDPEStateAvailable,
};

const sc_keymgr_dpe_ecc_key_t kDiceKeyCdi1 = {
    .keygen_seed_idx = kNvmInfoFieldCdi1KeySeedIdx,
    .keymgr_dpe_diversifier = &kCdi1KeymgrDiversifier,
    .required_keymgr_dpe_state = kScKeymgrDPEStateAvailable,
};
