// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/dice.h"

#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/dice_chain.h"
#include "sw/device/silicon_creator/lib/cert/dice_keys.h"
#include "sw/device/silicon_creator/lib/cert/dice_storage.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

enum {
  kDiceSlotSize = 936,
};

const dice_storage_slot_t kDiceStorageCdi0Ecdsa = DICE_STORAGE_SLOT(
    "CDI_0", &kFlashCtrlInfoPageDiceCerts,
    /*offset_val=*/0,
    /*slot_size_val=*/kDiceSlotSize, kPersoObjectTypeX509Cert);

const dice_storage_slot_t kDiceStorageCdi1Ecdsa = DICE_STORAGE_SLOT(
    "CDI_1", &kFlashCtrlInfoPageDiceCerts,
    /*offset_val=*/kDiceSlotSize,
    /*slot_size_val=*/kDiceSlotSize, kPersoObjectTypeX509Cert);

static_assert(kDiceMeasurementSizeInBytes == 32,
              "The DICE attestation measurement size should equal the size of "
              "the keymgr binding registers.");

rom_error_t dice_attest_cdi_0(keymgr_binding_value_t *rom_ext_measurement,
                              const manifest_t *rom_ext_manifest) {
  HARDENED_RETURN_IF_ERROR(dice_chain_init());
  HARDENED_RETURN_IF_ERROR(dice_chain_attestation_silicon());
  HARDENED_RETURN_IF_ERROR(ownership_seal_init());
  return dice_chain_attestation_creator(rom_ext_measurement, rom_ext_manifest);
}

rom_error_t dice_attest_cdi_1(const manifest_t *owner_manifest,
                              keymgr_binding_value_t *bl0_measurement,
                              hmac_digest_t *owner_measurement,
                              hmac_digest_t *owner_history_hash,
                              keymgr_binding_value_t *sealing_binding,
                              owner_app_domain_t key_domain) {
  HARDENED_RETURN_IF_ERROR(dice_chain_init());
  HARDENED_RETURN_IF_ERROR(dice_chain_rom_ext_check());
  return dice_chain_attestation_owner(owner_manifest, bl0_measurement,
                                      owner_measurement, owner_history_hash,
                                      sealing_binding, key_domain);
}
