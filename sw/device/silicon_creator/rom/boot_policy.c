// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/boot_policy.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/rom/boot_policy_ptrs.h"

rom_error_t boot_policy_choose_slot(boot_policy_t *boot_policy) {
  const manifest_t *slot_a = boot_policy_manifest_a_load();
  if (slot_a == NULL) {
    return kErrorBootPolicyLoadFailure;
  }
  const manifest_t *slot_b = boot_policy_manifest_b_load();
  if (slot_b == NULL) {
    return kErrorBootPolicyLoadFailure;
  }
  HARDENED_CHECK_NE(slot_a, NULL);
  HARDENED_CHECK_NE(slot_b, NULL);

  // Choose the ROM_EXT with the greater security version.
  // - If equal, choose the ROM_EXT with the greater major version.
  // - If equal, choose the ROM_EXT with the greater minor version,
  // - If equal, prefer slot A.
  boot_slot_t choice = kBootSlotUnspecified;
  if (slot_a->security_version > slot_b->security_version) {
    choice = kBootSlotA;
  } else if (slot_a->security_version < slot_b->security_version) {
    choice = kBootSlotB;
  } else if (slot_a->version_major > slot_b->version_major) {
    choice = kBootSlotA;
  } else if (slot_a->version_major < slot_b->version_major) {
    choice = kBootSlotB;
  } else if (slot_a->version_minor >= slot_b->version_minor) {
    choice = kBootSlotA;
  } else {
    choice = kBootSlotB;
  }

  boot_policy_manifest_a_unload();
  boot_policy_manifest_b_unload();
  boot_policy->first_choice = choice;
  return kErrorOk;
}

static nvm_data_id_t get_data_id_of_boot_slot(boot_slot_t boot_slot) {
  switch (launder32(boot_slot)) {
    case kBootSlotA:
      HARDENED_CHECK_EQ(boot_slot, kBootSlotA);
      return kNvmDataIdRomExtSlotA;
    case kBootSlotB:
      HARDENED_CHECK_EQ(boot_slot, kBootSlotB);
      return kNvmDataIdRomExtSlotB;
    default:
      break;
  }
  return kNvmDataIdInvalid;
}

const void *boot_policy_load_image(boot_slot_t boot_slot) {
  nvm_data_id_t data_id = get_data_id_of_boot_slot(boot_slot);
  if (nvm_data_load(data_id) != kErrorOk) {
    return NULL;
  }
  void *data_ptr = NULL;
  if (nvm_data_get(data_id, &data_ptr, NULL) != kErrorOk) {
    return NULL;
  }
  return data_ptr;
}

const void *boot_policy_get_image(boot_slot_t boot_slot) {
  void *data_ptr = NULL;
  nvm_data_id_t data_id = get_data_id_of_boot_slot(boot_slot);
  rom_error_t error = nvm_data_get(data_id, &data_ptr, NULL);
  if (error != kErrorOk) {
    return NULL;
  }
  return data_ptr;
}

void boot_policy_unload_image(boot_slot_t boot_slot) {
  nvm_data_id_t data_id = get_data_id_of_boot_slot(boot_slot);
  nvm_data_unload(data_id);
}

rom_error_t boot_policy_manifest_check(const manifest_t *manifest,
                                       const boot_data_t *boot_data) {
  if (manifest->identifier != CHIP_ROM_EXT_IDENTIFIER) {
    return kErrorBootPolicyBadIdentifier;
  }
  if (manifest->length < CHIP_ROM_EXT_SIZE_MIN ||
      manifest->length > CHIP_ROM_EXT_RESIZABLE_SIZE_MAX) {
    return kErrorBootPolicyBadLength;
  }
  RETURN_IF_ERROR(manifest_check(manifest));

  if (launder32(manifest->security_version) >=
      boot_data->min_security_version_rom_ext) {
    HARDENED_CHECK_GE(manifest->security_version,
                      boot_data->min_security_version_rom_ext);
    return kErrorOk;
  }
  return kErrorBootPolicyRollback;
}
