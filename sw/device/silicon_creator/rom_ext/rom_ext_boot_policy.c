// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy_ptrs.h"

rom_ext_boot_policy_manifests_t rom_ext_boot_policy_manifests_get(
    const boot_data_t *boot_data) {
  const manifest_t *slot_a = rom_ext_boot_policy_manifest_a_get();
  const manifest_t *slot_b = rom_ext_boot_policy_manifest_b_get();
  uint32_t slot = boot_data->primary_bl0_slot;
  switch (launder32(slot)) {
    case kBootDataSlotA:
      HARDENED_CHECK_EQ(slot, kBootDataSlotA);
      return (rom_ext_boot_policy_manifests_t){
          .ordered = {slot_a, slot_b},
      };
    case kBootDataSlotB:
      HARDENED_CHECK_EQ(slot, kBootDataSlotB);
      return (rom_ext_boot_policy_manifests_t){
          .ordered = {slot_b, slot_a},
      };
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
}

rom_error_t rom_ext_boot_policy_manifest_check(const manifest_t *manifest,
                                               const boot_data_t *boot_data) {
  if (manifest->identifier != CHIP_BL0_IDENTIFIER) {
    return kErrorBootPolicyBadIdentifier;
  }
  if (manifest->length < CHIP_BL0_SIZE_MIN ||
      manifest->length > CHIP_BL0_SIZE_MAX) {
    return kErrorBootPolicyBadLength;
  }
  if (manifest->security_version < boot_data->min_security_version_bl0) {
    return kErrorBootPolicyRollback;
  }
  HARDENED_CHECK_GE(manifest->security_version,
                    boot_data->min_security_version_bl0);

  RETURN_IF_ERROR(manifest_check(manifest));
  return kErrorOk;
}

extern const manifest_t *rom_ext_boot_policy_manifest_a_get(void);
extern const manifest_t *rom_ext_boot_policy_manifest_b_get(void);
