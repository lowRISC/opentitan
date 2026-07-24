// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy_ptrs.h"

const manifest_t *rom_ext_boot_policy_slot_a_manifest = NULL;
const manifest_t *rom_ext_boot_policy_slot_b_manifest = NULL;

const manifest_t *rom_ext_boot_policy_manifest_bank_search(
    uintptr_t bank_base, const boot_data_t *boot_data) {
  // Search backward. Searching backward is important because the region before
  // the active firmware (e.g. if active is at the higher offset) might not be
  // write-protected, allowing an attacker to write a malicious manifest at a
  // lower offset. By searching backward, we prefer the legitimate active
  // firmware at the higher offset. Thus, the array elements must be defined in
  // descending order.
  static const uint32_t kOwnerOffsets[] = {
#ifdef OT_COVERAGE_ENABLED
      168 * 1024,
      128 * 1024,
#endif
      88 * 1024,
      64 * 1024,
  };
  const size_t kNumOffsets = sizeof(kOwnerOffsets) / sizeof(kOwnerOffsets[0]);

  // Default candidate for error reporting (lowest offset).
  const manifest_t *candidate =
      (const manifest_t *)(bank_base + kOwnerOffsets[kNumOffsets - 1]);

  for (size_t i = 0; i < kNumOffsets; ++i) {
    const manifest_t *manifest =
        (const manifest_t *)(bank_base + kOwnerOffsets[i]);
    if (manifest->identifier == CHIP_BL0_IDENTIFIER) {
      candidate = manifest;
      if (rom_ext_boot_policy_manifest_check(manifest, boot_data) == kErrorOk) {
        return manifest;
      }
    }
  }
  return candidate;
}

void rom_ext_boot_policy_manifest_search(const boot_data_t *boot_data) {
  rom_ext_boot_policy_slot_a_manifest =
      rom_ext_boot_policy_manifest_bank_search(TOP_EARLGREY_EFLASH_BASE_ADDR,
                                               boot_data);
  rom_ext_boot_policy_slot_b_manifest =
      rom_ext_boot_policy_manifest_bank_search(
          TOP_EARLGREY_EFLASH_BASE_ADDR + (TOP_EARLGREY_EFLASH_SIZE_BYTES / 2),
          boot_data);
}

rom_ext_boot_policy_manifests_t rom_ext_boot_policy_manifests_get(
    const boot_data_t *boot_data) {
  const manifest_t *slot_a = rom_ext_boot_policy_manifest_a_get(boot_data);
  const manifest_t *slot_b = rom_ext_boot_policy_manifest_b_get(boot_data);
  uint32_t slot = boot_data->primary_bl0_slot;
  switch (launder32(slot)) {
    case kBootSlotB:
      HARDENED_CHECK_EQ(slot, kBootSlotB);
      return (rom_ext_boot_policy_manifests_t){
          .ordered = {slot_b, slot_a},
      };
    case kBootSlotA:
      OT_FALLTHROUGH_INTENDED;
    default:
      return (rom_ext_boot_policy_manifests_t){
          .ordered = {slot_a, slot_b},
      };
  }
}
