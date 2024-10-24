// Copyright lowRISC contributors (OpenTitan project).
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

// TODO(#21204): Refactor to use `manifest_check` from `lib/manifest.h`.
OT_WARN_UNUSED_RESULT
static inline rom_error_t manifest_check_rom_ext(const manifest_t *manifest) {
  // Major version must be `kManifestVersionMajor1`.
  if (manifest->manifest_version.major != kManifestVersionMajor1) {
    return kErrorManifestBadVersionMajor;
  }

  // Signed region must be inside the image.
  if (manifest->signed_region_end > manifest->length) {
    return kErrorManifestBadSignedRegion;
  }

  // Executable region must be non-empty, inside the signed region, located
  // after the manifest, and word aligned.
  if (manifest->code_start >= manifest->code_end ||
      manifest->code_start < sizeof(manifest_t) ||
      manifest->code_end > manifest->signed_region_end ||
      (manifest->code_start & 0x3) != 0 || (manifest->code_end & 0x3) != 0) {
    return kErrorManifestBadCodeRegion;
  }

  // Entry point must be inside the executable region and word aligned.
  if (manifest->entry_point < manifest->code_start ||
      manifest->entry_point >= manifest->code_end ||
      (manifest->entry_point & 0x3) != 0) {
    return kErrorManifestBadEntryPoint;
  }

  return kErrorOk;
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

  RETURN_IF_ERROR(manifest_check_rom_ext(manifest));
  return kErrorOk;
}

extern const manifest_t *rom_ext_boot_policy_manifest_a_get(void);
extern const manifest_t *rom_ext_boot_policy_manifest_b_get(void);
