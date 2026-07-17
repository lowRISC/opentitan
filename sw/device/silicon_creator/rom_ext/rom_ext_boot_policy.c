// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"

#include "sw/device/silicon_creator/rom_ext/rom_ext_manifest.h"

// TODO(#21204): Refactor to use `manifest_check` from `lib/manifest.h`.
OT_WARN_UNUSED_RESULT
static inline rom_error_t manifest_check_rom_ext(const manifest_t *manifest) {
  // Major version must be `kManifestVersionMajor2`.
  if (manifest->manifest_version.major != kManifestVersionMajor2) {
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

static rom_error_t manifest_base_address_check(const manifest_t *manifest) {
  uintptr_t actual_base = (uintptr_t)manifest;
  uintptr_t expected_base = (uintptr_t)manifest->manifest_base_address;

  // For backward compatibility, skip the check if the expected base address
  // is the default unset value (0xa5a5a5a5) and the remapped address is virtual
  // base + 64K.
  if (expected_base == 0xa5a5a5a5) {
    uintptr_t virtual_base = owner_vma_get((uintptr_t)manifest);
    if (virtual_base == (uintptr_t)_owner_virtual_start_address + 64 * 1024) {
      return kErrorOk;
    }
  }

  if (manifest->address_translation == kHardenedBoolTrue) {
    actual_base = owner_vma_get((uintptr_t)manifest);
  }
  if (expected_base != actual_base) {
    return kErrorManifestBadBaseAddress;
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
  // Sanity check boot_data to reject a bogus pointer.
  HARDENED_CHECK_EQ(boot_data->identifier, kBootDataIdentifier);
  // Launder both values to ensure they are reloaded from memory for the
  // hardened check.
  if (launder32(manifest->security_version) <
      launder32(boot_data->min_security_version_bl0)) {
    return kErrorBootPolicyRollback;
  }
  HARDENED_CHECK_GE(manifest->security_version,
                    boot_data->min_security_version_bl0);

  RETURN_IF_ERROR(manifest_check_rom_ext(manifest));
  RETURN_IF_ERROR(manifest_base_address_check(manifest));
  return kErrorOk;
}
