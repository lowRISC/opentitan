// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/boot_policy.h"

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/mask_rom/boot_policy_ptrs.h"

boot_policy_manifests_t boot_policy_manifests_get(void) {
  const manifest_t *slot_a = boot_policy_manifest_a_get();
  const manifest_t *slot_b = boot_policy_manifest_b_get();
  if (slot_a->security_version >= slot_b->security_version) {
    return (boot_policy_manifests_t){
        .ordered = {slot_a, slot_b},
    };
  }
  return (boot_policy_manifests_t){
      .ordered = {slot_b, slot_a},
  };
}

rom_error_t boot_policy_manifest_check(lifecycle_state_t lc_state,
                                       const manifest_t *manifest) {
  if (manifest->identifier != MANIFEST_IDENTIFIER_ROM_EXT) {
    return kErrorBootPolicyBadIdentifier;
  }
  if (manifest->length < MANIFEST_LENGTH_FIELD_ROM_EXT_MIN ||
      manifest->length > MANIFEST_LENGTH_FIELD_ROM_EXT_MAX) {
    return kErrorBootPolicyBadLength;
  }
  RETURN_IF_ERROR(manifest_check(manifest));
  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(lc_state, &boot_data));
  // TODO(#9491): Harden this comparison.
  if (manifest->security_version < boot_data.min_security_version_rom_ext) {
    return kErrorBootPolicyRollback;
  }
  return kErrorOk;
}

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern const manifest_t *boot_policy_manifest_a_get(void);
extern const manifest_t *boot_policy_manifest_b_get(void);
