// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/boot_policy.h"

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

rom_error_t boot_policy_manifest_check(const manifest_t *manifest) {
  RETURN_IF_ERROR(manifest_check(manifest));
  if (manifest->identifier != kBootPolicyRomExtIdentifier) {
    return kErrorBootPolicyBadIdentifier;
  }
  // TODO(#7879): Implement anti-rollback.
  uint32_t min_security_version = 0;
  if (manifest->security_version < min_security_version) {
    return kErrorBootPolicyRollback;
  }
  return kErrorOk;
}

extern const manifest_t *boot_policy_manifest_a_get(void);
extern const manifest_t *boot_policy_manifest_b_get(void);
