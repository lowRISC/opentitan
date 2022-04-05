// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/boot_policy.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
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

rom_error_t boot_policy_manifest_check(const manifest_t *manifest,
                                       const boot_data_t *boot_data) {
  if (manifest->identifier != MANIFEST_IDENTIFIER_ROM_EXT) {
    return kErrorBootPolicyBadIdentifier;
  }
  if (manifest->length < MANIFEST_LENGTH_FIELD_ROM_EXT_MIN ||
      manifest->length > MANIFEST_LENGTH_FIELD_ROM_EXT_MAX) {
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
