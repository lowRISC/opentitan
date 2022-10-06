// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_BOOT_MEASUREMENTS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_BOOT_MEASUREMENTS_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Boot measurements shared between ROM and ROM_EXT boot stages.
 */
typedef struct boot_measurements {
  /**
   * ROM_EXT digest value calculated in ROM. Stored in a format that can be
   * consumed by the key manager.
   *
   * If OTP `ROM_KEYMGR_ROM_EXT_MEAS_EN` is set to `kHardenedBoolTrue`, the
   * rom will use this value to configure the key manager attestation
   * binding registers.
   */
  keymgr_binding_value_t rom_ext;
} boot_measurements_t;

OT_ASSERT_MEMBER_OFFSET(boot_measurements_t, rom_ext, 0);
OT_ASSERT_SIZE(boot_measurements_t, 32);

extern boot_measurements_t boot_measurements;

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_BOOT_MEASUREMENTS_H_
