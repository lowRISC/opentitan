// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_KEYMGR_BINDING_VALUE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_KEYMGR_BINDING_VALUE_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Binding value used by key manager to derive secret values.
 *
 * A change in this value changes the secret value of key manager, and
 * consequently, the versioned keys and identity seeds generated at subsequent
 * boot stages.
 *
 * Note: The size of this value is an implementation detail of the key manager
 * hardware.
 */
typedef struct keymgr_binding_value {
  uint32_t data[8];
} keymgr_binding_value_t;

OT_ASSERT_MEMBER_OFFSET(keymgr_binding_value_t, data, 0);
OT_ASSERT_SIZE(keymgr_binding_value_t, 32);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_KEYMGR_BINDING_VALUE_H_
