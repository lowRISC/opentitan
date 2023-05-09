// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_status.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/status.h"

hardened_bool_t hardened_status_ok(status_t s) {
  const int32_t laundered_value = (int32_t)launder32((uint32_t)s.value);
  if (laundered_value == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ((hardened_bool_t)s.value, kHardenedBoolTrue);
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}
