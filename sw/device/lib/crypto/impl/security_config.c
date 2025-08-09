// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/security_config.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/clkmgr.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"

hardened_bool_t security_config_check(void) {
  // Check if the jittery clock is enabled.
  hardened_bool_t jittery_clk_en = clkmgr_check_jittery_clk_en();
  if (launder32(jittery_clk_en) == kHardenedBoolFalse) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_EQ(jittery_clk_en, kHardenedBoolTrue);

  // Check if the dummy instructions and the data independent timing is enabled
  // in ibex.
  hardened_bool_t ibex_secure_config = ibex_check_security_config();
  if (launder32(ibex_secure_config) == kHardenedBoolFalse) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_EQ(ibex_secure_config, kHardenedBoolTrue);

  return kHardenedBoolTrue;
}
