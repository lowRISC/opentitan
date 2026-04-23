// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/config.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/alert.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/include/entropy_src.h"

#include "clkmgr_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

otcrypto_status_t otcrypto_security_config_check(
    otcrypto_key_security_level_t security_level) {
  if (launder32(security_level) != kOtcryptoKeySecurityLevelLow) {
    // Check if the jittery clock is enabled.
    uint32_t jittery_clk_en = abs_mmio_read32(
        TOP_EARLGREY_CLKMGR_AON_BASE_ADDR + CLKMGR_JITTER_ENABLE_REG_OFFSET);
    if (launder32(jittery_clk_en) != kMultiBitBool4True) {
      return OTCRYPTO_FATAL_ERR;
    }
    HARDENED_CHECK_EQ(jittery_clk_en, kMultiBitBool4True);

    // Check if the dummy instructions and the data independent timing is
    // enabled in ibex.
    hardened_bool_t ibex_secure_config = ibex_check_security_config();
    if (launder32(ibex_secure_config) == kHardenedBoolFalse) {
      return OTCRYPTO_FATAL_ERR;
    }
    HARDENED_CHECK_EQ(ibex_secure_config, kHardenedBoolTrue);
  } else {
    // Do not check the device config when security level is low.
    HARDENED_CHECK_EQ(security_level, kOtcryptoKeySecurityLevelLow);
  }
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_set_security_config(
    otcrypto_key_security_level_t security_level) {
  if (launder32(security_level) != kOtcryptoKeySecurityLevelLow) {
    // Enable the jittery clock.
    abs_mmio_write32(
        TOP_EARLGREY_CLKMGR_AON_BASE_ADDR + CLKMGR_JITTER_ENABLE_REG_OFFSET,
        kMultiBitBool4True);

    // Enable the dummy instructions and the data independent timing in ibex.
    HARDENED_TRY(ibex_set_security_config());
  } else {
    // Do not check the device config when security level is low.
    HARDENED_CHECK_EQ(security_level, kOtcryptoKeySecurityLevelLow);
  }
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_disable_icache(hardened_bool_t *icache_enabled) {
  HARDENED_TRY(ibex_disable_icache(icache_enabled));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_restore_icache(hardened_bool_t icache_enabled) {
  ibex_restore_icache(icache_enabled);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_init(otcrypto_key_security_level_t security_level) {
  HARDENED_TRY(otcrypto_set_security_config(security_level));

  HARDENED_TRY(init_alert_registers());

  // Instantiate the RNG.
  HARDENED_TRY(otcrypto_entropy_init());

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_eval_exit(otcrypto_status_t status) {
  if (read_alert_registers()) {
    return OTCRYPTO_FATAL_ERR;
  }
  HARDENED_CHECK_EQ(launder32(read_alert_registers()), 0);

  // Verify the entropy source before leaving.
  HARDENED_TRY(otcrypto_entropy_health_test_config_check());

  return status;
}
