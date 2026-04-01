// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/security_config.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"

#include "clkmgr_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

status_t otcrypto_security_config_check(
    otcrypto_key_security_level_t security_level) {
  // Only check the security config on silicon as some of the countermeasures
  // might not be available in other targets.
  if (kDeviceType == kDeviceSilicon) {
    if (launder32(security_level) != kOtcryptoKeySecurityLevelLow) {
#if defined(OPENTITAN_IS_EARLGREY)
      // Check if the jittery clock is enabled on OpenTitan EarlGrey.
      uint32_t jittery_clk_en = abs_mmio_read32(
          TOP_EARLGREY_CLKMGR_AON_BASE_ADDR + CLKMGR_JITTER_ENABLE_REG_OFFSET);
      if (launder32(jittery_clk_en) != kMultiBitBool4True) {
        return OTCRYPTO_FATAL_ERR;
      }
      HARDENED_CHECK_EQ(jittery_clk_en, kMultiBitBool4True);
#endif

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
  } else {
    HARDENED_CHECK_NE(launder32(kDeviceType), kDeviceSilicon);
  }

  return OTCRYPTO_OK;
}
