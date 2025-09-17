// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top/dt/dt_clkmgr.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/testing/rand_testutils.h"

enum {
  /**
   * CSR_REG_CPUCTRL[1] is the data independent timing field.
   */
  kCpuctrlDataIndTimingIdx = 1,
  kCpuctrlDataIndTimingMask = (1 << kCpuctrlDataIndTimingIdx),
  /**
   * CSR_REG_CPUCTRL[2] is the dummy instruction enable configuration field.
   */
  kCpuctrlDummyInstrEnIdx = 2,
  kCpuctrlDummyInstrEnMask = (1 << kCpuctrlDummyInstrEnIdx),
};

// Available security levels. The test randomly chooses one.
static const otcrypto_key_security_level_t available_security_levels[3] = {
    kOtcryptoKeySecurityLevelLow,
    kOtcryptoKeySecurityLevelMedium,
    kOtcryptoKeySecurityLevelHigh,
};

status_t determine_security_level(
    otcrypto_key_security_level_t *security_level) {
  // Check jittery clock.
  if (kDtClkmgrCount == 0) {
    // No clock manager available, so we do not have a jittery clock.
    *security_level = kOtcryptoKeySecurityLevelLow;
    return OK_STATUS();
  }

  dif_clkmgr_t clkmgr;
  TRY(dif_clkmgr_init_from_dt(kDtClkmgrAon, &clkmgr));

  dif_toggle_t clk_jitter_status;
  TRY(dif_clkmgr_jitter_get_enabled(&clkmgr, &clk_jitter_status));
  if (clk_jitter_status == kDifToggleDisabled) {
    bool jitter_locked;
    TRY(dif_clkmgr_jitter_enable_is_locked(&clkmgr, &jitter_locked));
    if (jitter_locked) {
      // Clock manager is locked, so we cannot enable the jittery clock.
      *security_level = kOtcryptoKeySecurityLevelLow;
      return OK_STATUS();
    }
    // Jittery clock is off, turn it on.
    TRY(dif_clkmgr_jitter_set_enabled(&clkmgr, kDifToggleEnabled));
  }

  // Set data independent timing.
  CSR_SET_BITS(CSR_REG_CPUCTRL, kCpuctrlDataIndTimingMask);

  // Set dummy instructions.
  CSR_SET_BITS(CSR_REG_CPUCTRL, kCpuctrlDummyInstrEnMask);

  // Read back data independent timing and dummy instruction configuration.
  uint32_t cpuctrl_csr;
  CSR_READ(CSR_REG_CPUCTRL, &cpuctrl_csr);

  if (((cpuctrl_csr & kCpuctrlDataIndTimingMask) >> kCpuctrlDataIndTimingIdx) !=
      1) {
    // Could not enable data independent timing.
    *security_level = kOtcryptoKeySecurityLevelLow;
    return OK_STATUS();
  }

  if (((cpuctrl_csr & kCpuctrlDummyInstrEnMask) >> kCpuctrlDummyInstrEnIdx) !=
      1) {
    // Could not enable dummy instructions.
    *security_level = kOtcryptoKeySecurityLevelLow;
    return OK_STATUS();
  }

  // All required countermeasures are enabled, randomly select a security level.
  // Select a random security level.
  uint32_t sec_lvl_idx = rand_testutils_gen32_range(
      /*min=*/0, /*max=*/ARRAYSIZE(available_security_levels) - 1);
  *security_level = available_security_levels[sec_lvl_idx];
  return OK_STATUS();
}
