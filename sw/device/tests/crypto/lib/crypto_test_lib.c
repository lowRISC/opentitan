// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/testing/rand_testutils.h"

// Available security levels. The test randomly chooses one.
static const otcrypto_key_security_level_t available_security_levels[3] = {
    kOtcryptoKeySecurityLevelLow,
    kOtcryptoKeySecurityLevelMedium,
    kOtcryptoKeySecurityLevelHigh,
};

status_t determine_security_level(
    otcrypto_key_security_level_t *security_level) {
  uint32_t sec_lvl_idx = rand_testutils_gen32_range(
      /*min=*/0, /*max=*/ARRAYSIZE(available_security_levels) - 1);
  *security_level = available_security_levels[sec_lvl_idx];
  return OK_STATUS();
}
