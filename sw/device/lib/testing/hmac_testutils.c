// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/hmac_testutils.h"

#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/testing/check.h"

void hmac_testutils_check_message_length(const dif_hmac_t *hmac,
                                         uint64_t expected_sent_bits) {
  uint64_t sent_bits;
  CHECK_DIF_OK(dif_hmac_get_message_length(hmac, &sent_bits));

  // 64bit formatting is not supported, so split into hi and lo hex 32bit
  // values. These should appear as 64bit hex values in the debug output.
  CHECK(expected_sent_bits == sent_bits,
        "Message length mismatch. "
        "Expected 0x%08x%08x bits but got 0x%08x%08x bits.",
        (uint32_t)(expected_sent_bits >> 32), (uint32_t)expected_sent_bits,
        (uint32_t)(sent_bits >> 32), (uint32_t)sent_bits);
}
