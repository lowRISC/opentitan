// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/hmac_testutils.h"

#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/test_framework/check.h"

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

/**
 * Checks whether the HMAC FIFO is empty.
 */
static bool check_fifo_empty(const dif_hmac_t *hmac) {
  uint32_t fifo_depth;
  CHECK_DIF_OK(dif_hmac_fifo_count_entries(hmac, &fifo_depth));
  return fifo_depth == 0;
}
void hmac_testutils_fifo_empty_polled(const dif_hmac_t *hmac) {
  IBEX_SPIN_FOR(check_fifo_empty(hmac), HMAC_TESTUTILS_FIFO_EMPTY_USEC);
}

static bool check_finished(const dif_hmac_t *hmac,
                           dif_hmac_digest_t *digest_out) {
  dif_result_t res = dif_hmac_finish(hmac, digest_out);
  CHECK(res == kDifOk || res == kDifUnavailable, "HMAC error = %d", res);

  return res == kDifOk;
}
void hmac_testutils_finish_polled(const dif_hmac_t *hmac,
                                  dif_hmac_digest_t *digest_out) {
  IBEX_SPIN_FOR(check_finished(hmac, digest_out),
                HMAC_TESTUTILS_FINISH_TIMEOUT_USEC);
}

void hmac_testutils_finish_and_check_polled(const dif_hmac_t *hmac,
                                            const dif_hmac_digest_t *expected) {
  dif_hmac_digest_t digest;
  hmac_testutils_finish_polled(hmac, &digest);
  CHECK_BUFFER(digest.digest, expected, ARRAYSIZE(digest.digest));
}

void hmac_testutils_push_message(const dif_hmac_t *hmac, const char *data,
                                 size_t len) {
  const char *dp = data;
  size_t sent_bytes;

  while (dp - data < len) {
    dif_result_t res =
        dif_hmac_fifo_push(hmac, dp, len - (dp - data), &sent_bytes);
    CHECK(res == kDifOk || res == kDifIpFifoFull, "HMAC error = %d", res);

    // Wait until the FIFO is drained before pushing more data. This helps
    // to prevent the undesirable back pressure condition.
    if (res == kDifIpFifoFull) {
      hmac_testutils_fifo_empty_polled(hmac);
    }

    dp += sent_bytes;
  }
}
