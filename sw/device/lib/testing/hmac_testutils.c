// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/hmac_testutils.h"

#include <stdbool.h>

#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/test_framework/check.h"

const char kHmacRefData[34] = "Sample message for keylen=blocklen";

const uint8_t kHmacRefLongKey[100] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B,
    0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20, 0x21, 0x22, 0x23,
    0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F,
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3A, 0x3B,
    0x3C, 0x3D, 0x3E, 0x3F, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
    0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51, 0x52, 0x53,
    0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F,
    0x60, 0x61, 0x62, 0x63};

/**
 * Big endian representation of the hashed "long" key, which is used as the
 * input key into the HMAC mode digest generation.
 */
const dif_hmac_digest_t kHmacRefExpectedLongKeyDigest = {
    .digest =
        {
            0x5C954D52,
            0x9E7F3392,
            0x381052EE,
            0x76E4BBF6,
            0x61D04E43,
            0x7469A30D,
            0x9CF5AA6A,
            0xBCE0AFF1,
        },
};

/**
 * Big endian representation of the final HMAC mode digest.
 */
const dif_hmac_digest_t kHmacRefExpectedDigest = {
    .digest =
        {
            0x1B78378D,
            0xC7A38A43,
            0x0878DDB9,
            0x41C63DBB,
            0x86CB38CC,
            0x00AE7683,
            0x2DDEADB5,
            0xBDCCB6C7,
        },
};

status_t hmac_testutils_check_message_length(const dif_hmac_t *hmac,
                                             uint64_t expected_sent_bits) {
  uint64_t sent_bits;
  TRY(dif_hmac_get_message_length(hmac, &sent_bits));

  // 64bit formatting is not supported, so split into hi and lo hex 32bit
  // values. These should appear as 64bit hex values in the debug output.
  TRY_CHECK(expected_sent_bits == sent_bits,
            "Message length mismatch. "
            "Expected 0x%08x%08x bits but got 0x%08x%08x bits.",
            (uint32_t)(expected_sent_bits >> 32), (uint32_t)expected_sent_bits,
            (uint32_t)(sent_bits >> 32), (uint32_t)sent_bits);

  return OK_STATUS();
}

/**
 * Checks whether the HMAC FIFO is empty.
 */
static bool check_fifo_empty(const dif_hmac_t *hmac) {
  uint32_t fifo_depth;
  dif_result_t res = dif_hmac_fifo_count_entries(hmac, &fifo_depth);
  return res == kDifOk || fifo_depth == 0;
}

status_t hmac_testutils_fifo_empty_polled(const dif_hmac_t *hmac) {
  uint32_t usec;
  TRY(compute_hmac_testutils_fifo_empty_usec(&usec));
  IBEX_TRY_SPIN_FOR(check_fifo_empty(hmac), usec);
  return OK_STATUS();
}

status_t hmac_testutils_finish_polled(const dif_hmac_t *hmac,
                                      dif_hmac_digest_t *digest_out) {
  uint32_t usec;
  TRY(compute_hmac_testutils_finish_timeout_usec(&usec));
  IBEX_TRY_SPIN_FOR(dif_hmac_finish(hmac, digest_out) == kDifOk, usec);
  return OK_STATUS();
}

status_t hmac_testutils_finish_and_check_polled(
    const dif_hmac_t *hmac, const dif_hmac_digest_t *expected) {
  dif_hmac_digest_t digest;
  TRY(hmac_testutils_finish_polled(hmac, &digest));
  TRY_CHECK(memcmp(&digest.digest, &expected->digest, sizeof(digest.digest)) ==
            0);
  return OK_STATUS();
}

status_t hmac_testutils_push_message(const dif_hmac_t *hmac, const char *data,
                                     size_t len) {
  const char *dp = data;
  size_t sent_bytes;

  while (dp - data < len) {
    const size_t offset = (size_t)(dp - data);
    dif_result_t res = dif_hmac_fifo_push(hmac, dp, len - offset, &sent_bytes);
    TRY_CHECK(res == kDifOk || res == kDifIpFifoFull, "HMAC error = %d", res);

    // Wait until the FIFO is drained before pushing more data. This helps
    // to prevent the undesirable back pressure condition.
    if (res == kDifIpFifoFull) {
      TRY(hmac_testutils_fifo_empty_polled(hmac));
    }

    dp += sent_bytes;
  }
  return OK_STATUS();
}
