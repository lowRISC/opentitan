// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static const char kData[142] =
    "Every one suspects himself of at least one of "
    "the cardinal virtues, and this is mine: I am "
    "one of the few honest people that I have ever "
    "known";

static uint32_t kHmacKey[8] = {
    0xec4e6c89, 0x082efa98, 0x299f31d0, 0xa4093822,
    0x03707344, 0x13198a2e, 0x85a308d3, 0x243f6a88,
};

static const dif_hmac_digest_t kExpectedHmacDigest = {
    .digest =
        {
            0xebce4019,
            0x284d39f1,
            0x5eae12b0,
            0x0c48fb23,
            0xfadb9531,
            0xafbbf3c2,
            0x90d3833f,
            0x397b98e4,
        },
};

// Polls for HMAC to finish and returns the digest.
status_t hmac_finish_polled(const dif_hmac_t *hmac,
                            dif_hmac_digest_t *digest_out) {
  uint32_t usec;
  TRY(compute_hmac_testutils_finish_timeout_usec(&usec));
  IBEX_TRY_SPIN_FOR(
      dif_hmac_finish(hmac, /*disable_after_done=*/false, digest_out) == kDifOk,
      usec);
  return OK_STATUS();
}

// Processes a message and checks the HMAC FIFO.
static void hmac_process_message(const dif_hmac_t *hmac, const char *data,
                                 size_t len) {
  CHECK_STATUS_OK(hmac_testutils_push_message(hmac, data, len));
  CHECK_STATUS_OK(hmac_testutils_fifo_empty_polled(hmac));
  CHECK_STATUS_OK(hmac_testutils_check_message_length(hmac, len * 8));
  CHECK_DIF_OK(dif_hmac_process(hmac));
}

bool test_main(void) {
  dif_hmac_t hmac;
  CHECK_DIF_OK(
      dif_hmac_init(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac));

  static const dif_hmac_transaction_t kHmacTransactionConfig = {
      .digest_endianness = kDifHmacEndiannessLittle,
      .message_endianness = kDifHmacEndiannessLittle,
  };

  CHECK_DIF_OK(dif_hmac_mode_hmac_start(&hmac, (uint8_t *)(&kHmacKey[0]),
                                        kHmacTransactionConfig));
  hmac_process_message(&hmac, kData, sizeof(kData));

  dif_hmac_digest_t digest;
  CHECK_STATUS_OK(hmac_finish_polled(&hmac, &digest));
  CHECK_ARRAYS_EQ(digest.digest, kExpectedHmacDigest.digest,
                  ARRAYSIZE(digest.digest));

  // The digest should not longer match after secure wipe.
  const uint32_t kSecureWipeValue = UINT32_MAX;
  CHECK_DIF_OK(dif_hmac_wipe_secret(&hmac, kSecureWipeValue, &digest));

  // Secure wipe is kSecureWipeValue overwritten to the digest words.
  for (size_t i = 0; i < ARRAYSIZE(digest.digest); ++i) {
    uint32_t expected_value = kSecureWipeValue;
    CHECK(digest.digest[i] == expected_value,
          "Expected digest[%d] = %x, actual = %x", i, expected_value,
          digest.digest[i]);
  }

  // HMAC should no longer have the key configured after secure wipe.
  CHECK_DIF_OK(
      dif_hmac_mode_hmac_start(&hmac, /*key=*/NULL, kHmacTransactionConfig));
  hmac_process_message(&hmac, kData, sizeof(kData));
  CHECK_STATUS_OK(hmac_testutils_finish_polled(&hmac, &digest));
  CHECK_ARRAYS_NE(digest.digest, kExpectedHmacDigest.digest,
                  ARRAYSIZE(digest.digest));
  return true;
}
