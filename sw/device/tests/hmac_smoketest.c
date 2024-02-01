// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static const dif_hmac_transaction_t kHmacTransactionConfig = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessLittle,
};

static const char kData[142] =
    "Every one suspects himself of at least one of "
    "the cardinal virtues, and this is mine: I am "
    "one of the few honest people that I have ever "
    "known";

static uint32_t kHmacKey[8] = {
    0xec4e6c89, 0x082efa98, 0x299f31d0, 0xa4093822,
    0x03707344, 0x13198a2e, 0x85a308d3, 0x243f6a88,
};

static const dif_hmac_digest_t kExpectedShaDigest = {
    .digest =
        {
            0xd6c6c94e,
            0xf7cff519,
            0x45c76d42,
            0x9d37a8b8,
            0xe2762fe9,
            0x71ff68cb,
            0x68e236af,
            0x3dc296dc,
        },
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

/**
 * Initialize the HMAC engine. Return `true` if the configuration is valid.
 */
static void test_setup(mmio_region_t base_addr, dif_hmac_t *hmac) {
  CHECK_DIF_OK(dif_hmac_init(base_addr, hmac));
}

/**
 * Start HMAC in the correct mode. If `key` == NULL use SHA256 mode, otherwise
 * use the provided key in HMAC mode.
 */
static void test_start(const dif_hmac_t *hmac, const uint8_t *key) {
  // Let a null key indicate we are operating in SHA256-only mode.
  if (key == NULL) {
    CHECK_DIF_OK(dif_hmac_mode_sha256_start(hmac, kHmacTransactionConfig));
  } else {
    CHECK_DIF_OK(dif_hmac_mode_hmac_start(hmac, key, kHmacTransactionConfig));
  }
}

/**
 * Kick off the HMAC (or SHA256) run.
 */
static void run_hmac(const dif_hmac_t *hmac) {
  CHECK_DIF_OK(dif_hmac_process(hmac));
}

static void run_test(const dif_hmac_t *hmac, const char *data, size_t len,
                     const uint8_t *key,
                     const dif_hmac_digest_t *expected_digest) {
  test_start(hmac, key);
  CHECK_STATUS_OK(hmac_testutils_push_message(hmac, data, len));
  CHECK_STATUS_OK(hmac_testutils_fifo_empty_polled(hmac));
  CHECK_STATUS_OK(hmac_testutils_check_message_length(hmac, len * 8));
  run_hmac(hmac);
  CHECK_STATUS_OK(
      hmac_testutils_finish_and_check_polled(hmac, expected_digest));
}

bool test_main(void) {
  LOG_INFO("Running HMAC DIF test...");

  dif_hmac_t hmac;
  test_setup(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac);

  LOG_INFO("Running test SHA256 pass 1...");
  run_test(&hmac, kData, sizeof(kData), NULL, &kExpectedShaDigest);

  LOG_INFO("Running test SHA256 pass 2...");
  run_test(&hmac, kData, sizeof(kData), NULL, &kExpectedShaDigest);

  LOG_INFO("Running test HMAC pass 1...");
  run_test(&hmac, kData, sizeof(kData), (uint8_t *)(&kHmacKey[0]),
           &kExpectedHmacDigest);

  LOG_INFO("Running test HMAC pass 2...");
  run_test(&hmac, kData, sizeof(kData), (uint8_t *)(&kHmacKey[0]),
           &kExpectedHmacDigest);

  return true;
}
