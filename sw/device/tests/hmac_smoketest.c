// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MAX_FIFO_FILL 10

const test_config_t kTestConfig;

// This test needs to understand the byte order of the data in the string and
// the digest values below, as they are laid out for the current processor.
// RISC-V is little-endian, so the first of these `kHmacTransactionConfig`
// values is the one we expect to be used, but we include the other for
// completeness.
static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

static const dif_hmac_transaction_t kHmacTransactionConfig = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessLittle,
};

static const char kData[142] =
    "Every one suspects himself of at least one of "
    "the cardinal virtues, and this is mine: I am "
    "one of the few honest people that I have ever "
    "known";

static uint32_t kHmacKey[8] = {0x243f6a88, 0x85a308d3, 0x13198a2e, 0x03707344,
                               0xa4093822, 0x299f31d0, 0x082efa98, 0xec4e6c89};

static const uint32_t kExpectedShaDigest[8] = {
    0xdc96c23d, 0xaf36e268, 0xcb68ff71, 0xe92f76e2,
    0xb8a8379d, 0x426dc745, 0x19f5cff7, 0x4ec9c6d6};

static const uint32_t kExpectedHmacDigest[8] = {
    0xe4987b39, 0x3f83d390, 0xc2f3bbaf, 0x3195dbfa,
    0x23fb480c, 0xb012ae5e, 0xf1394d28, 0x1940ceeb};

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
 * Load a message into the HMAC engine. This function may block if the FIFO
 * fills up.
 */
static void push_message(const dif_hmac_t *hmac, const char *data, size_t len) {
  int fifo_fill_count = 0;
  const char *dp = data;
  size_t sent_bytes;

  while (dp - data < len) {
    dif_result_t res =
        dif_hmac_fifo_push(hmac, dp, len - (dp - data), &sent_bytes);

    CHECK(res != kDifBadArg,
          "Invalid arguments encountered while pushing to FIFO.");

    if (res == kDifIpFifoFull) {
      ++fifo_fill_count;
    } else {
      CHECK(res != kDifBadArg,
            "Invalid arguments encountered while pushing to FIFO.");
      CHECK(res == kDifOk, "Unknown error encountered while pushing to FIFO.");
    }

    CHECK(fifo_fill_count <= MAX_FIFO_FILL,
          "FIFO filled up too may times, giving up.");

    dp += sent_bytes;
  }
}

/** Spin while the HMAC FIFO still has entries in it. Once the FIFO is empty we
 * can check the message length. Return `true` if there are no errors.
 */
static void wait_for_fifo_empty(const dif_hmac_t *hmac) {
  uint32_t fifo_depth;
  do {
    CHECK_DIF_OK(dif_hmac_fifo_count_entries(hmac, &fifo_depth));
  } while (fifo_depth > 0);
}

/**
 * Read and compare the length of the message in the HMAC engine to the length
 * of the message sent in bits.
 */
static void check_message_length(const dif_hmac_t *hmac,
                                 uint64_t expected_sent_bits) {
  uint64_t sent_bits;
  CHECK_DIF_OK(dif_hmac_get_message_length(hmac, &sent_bits));

  // TODO: Support 64-bit integers in logging.
  CHECK(expected_sent_bits == sent_bits,
        "Message length mismatch. Expected %u bits but got %u bits.",
        (uint32_t)expected_sent_bits, (uint32_t)sent_bits);
}

/**
 * Kick off the HMAC (or SHA256) run.
 */
static void run_hmac(const dif_hmac_t *hmac) {
  CHECK_DIF_OK(dif_hmac_process(hmac));
}

/**
 * Read the HMAC digest and compare it to the expected result.
 */
static void check_digest(const dif_hmac_t *hmac,
                         const uint32_t *expected_digest) {
  dif_hmac_digest_t digest_result;
  bool hmac_done = false;
  do {
    dif_result_t res = dif_hmac_finish(hmac, &digest_result);

    CHECK(res != kDifBadArg,
          "Invalid arguments encountered reading HMAC digest.");

    hmac_done = (res != kDifIpBusy);

    if (hmac_done) {
      CHECK(res == kDifOk, "Unknown error encountered reading HMAC digest.");
    }
  } while (!hmac_done);

  for (int i = 0; i < 8; ++i) {
    CHECK(expected_digest[i] == digest_result.digest[i],
          "Digest mismatch, expected: 0x%X at index [%i] but got: 0x%X.",
          expected_digest[i], i, digest_result.digest[i]);
  }
}

static void run_test(const dif_hmac_t *hmac, const char *data, size_t len,
                     const uint8_t *key, const uint32_t *expected_digest) {
  test_start(hmac, key);
  push_message(hmac, data, len);
  wait_for_fifo_empty(hmac);
  check_message_length(hmac, len * 8);
  run_hmac(hmac);
  check_digest(hmac, expected_digest);
}

bool test_main() {
  LOG_INFO("Running HMAC DIF test...");

  dif_hmac_t hmac;
  test_setup(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac);

  LOG_INFO("Running test SHA256 pass 1...");
  run_test(&hmac, kData, sizeof(kData), NULL, kExpectedShaDigest);

  LOG_INFO("Running test SHA256 pass 2...");
  run_test(&hmac, kData, sizeof(kData), NULL, kExpectedShaDigest);

  LOG_INFO("Running test HMAC pass 1...");
  run_test(&hmac, kData, sizeof(kData), (uint8_t *)(&kHmacKey[0]),
           kExpectedHmacDigest);

  LOG_INFO("Running test HMAC pass 2...");
  run_test(&hmac, kData, sizeof(kData), (uint8_t *)(&kHmacKey[0]),
           kExpectedHmacDigest);

  return true;
}
