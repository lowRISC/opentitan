// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/runtime/check.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

static dif_hmac_t hmac0;

static const size_t kDataLen = 142;
static const char kData[142] =
    "Every one suspects himself of at least one of "
    "the cardinal virtues, and this is mine: I am "
    "one of the few honest people that I have ever "
    "known";

static const uint32_t kExpectedDigest[8] = {0xdc96c23d, 0xaf36e268, 0xcb68ff71,
                                            0xe92f76e2, 0xb8a8379d, 0x426dc745,
                                            0x19f5cff7, 0x4ec9c6d6};

const test_config_t kTestConfig;

/**
 * Computes the SHA256 of the given data.
 */
static void compute_sha256(const dif_hmac_t *hmac, const void *data, size_t len,
                           dif_hmac_digest_t *digest) {
  CHECK(dif_hmac_mode_sha256_start(hmac) == kDifHmacOk);
  const char *data8 = (const char *)data;
  size_t data_left = len;
  while (data_left > 0) {
    size_t bytes_sent;
    dif_hmac_fifo_result_t result =
        dif_hmac_fifo_push(hmac, data8, data_left, &bytes_sent);
    if (result == kDifHmacFifoOk) {
      break;
    }
    CHECK(result == kDifHmacFifoFull, "Error while pushing to FIFO.");
    data8 += bytes_sent;
    data_left -= bytes_sent;
  }

  CHECK(dif_hmac_process(hmac) == kDifHmacOk);
  dif_hmac_digest_result_t digest_result = kDifHmacDigestProcessing;
  while (digest_result == kDifHmacDigestProcessing) {
    digest_result = dif_hmac_digest_read(hmac, digest);
  }
  CHECK(digest_result == kDifHmacDigestOk, "Error reading the digest.");
}

const test_config_t kTestConfig = {};

bool test_main(void) {
  dif_hmac_config_t config = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR),
      .message_endianness = kDifHmacEndiannessBig,
      .digest_endianness = kDifHmacEndiannessBig,
  };
  CHECK(dif_hmac_init(&config, &hmac0) == kDifHmacOk);

  dif_hmac_digest_t digest;
  compute_sha256(&hmac0, kData, kDataLen, &digest);

  for (uint32_t i = 0; i < 8; ++i) {
    uint32_t got = digest.digest[i];
    uint32_t want = kExpectedDigest[i];
    if (got != want) {
      LOG_ERROR("Digest mismatch at index %d: wanted 0x%x, got 0x%x.", i, want,
                got);
      // TODO: Document why this is called, or delete it.
      flash_write_scratch_reg(got);
      return false;
    }
  }

  return true;
}
