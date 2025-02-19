// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hmac_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/dif/autogen/dif_hmac_autogen.h"

OTTF_DEFINE_TEST_CONFIG();

static const dif_hmac_transaction_t kHmacconfig_littled_littlem = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessLittle,
};

static const dif_hmac_transaction_t kHmacconfig_littled_bigm = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessBig,
};

static const dif_hmac_transaction_t kHmacconfig_bigd_littlem = {
    .digest_endianness = kDifHmacEndiannessBig,
    .message_endianness = kDifHmacEndiannessLittle,
};

static const dif_hmac_transaction_t kHmacconfig_bigd_bigm = {
    .digest_endianness = kDifHmacEndiannessBig,
    .message_endianness = kDifHmacEndiannessBig,
};

static const char kData[142] =
    "Every one suspects himself of at least one of "
    "the cardinal virtues, and this is mine: I am "
    "one of the few honest people that I have ever "
    "known";

static const char kData2[8] = "Help Us ";
static const char kData2_endian[8] = "pleH sU ";

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

static const dif_hmac_digest_t kExpectedShaDigest_bigendian = {
    .digest =
        {
            0x4ec9c6d6,
            0x19f5cff7,
            0x426dc745,
            0xb8a8379d,
            0xe92f76e2,
            0xcb68ff71,
            0xaf36e268,
            0xdc96c23d,
        },
};

static const dif_hmac_digest_t kExpectedShaDigest_shortmessage = {
    .digest =
        {
            0x8ce72131,
            0xd5ac567a,
            0x234045e8,
            0x04f2ac21,
            0x29e62b92,
            0x99255af0,
            0x392a3664,
            0x31066f19,
        },
};

static const dif_hmac_digest_t kExpectedShaDigest_shortmessage_bigendian = {
    .digest =
        {
            0x3121e78c,
            0x7a56acd5,
            0xe8454023,
            0x21acf204,
            0x922be629,
            0xf05a2599,
            0x64362a39,
            0x196f0631,
        },
};

/**
 * Initialize the HMAC engine. Return `true` if the configuration is valid.
 */
static void test_setup(mmio_region_t base_addr, dif_hmac_t *hmac) {
  CHECK_DIF_OK(dif_hmac_init(base_addr, hmac));
}

static void run_test_endianness(const dif_hmac_t *hmac, const char *data,
                                size_t len, const dif_hmac_transaction_t config,
                                const dif_hmac_digest_t *expected_digest) {
  CHECK_DIF_OK(dif_hmac_mode_sha256_start(hmac, config));
  CHECK_STATUS_OK(hmac_testutils_push_message(hmac, data, len));
  CHECK_STATUS_OK(hmac_testutils_fifo_empty_polled(hmac));
  CHECK_STATUS_OK(hmac_testutils_check_message_length(hmac, len * 8));
  CHECK_DIF_OK(dif_hmac_process(hmac));
  CHECK_STATUS_OK(
      hmac_testutils_finish_and_check_polled(hmac, expected_digest));
}

bool test_main(void) {
  LOG_INFO("Running HMAC DIF test...");
  dif_hmac_t hmac;
  test_setup(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac);

  LOG_INFO(
      "Running test SHA256 pass little-endian digest and little-endian "
      "message...");
  run_test_endianness(&hmac, kData, sizeof(kData), kHmacconfig_littled_littlem,
                      &kExpectedShaDigest);

  LOG_INFO(
      "Running test SHA256 with big-endian digest,little-endian message "
      "config...");
  run_test_endianness(&hmac, kData, sizeof(kData), kHmacconfig_bigd_littlem,
                      &kExpectedShaDigest_bigendian);

  LOG_INFO(
      "Running test SHA256 pass with big-endian digest,big endian message "
      "config... ");
  run_test_endianness(&hmac, kData2, sizeof(kData2), kHmacconfig_bigd_bigm,
                      &kExpectedShaDigest_shortmessage_bigendian);

  LOG_INFO(
      "Running test SHA256 pass little-endian digest, big endian message "
      "config... ");
  run_test_endianness(&hmac, kData2, sizeof(kData2), kHmacconfig_littled_bigm,
                      &kExpectedShaDigest_shortmessage);

  LOG_INFO(
      "Running test SHA256 pass big-endian digest, little endian message "
      "config \n"
      " with input message byte-swapped to verify the in-built byteswap "
      "function..");
  run_test_endianness(&hmac, kData2_endian, sizeof(kData2_endian),
                      kHmacconfig_bigd_littlem,
                      &kExpectedShaDigest_shortmessage_bigendian);

  return true;
}
