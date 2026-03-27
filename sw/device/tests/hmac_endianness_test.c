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

enum {
  kKeyswapSetBigendian = 0,
  kKeyswapSetLittleendian = 1,
};

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

static uint32_t kHmacKey[8] = {
    0xec4e6c89, 0x082efa98, 0x299f31d0, 0xa4093822,
    0x03707344, 0x13198a2e, 0x85a308d3, 0x243f6a88,
};

static uint32_t kHmacKey_swapped[8] = {
    0x896c4eec, 0x98fa2e08, 0xd0319f29, 0x223809a4,
    0x44737003, 0x2e8a1913, 0xd308a385, 0x886a3f24,
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
static const dif_hmac_digest_t kExpectedHmacDigest_bigendian = {
    .digest =
        {
            0x1940ceeb,
            0xf1394d28,
            0xb012ae5e,
            0x23fb480c,
            0x3195dbfa,
            0xc2f3bbaf,
            0x3f83d390,
            0xe4987b39,
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

static void run_test_hmacmode_endianness(
    const dif_hmac_t *hmac, const char *data, size_t len, const uint8_t *key,
    bool KEY_SWAP_BIT_VAL, dif_hmac_transaction_t config,
    const dif_hmac_digest_t *expected_digest) {
  uint32_t cfg_reg =
      abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET);
  cfg_reg =
      bitfield_bit32_write(cfg_reg, HMAC_CFG_KEY_SWAP_BIT, KEY_SWAP_BIT_VAL);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, cfg_reg);
  CHECK_DIF_OK(dif_hmac_mode_hmac_start(hmac, key, config));
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

  LOG_INFO(
      "Running test HMAC pass little-endian digest and little-endian "
      "message with key_swap set to 0...");
  run_test_hmacmode_endianness(
      &hmac, kData, sizeof(kData), (uint8_t *)(&kHmacKey[0]),
      kKeyswapSetBigendian, kHmacconfig_littled_littlem, &kExpectedHmacDigest);

  LOG_INFO(
      "Running test HMAC pass little-endian digest and little-endian "
      "message with key_swap set to 1 and with key swapped..");
  run_test_hmacmode_endianness(
      &hmac, kData, sizeof(kData), (uint8_t *)(&kHmacKey_swapped[0]),
      kKeyswapSetLittleendian, kHmacconfig_littled_littlem,
      &kExpectedHmacDigest);

  LOG_INFO(
      "Running test HMAC pass big-endian digest and little-endian "
      "message with key_swap set to 0...");
  run_test_hmacmode_endianness(&hmac, kData, sizeof(kData),
                               (uint8_t *)(&kHmacKey[0]), kKeyswapSetBigendian,
                               kHmacconfig_bigd_littlem,
                               &kExpectedHmacDigest_bigendian);
  return true;
}
