// Copyright lowRISC contributors.
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

static const dif_hmac_transaction_t kHmacTransactionConfig = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessLittle,
};

/**
 * https://csrc.nist.gov/CSRC/media/Projects/
 * Cryptographic-Standards-and-Guidelines/documents/examples/HMAC_SHA256.pdf
 *
 * Key Length: 100
 * Tag length: 32
 *
 * When key is > than the block size, it should be hashed to obtain the block
 * sized key. Please refer to:
 * https://csrc.nist.gov/csrc/media/publications/fips/198/archive/
 * 2002-03-06/documents/fips-198a.pdf
 *
 * Specifically chapter 3 and 5 (Table 1).
 */

static const char kData[34] = "Sample message for keylen=blocklen";

static uint8_t kHmacLongKey[100] = {
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
static const dif_hmac_digest_t kExpectedShaDigest = {
    .digest =
        {
            0xBCE0AFF1,
            0x9CF5AA6A,
            0x7469A30D,
            0x61D04E43,
            0x76E4BBF6,
            0x381052EE,
            0x9E7F3392,
            0x5C954D52,
        },
};

/**
 * Big endian representation of the final HMAC mode digest.
 */
static const dif_hmac_digest_t kExpectedHmacDigest = {
    .digest =
        {
            0xBDCCB6C7,
            0x2DDEADB5,
            0x00AE7683,
            0x86CB38CC,
            0x41C63DBB,
            0x0878DDB9,
            0xC7A38A43,
            0x1B78378D,
        },
};

bool test_main(void) {
  dif_hmac_t hmac;
  mmio_region_t base_addr = mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_hmac_init(base_addr, &hmac));

  // Use HMAC in SHA256 mode to generate a 256bit key from `kHmacLongKey`.
  CHECK_DIF_OK(dif_hmac_mode_sha256_start(&hmac, kHmacTransactionConfig));
  hmac_testutils_push_message(&hmac, (char *)kHmacLongKey,
                              sizeof(kHmacLongKey));
  hmac_testutils_check_message_length(&hmac, sizeof(kHmacLongKey) * 8);
  CHECK_DIF_OK(dif_hmac_process(&hmac));
  dif_hmac_digest_t key_digest;
  hmac_testutils_finish_polled(&hmac, &key_digest);
  CHECK_ARRAYS_EQ(key_digest.digest, kExpectedShaDigest.digest,
                  ARRAYSIZE(key_digest.digest));

  // Generate HMAC final digest, using the resulted SHA256 digest over the
  // `kHmacLongKey`.
  CHECK_DIF_OK(dif_hmac_mode_hmac_start(&hmac, (uint8_t *)&key_digest.digest[0],
                                        kHmacTransactionConfig));
  hmac_testutils_push_message(&hmac, kData, sizeof(kData));
  hmac_testutils_check_message_length(&hmac, sizeof(kData) * 8);
  CHECK_DIF_OK(dif_hmac_process(&hmac));
  hmac_testutils_finish_and_check_polled(&hmac, &kExpectedHmacDigest);

  return true;
}
