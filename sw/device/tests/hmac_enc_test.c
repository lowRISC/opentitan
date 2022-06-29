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

bool test_main(void) {
  dif_hmac_t hmac;
  mmio_region_t base_addr = mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_hmac_init(base_addr, &hmac));

  // Use HMAC in SHA256 mode to generate a 256bit key from `kRefHmacLongKey`.
  CHECK_DIF_OK(dif_hmac_mode_sha256_start(&hmac, kHmacTransactionConfig));
  hmac_testutils_push_message(&hmac, (char *)kRefHmacLongKey,
                              sizeof(kRefHmacLongKey));
  hmac_testutils_check_message_length(&hmac, sizeof(kRefHmacLongKey) * 8);
  CHECK_DIF_OK(dif_hmac_process(&hmac));
  dif_hmac_digest_t key_digest;
  hmac_testutils_finish_polled(&hmac, &key_digest);
  CHECK_ARRAYS_EQ(key_digest.digest, kRefExpectedShaDigest.digest,
                  ARRAYSIZE(key_digest.digest));

  // Generate HMAC final digest, using the resulted SHA256 digest over the
  // `kRefHmacLongKey`.
  CHECK_DIF_OK(dif_hmac_mode_hmac_start(&hmac, (uint8_t *)&key_digest.digest[0],
                                        kHmacTransactionConfig));
  hmac_testutils_push_message(&hmac, kRefData, sizeof(kRefData));
  hmac_testutils_check_message_length(&hmac, sizeof(kRefData) * 8);
  CHECK_DIF_OK(dif_hmac_process(&hmac));
  hmac_testutils_finish_and_check_polled(&hmac, &kRefExpectedHmacDigest);

  return true;
}
