// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// The following plaintext, key and ciphertext are extracted from Appendix C of
// the Advanced Encryption Standard (AES) FIPS Publication 197 available at
// https://www.nist.gov/publications/advanced-encryption-standard-aes

#define TIMEOUT (1000 * 1000)

static const uint32_t kPlainText[] = {
    0x33221100,
    0x77665544,
    0xbbaa9988,
    0xffeeddcc,
};

static const uint8_t kKey[] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
    0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,
    0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
};

static const uint32_t kCipherTextGold[] = {
    0x493350e6,
    0x4a0a5568,
    0x9d4d4aa1,
    0xd256e2e0,
};

static const uint32_t kIv[] = {
    0x01020304,
    0x0c0d0e0f,
    0x1718191a,
    0x1c1d1e1f,
};

// The mask share, used to mask kKey. Note that the masking should not be done
// manually. Software is expected to get the key in two shares right from the
// beginning.
static const uint8_t kKeyShare1[] = {
    0x0f, 0x1f, 0x2f, 0x3f, 0x4f, 0x5f, 0x6f, 0x7f, 0x8f, 0x9f, 0xaf,
    0xbf, 0xcf, 0xdf, 0xef, 0xff, 0x0a, 0x1a, 0x2a, 0x3a, 0x4a, 0x5a,
    0x6a, 0x7a, 0x8a, 0x9a, 0xaa, 0xba, 0xca, 0xda, 0xea, 0xfa,
};

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  dif_aes_t aes;

  // First of all, we need to get the entropy complex up and running.
  entropy_testutils_boot_mode_init();

  // Initialise AES.
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  // Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.
  uint8_t key_share0[ARRAYSIZE(kKey)];
  for (int i = 0; i < ARRAYSIZE(kKey); ++i) {
    key_share0[i] = kKey[i] ^ kKeyShare1[i];
  }

  // "Convert" key share byte arrays to `dif_aes_key_share_t`.
  dif_aes_key_share_t key;
  memcpy(key.share0, key_share0, ARRAYSIZE(kKey));
  memcpy(key.share1, kKeyShare1, ARRAYSIZE(kKey));

  // "Convert" iv byte arrays to `dif_aes_iv_t`.
  dif_aes_iv_t iv;
  memcpy(iv.iv, kIv, ARRAYSIZE(kIv));

  // Setup CBC encryption transaction.
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeCbc,
      .key_len = kDifAesKey256,
      .manual_operation = kDifAesManualOperationManual,
  };

  // Write the initial key share, IV and data in CSRs (known combinations).
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, &iv));
  dif_aes_data_t in_data_plain;
  memcpy(in_data_plain.data, kPlainText, ARRAYSIZE(kPlainText));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true, TIMEOUT);
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  // Write the PRNG_RESEED bit to reseed the internal state of the PRNG.
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerPrngReseed));

  // Trigger the AES operation to run and wait for it to complete.
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true, TIMEOUT);

  // Check the ciphertext against the expected value.
  dif_aes_data_t out_data;
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data));
  CHECK_ARRAYS_EQ(out_data.data, kCipherTextGold, ARRAYSIZE(kCipherTextGold));

  // Write the KEY_IV_DATA_IN_CLEAR and DATA_OUT_CLEAR trigger bits to 1 and
  // wait for it to complete by polling the status idle bit.
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerDataOutClear));
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerKeyIvDataInClear));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, TIMEOUT);

  // Read back the data out CSRs - they should all read garbage values.
  CHECK(dif_aes_read_output(&aes, &out_data) == kDifError);
  CHECK(!aes_testutils_get_status(&aes, kDifAesStatusOutputValid));

  // Assertion check verifies that the internal states (data_in, key share and
  // IV are also garbage, i.e. different from the originally written values.
  CHECK_DIF_OK(dif_aes_read_iv(&aes, &iv));
  CHECK_ARRAYS_NE(iv.iv, kIv, ARRAYSIZE(kIv));

  CHECK_DIF_OK(dif_aes_end(&aes));
  return true;
}
