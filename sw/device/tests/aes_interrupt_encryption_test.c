// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kTestTimeout = (1000 * 1000),
};

// The mask share, used to mask kKey. Note that the masking should not be done
// manually. Software is expected to get the key in two shares right from the
// beginning.

static const unsigned char kAesModesPlainTextBlock12[32] = {
    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e,
    0x11, 0x73, 0x93, 0x17, 0x2a, 0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03,
    0xac, 0x9c, 0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51,
};

static const unsigned char kAesModesPlainTextBlock34[32] = {
    0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11, 0xe5, 0xfb, 0xc1,
    0x19, 0x1a, 0x0a, 0x52, 0xef, 0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f,
    0x9b, 0x17, 0xad, 0x2b, 0x41, 0x7b, 0xe6, 0x6c, 0x37, 0x10};

static const uint8_t kKeyShare1[] = {
    0x0f, 0x1f, 0x2f, 0x3f, 0x4f, 0x5f, 0x6f, 0x7f, 0x8f, 0x9f, 0xaf,
    0xbf, 0xcf, 0xdf, 0xef, 0xff, 0x0a, 0x1a, 0x2a, 0x3a, 0x4a, 0x5a,
    0x6a, 0x7a, 0x8a, 0x9a, 0xaa, 0xba, 0xca, 0xda, 0xea, 0xfa,
};

OTTF_DEFINE_TEST_CONFIG();

status_t execute_test(void) {
  // Initialise AES.
  dif_aes_t aes;
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  // Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.

  uint8_t key_share0[sizeof(kAesModesKey128)];
  for (int i = 0; i < sizeof(kAesModesKey128); ++i) {
    key_share0[i] = kAesModesKey128[i] ^ kKeyShare1[i];
  }

  // "Convert" key share byte arrays to `dif_aes_key_share_t`.
  dif_aes_key_share_t key;
  memcpy(key.share0, key_share0, sizeof(key.share0));
  memcpy(key.share1, kKeyShare1, sizeof(key.share1));

  dif_aes_iv_t iv;
  memcpy(iv.iv, kAesModesIvCbc, sizeof(iv.iv));

  // Write the initial key share, IV and data in CSRs (known combinations).

  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeCbc,
      .key_len = kDifAesKey128,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, &iv));

  // "Convert" plain data byte arrays to `dif_aes_data_t` array.
  enum {
    kAesNumBlocks = 2,
  };

  dif_aes_data_t plain_text[kAesNumBlocks];
  dif_aes_data_t cipher_text[kAesNumBlocks];

  memcpy(plain_text[0].data, kAesModesPlainTextBlock12,
         sizeof(kAesModesPlainTextBlock12));

  // Encrypt kAesNumBlocks blocks.

  CHECK_DIF_OK(dif_aes_process_data(&aes, plain_text, cipher_text,
                                    (size_t)kAesNumBlocks));

  CHECK_DIF_OK(dif_aes_load_data(&aes, plain_text[0]));

  LOG_INFO("Started AES Encrypt with load function");

  dif_aes_iv_t iv_encrypt1;
  CHECK_DIF_OK(dif_aes_read_iv(&aes, &iv_encrypt1));

  bool ready = false;

  do {
    CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusOutputValid, &ready));
  } while (!ready);

  // Disable the AES unit to no longer automatically start encryption/decryption

  transaction.manual_operation = kDifAesManualOperationManual;

  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerDataOutClear));
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerKeyIvDataInClear));

  LOG_INFO("De-initialized Automatic operation");

  //  Perform an trial encryption using a different data and key. Message size,
  //  key size and mode can be chosen arbitrarily.

  dif_aes_t aes2;

  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes2));

  CHECK_DIF_OK(dif_aes_reset(&aes2));

  // Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.

  uint8_t key_share0_t[sizeof(kAesModesKey256)];
  for (int i = 0; i < sizeof(kAesModesKey256); ++i) {
    key_share0_t[i] = kAesModesKey256[i] ^ kKeyShare1[i];
  }

  // "Convert" key share byte arrays to `dif_aes_key_share_t`.
  dif_aes_key_share_t key_t;
  memcpy(key_t.share0, key_share0, sizeof(key_t.share0));
  memcpy(key_t.share1, kKeyShare1, sizeof(key_t.share1));

  dif_aes_iv_t iv2;
  memcpy(iv2.iv, kAesModesIvCtr, sizeof(iv2.iv));

  dif_aes_transaction_t transaction_trial = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeCtr,
      .key_len = kDifAesKey256,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  CHECK_DIF_OK(dif_aes_start(&aes2, &transaction_trial, &key_t, &iv2));

  // "Convert" plain data byte arrays to `dif_aes_data_t` array.
  enum {
    kAesNumBlocks_t2 = 4,
  };

  dif_aes_data_t plain_text2[kAesNumBlocks_t2];
  dif_aes_data_t cipher_text2[kAesNumBlocks_t2];
  memcpy(plain_text2[0].data, kAesModesPlainText, sizeof(kAesModesPlainText));

  CHECK_DIF_OK(dif_aes_process_data(&aes2, plain_text2, cipher_text2,
                                    (size_t)kAesNumBlocks_t2));

  CHECK_DIF_OK(dif_aes_load_data(&aes2, plain_text2[0]));
  LOG_INFO("Started AES trial Encrypt");
  CHECK_DIF_OK(dif_aes_end(&aes2));

  // Not checking successful encryption here since its a trial transaction
  //  Trial encryption ends here
  //  Resume the Original Encryption below

  // Using the iv read from `iv_encrypt1` for resuming the encryption of
  // remaining 2 blocks.
  memcpy(iv.iv, &iv_encrypt1, sizeof(iv.iv));
  transaction.manual_operation = kDifAesManualOperationAuto;

  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, &iv));

  memcpy(plain_text[0].data, kAesModesPlainTextBlock34,
         sizeof(kAesModesPlainTextBlock34));

  CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusInputReady, &ready));
  LOG_INFO("Resuming Encrypt with the remaining 2 blocks of data");

  CHECK_DIF_OK(dif_aes_process_data(&aes, plain_text, cipher_text,
                                    (size_t)kAesNumBlocks));
  CHECK_DIF_OK(dif_aes_load_data(&aes, plain_text[0]));

  do {
    CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusOutputValid, &ready));
  } while (!ready);

  // Decrypt operation below

  dif_aes_transaction_t transactiond = {
      .operation = kDifAesOperationDecrypt,
      .mode = kDifAesModeCbc,
      .key_len = kDifAesKey128,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  for (int i = 0; i < sizeof(kAesModesKey128); ++i) {
    key_share0[i] = kAesModesKey128[i] ^ kKeyShare1[i];
  }

  // "Convert" key share byte arrays to `dif_aes_key_share_t`.

  memcpy(key.share0, key_share0, sizeof(key.share0));
  memcpy(key.share1, kKeyShare1, sizeof(key.share1));

  memcpy(iv.iv, kAesModesIvCbc, sizeof(iv.iv));

  do {
    CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusInputReady, &ready));
  } while (!ready);

  CHECK_DIF_OK(dif_aes_start(&aes, &transactiond, &key, &iv));

  memcpy(cipher_text[0].data, kAesModesCipherTextCbc128,
         sizeof(cipher_text[0].data));

  CHECK_DIF_OK(dif_aes_load_data(&aes, cipher_text[0]));

  do {
    CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusOutputValid, &ready));
  } while (!ready);

  dif_aes_data_t out_data2;
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data2));
  CHECK_DIF_OK(dif_aes_end(&aes));
  // Finish the CBC decryption transaction.

  CHECK_ARRAYS_EQ((uint8_t *)out_data2.data, kAesModesPlainText,
                  sizeof(out_data2.data));
  LOG_INFO("Decryption Successful");

  return OK_STATUS();
}

bool test_main(void) {
  LOG_INFO("Entering AES Interrupt Encrypt Tests");

  return status_ok(execute_test());
}
