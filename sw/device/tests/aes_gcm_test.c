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

#include "hw/top/aes_regs.h"  // Generated.

enum {
  kTestTimeout = (1000 * 1000),
  kTestTimeoutMicros = 1000,  // 1ms
  kAesNumBlocks = 4,
  kAesNumAADBlocks = 2,
};

// AES GCM configuration used for this test.
static dif_aes_transaction_t transaction = {
    .operation = kDifAesOperationEncrypt,
    .mode = kDifAesModeGcm,
    .key_len = kDifAesKey128,
    .key_provider = kDifAesKeySoftwareProvided,
    .mask_reseeding = kDifAesReseedPerBlock,
    .manual_operation = kDifAesManualOperationAuto,
    .reseed_on_key_change = false,
    .ctrl_aux_lock = false,
};

OTTF_DEFINE_TEST_CONFIG();

status_t execute_test(bool save_and_restore_aad, bool save_and_restore_ptx) {
  // Initialise AES.
  dif_aes_t aes;
  dif_aes_data_t saved_gcm_state;
  dif_aes_iv_t saved_iv;
  TRY(dif_aes_init_from_dt(kDtAes, &aes));
  TRY(dif_aes_reset(&aes));

  // Prepare and load AES IV.
  dif_aes_iv_t aes_iv;
  memset(aes_iv.iv, 0, sizeof(aes_iv));
  memcpy(aes_iv.iv, kAesModesIvGcm, sizeof(kAesModesIvGcm));

  // Copy key share byte arrays to `dif_aes_key_share_t`.
  dif_aes_key_share_t key;
  memcpy(key.share0, kAesModesGcmKey128, sizeof(key.share0));
  memset(key.share1, 0, sizeof(key.share1));

  // Write the initial key share, IV and data in CSRs.
  TRY(dif_aes_start(&aes, &transaction, &key, &aes_iv));

  // Setup the AAD arrays.
  dif_aes_data_t aes_aad[kAesNumAADBlocks];
  // First 16-bytes AAD block.
  memcpy(aes_aad[0].data, &kAesModesAadGcm[0], 16);
  // Second 4-bytes AAD block.
  memset(aes_aad[1].data, 0, 16);
  memcpy(aes_aad[1].data, &kAesModesAadGcm[16], 4);

  // Load the first 16-bytes AAD block into the AES.
  TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_AAD,
                            16));
  TRY(dif_aes_load_data(&aes, aes_aad[0]));
  // When testing the save and restore feature, save the current state after the
  // first AAD is processed, reset the AES, restore the state, and proceed with
  // the operation.
  if (save_and_restore_aad) {
    LOG_INFO("Saving AES-GCM state after processing first AAD block...");
    TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_SAVE,
                              16));
    TRY(dif_aes_read_output(&aes, &saved_gcm_state));
    TRY(dif_aes_read_iv(&aes, &saved_iv));
    TRY(dif_aes_reset(&aes));
    LOG_INFO("Restoring AES-GCM state...");
    saved_iv.iv[3] = 0;  // Clear upper IV bits to restore the original IV.
    TRY(dif_aes_start(&aes, &transaction, &key, &saved_iv));
    AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                  kTestTimeoutMicros);
    TRY(dif_aes_set_gcm_phase(
        &aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_RESTORE, 16));
    TRY(dif_aes_load_data(&aes, saved_gcm_state));
  }
  // Load the second 4-bytes AAD block into the AES.
  TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_AAD,
                            4));
  TRY(dif_aes_load_data(&aes, aes_aad[1]));

  // "Convert" plain data byte arrays to `dif_aes_data_t` array.
  dif_aes_data_t plain_text[kAesNumBlocks];
  dif_aes_data_t cipher_text[kAesNumBlocks];
  memset(plain_text[0].data, 0, kAesNumBlocks * sizeof(plain_text[0].data));
  memcpy(plain_text[0].data, kAesModesPlainTextGcm,
         sizeof(kAesModesPlainTextGcm));

  // Process the plaintext blocks.
  // Block 0.
  size_t valid_bytes = sizeof(plain_text[0].data);
  TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_TEXT,
                            valid_bytes));
  TRY(dif_aes_load_data(&aes, plain_text[0]));
  TRY(dif_aes_read_output(&aes, &cipher_text[0]));
  if (save_and_restore_ptx) {
    LOG_INFO("Saving AES-GCM state after processing first PTX block...");
    TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_SAVE,
                              16));
    TRY(dif_aes_read_output(&aes, &saved_gcm_state));
    TRY(dif_aes_read_iv(&aes, &saved_iv));
    TRY(dif_aes_reset(&aes));
    LOG_INFO("Restoring AES-GCM state...");
    uint32_t iv_increment = saved_iv.iv[3];
    saved_iv.iv[3] = 0;  // Clear upper IV bits to restore the original IV.
    TRY(dif_aes_start(&aes, &transaction, &key, &saved_iv));
    AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                  kTestTimeoutMicros);
    TRY(dif_aes_set_gcm_phase(
        &aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_RESTORE, 16));
    // Restore the saved AES-GCM context.
    TRY(dif_aes_load_data(&aes, saved_gcm_state));
    // Restore the saved IV.
    saved_iv.iv[3] = iv_increment;
    TRY(dif_aes_load_iv(&aes, saved_iv));
    TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_TEXT,
                              16));
  }
  // Block 1.
  TRY(dif_aes_load_data(&aes, plain_text[1]));
  TRY(dif_aes_read_output(&aes, &cipher_text[1]));
  // Block 2.
  TRY(dif_aes_load_data(&aes, plain_text[2]));
  TRY(dif_aes_read_output(&aes, &cipher_text[2]));
  // Block 3.
  valid_bytes = valid_bytes -
                (valid_bytes * kAesNumBlocks - sizeof(kAesModesPlainTextGcm));
  TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_TEXT,
                            valid_bytes));
  TRY(dif_aes_load_data(&aes, plain_text[3]));
  TRY(dif_aes_read_output(&aes, &cipher_text[3]));

  // "Convert" `dif_aes_data_t` array to plain data byte arrays.
  unsigned char ctx[ARRAYSIZE(kAesModesCipherTextGcm128)];
  memcpy(ctx, cipher_text[0].data, sizeof(ctx));

  // Check whether we got the expected ciphertext.
  TRY_CHECK_ARRAYS_EQ(ctx, kAesModesCipherTextGcm128, sizeof(ctx));
  LOG_INFO("Encryption Successful");

  // Generate tag.
  uint64_t len_ptx = sizeof(kAesModesPlainTextGcm) * 8;
  uint64_t len_aad = sizeof(kAesModesAadGcm) * 8;

  TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_TAG,
                            16));
  TRY(dif_aes_load_gcm_tag_len(&aes, len_ptx, len_aad));

  // Read back tag, convert to plain data byte array, and compare to expected
  // tag.
  dif_aes_data_t tag;
  TRY(dif_aes_read_output(&aes, &tag));
  unsigned char tag_plain[sizeof(tag)];
  memcpy(tag_plain, tag.data, sizeof(tag_plain));

  TRY_CHECK_ARRAYS_EQ(tag_plain, kAesModesTagGcm128, sizeof(tag_plain));
  LOG_INFO("Tag Generation Successful");

  TRY(dif_aes_end(&aes));

  return OK_STATUS();
}

bool test_main(void) {
  LOG_INFO("Entering AES-GCM Test");
  status_t result = OK_STATUS();

  // First parameter after execute_test: save_and_restore_aad
  //                                     save GCM state and IV after processing
  //                                     AAD block 0 clear AES, restore, and
  //                                     continue with AAD block 1
  // Second parameter after execute_test: save_and_restore_ptx
  //                                      save GCM state and IV after processing
  //                                      PTX block 0 clear AES, restore, and
  //                                      continue with PTX block 1
  EXECUTE_TEST(result, execute_test, false, false);
  EXECUTE_TEST(result, execute_test, true, false);
  EXECUTE_TEST(result, execute_test, false, true);
  EXECUTE_TEST(result, execute_test, true, true);

  return status_ok(result);
}
