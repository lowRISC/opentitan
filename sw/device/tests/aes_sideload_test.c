// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/kmac_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"  // Generated.

#define TIMEOUT (1000 * 1000)

static const uint32_t kPlainText[] = {
    0x33221100,
    0x77665544,
    0xbbaa9988,
    0xffeeddcc,
};
static dif_keymgr_t keymgr;
static dif_kmac_t kmac;

OTTF_DEFINE_TEST_CONFIG();

static void keymgr_initialize(void) {
  // Initialize keymgr and advance to CreatorRootKey state.
  keymgr_testutils_startup(&keymgr, &kmac);

  keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams);
  keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerIntermediateKey);
  LOG_INFO("Keymgr entered OwnerIntKey State");

  dif_keymgr_versioned_key_params_t sideload_params = kKeyVersionedParams;
  sideload_params.dest = kDifKeymgrVersionedKeyDestAes;
  keymgr_testutils_generate_versioned_key(&keymgr, sideload_params);
  LOG_INFO("Keymgr generated HW output for Aes at OwnerIntKey State");
}

void aes_test(void) {
  dif_aes_t aes;
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  // Setup ECB encryption transaction.
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey256,
      .manual_operation = kDifAesManualOperationManual,
      .masking = kDifAesMaskingInternalPrng,
      .key_provider = kDifAesKeySideload,
      .mask_reseeding = kDifAesReseedPer64Block,
  };

  LOG_INFO("Encrypting the plain text with the side loaded key.");
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, NULL, NULL));
  dif_aes_data_t in_data_plain;
  memcpy(in_data_plain.data, kPlainText, sizeof(kPlainText));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true, TIMEOUT);
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  // Trigger the AES encryption and wait for it to complete.
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true, TIMEOUT);

  //  Verify that the ciphertext is different from the plaintext.
  dif_aes_data_t out_data;
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data));
  CHECK_ARRAYS_NE(out_data.data, kPlainText, ARRAYSIZE(kPlainText));

  // Finish the ECB encryption transaction.
  CHECK_DIF_OK(dif_aes_end(&aes));

  LOG_INFO("Decrypting the cypher text with the side loaded key.");
  transaction.operation = kDifAesOperationDecrypt;
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, NULL, NULL));
  memcpy(in_data_plain.data, out_data.data, sizeof(out_data.data));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true, TIMEOUT);
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  // Trigger the AES decryption and wait for it to complete.
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true, TIMEOUT);

  // Verify that the output is equal to the plain text.
  dif_aes_data_t out_data_plain;
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data_plain));
  CHECK_ARRAYS_EQ(out_data_plain.data, kPlainText, ARRAYSIZE(kPlainText));

  // Finish the ECB decryption transaction.
  CHECK_DIF_OK(dif_aes_end(&aes));

  LOG_INFO("Clearing the side loaded key.");

  // Clear the key in the keymgr and decrypt the ciphertext again.
  CHECK_DIF_OK(
      dif_keymgr_sideload_clear_set_enabled(&keymgr, kDifToggleEnabled));
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, NULL, NULL));

  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true, TIMEOUT);
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  // Trigger the AES decryption and wait for it to complete.
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true, TIMEOUT);

  // Verify that output is not equal to the plain text.
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data_plain));
  CHECK_ARRAYS_NE(out_data_plain.data, kPlainText, ARRAYSIZE(kPlainText));
  CHECK_DIF_OK(dif_aes_end(&aes));
}

bool test_main(void) {
  // Configure the keymgr to generate an AES key.
  keymgr_initialize();

  // Run the AES test.
  aes_test();

  return true;
}
