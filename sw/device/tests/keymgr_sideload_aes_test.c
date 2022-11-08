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

// Plaintext 16B block matching that input `00112233445566778899aabbccddeeff` to
// the AES C model. Refer to `hw/ip/aes/rtl/aes_cipher_core.sv` for mapping
// plaintext input to the hardware input.
static const uint32_t kPlainText[] = {
    0x33221100,  // word 0.
    0x77665544,  // word 1.
    0xbbaa9988,  // word 2.
    0xffeeddcc,  // word 3.
};

// Expected AES cipher result will be computed at the SV side and overwritten to
// this constant.
static volatile const uint8_t kAESDigest[16] = {0};

static dif_keymgr_t keymgr;
static dif_kmac_t kmac;

OTTF_DEFINE_TEST_CONFIG();

static void keymgr_initialize(void) {
  // Initialize keymgr and advance to CreatorRootKey state.
  keymgr_testutils_startup(&keymgr, &kmac);
  LOG_INFO("Keymgr entered CreatorRootKey State");
  // Generate identity at CreatorRootKey (to follow same sequence and reuse
  // chip_sw_keymgr_key_derivation_vseq.sv).
  keymgr_testutils_generate_identity(&keymgr);
  LOG_INFO("Keymgr generated identity at CreatorRootKey State");

  // Advance to OwnerIntermediateKey state.
  keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams);
  keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerIntermediateKey);
  LOG_INFO("Keymgr entered OwnerIntKey State");

  // Generate sideload key for AES interface at OwnerIntKey state.
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

  // Setup ECB encryption transaction using sideload key.
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey256,
      .key_provider = kDifAesKeySideload,
      .mask_reseeding = kDifAesReseedPer64Block,
      .manual_operation = kDifAesManualOperationManual,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  LOG_INFO(
      "Encrypting the plaintext with 256-bit AES sideload key in ECB mode");
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
  LOG_INFO("Finished encrypting with AES sideloaded key");
  // Finish the ECB encryption transaction.
  CHECK_DIF_OK(dif_aes_end(&aes));

  if (kDeviceType == kDeviceSimDV) {
    LOG_INFO("AES Plaintext (HW Core): 0x%08x%08x%08x%08x",
             in_data_plain.data[0], in_data_plain.data[1],
             in_data_plain.data[2], in_data_plain.data[3]);
    LOG_INFO("AES Ciphertext (HW Core): 0x%08x%08x%08x%08x", out_data.data[3],
             out_data.data[2], out_data.data[1], out_data.data[0]);
    LOG_INFO(
        "AES Expected Ciphertext (from C model): "
        "0x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x",
        kAESDigest[15], kAESDigest[14], kAESDigest[13], kAESDigest[12],
        kAESDigest[11], kAESDigest[10], kAESDigest[9], kAESDigest[8],
        kAESDigest[7], kAESDigest[6], kAESDigest[5], kAESDigest[4],
        kAESDigest[3], kAESDigest[2], kAESDigest[1], kAESDigest[0]);
    CHECK_ARRAYS_EQ(out_data.data, (uint32_t *)kAESDigest,
                    ARRAYSIZE(out_data.data));
  }

  LOG_INFO("Decrypting the ciphertext with the sideloaded key.");
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

  LOG_INFO("Clearing the sideloaded key.");

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
