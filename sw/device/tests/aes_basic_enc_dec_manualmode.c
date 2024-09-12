// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

// Register Offsets based on the OpenTitan documentation
#define AES_CTRL_SHADOWED_REG_OFFSET         0x74
#define AES_CTRL_AUX_SHADOWED_REG_OFFSET     0x78
#define AES_CTRL_AUX_REGWEN_REG_OFFSET       0x7C
#define AES_TRIGGER_REG_OFFSET               0x80
#define AES_STATUS_REG_OFFSET                0x84
#define AES_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_BIT  0
#define AES_CTRL_AUX_SHADOWED_FORCE_MASKS_BIT              1
// Function to monitor and log the value of specific AES registers.
static void monitor_aes_registers(mmio_region_t aes_base) {
  uint32_t ctrl_shadowed = mmio_region_read32(aes_base, AES_CTRL_SHADOWED_REG_OFFSET);
  uint32_t ctrl_aux_shadowed = mmio_region_read32(aes_base, AES_CTRL_AUX_SHADOWED_REG_OFFSET);
  uint32_t ctrl_aux_regwen = mmio_region_read32(aes_base, AES_CTRL_AUX_REGWEN_REG_OFFSET);
  uint32_t trigger = mmio_region_read32(aes_base, AES_TRIGGER_REG_OFFSET);
  uint32_t status = mmio_region_read32(aes_base, AES_STATUS_REG_OFFSET);

  LOG_INFO("REGISTER AES_CTRL_SHADOWED: 0x%x", ctrl_shadowed);
  LOG_INFO("REGISTER AES_CTRL_AUX_SHADOWED: 0x%x", ctrl_aux_shadowed);
  LOG_INFO("REGISTER AES_STATUS: 0x%x", status);
  LOG_INFO("REGISTER AES_TRIGGER: 0x%x", trigger);
  LOG_INFO("REGISTER AES_CTRL_AUX_REGWEN: 0x%x", ctrl_aux_regwen);
}


enum {
  kTestTimeout = 1000 * 1000,  // Timeout for waiting for AES operations
};

// AES key used for the test
static const unsigned char kAesModesKey128[16] = {
    0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
    0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c};

static const unsigned char kAesModesPlainText[16] = {
    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 
    0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,};

static const unsigned char kAesModesCipherTextEcb128[16] = {
    0x3a, 0xd7, 0x7b, 0xb4, 0x0d, 0x7a, 0x36, 0x60, 
    0xa8, 0x9e, 0xca, 0xf3, 0x24, 0x66, 0xef, 0x97};

// Function to print AES blocks key and data
static void aes_print_block(const unsigned char *data, const int num_bytes) {
  for (int i = 0; i < num_bytes; i++) {
    LOG_INFO("%02x ", data[i]);
  }
  LOG_INFO("");  // Print newline after the block.
}

status_t execute_test(void) {
  // Initialize the AES, EDN, and CSRNG hardware interfaces
  dif_aes_t aes;
  //dif_edn_t edn = {
  //    .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};
  // dif_csrng_t csrng = {
  //     .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR)};

  // Initialize AES hardware
  CHECK_DIF_OK(dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR),
                            &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes)); // Reset AES to a known state
  LOG_INFO("AES hardware initialized and reset.");

  // Monitor AES registers
  LOG_INFO("AES registers after hardware initialized and reset:");
  monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));

  // Configure AES for ECB mode, 128-bit key, and manual operation
  // Define the transaction settings for the AES module
  LOG_INFO("AES transaction to be configured as: Operation=Encrypt, Mode=ECB, Key Length=128-bit, Manual Operation, reseed=true and force_masks=True for our desired operation");

dif_aes_transaction_t transaction = {
    .operation =
        kDifAesOperationEncrypt,  // Set the AES operation to encryption
    .mode =
        kDifAesModeEcb,  // Use Electronic Codebook (ECB) mode for encryption
    .key_len = kDifAesKey128,  // Use a 128-bit key for encryption
    .key_provider = kDifAesKeySoftwareProvided,  // The encryption key is
                                                 // provided by software
    //.mask_reseeding = kDifAesReseedPer64Block,   // Configure the PRNG to reseed
    //                                             // every 64 blocks
    .mask_reseeding = kDifAesReseedPerBlock,  // Resseed PRNG every block (128 bits)                                                 
    //.manual_operation = kDifAesManualOperationAuto,  // Set AES to automatic
    //operation, where it starts processing as soon as data is available
    .manual_operation =
        kDifAesManualOperationManual,  // Set AES to manual operation, where
                                       // software manually triggers the
                                       // operation
   .reseed_on_key_change = true,  // Enable PRNG reseeding every time the key
                                  // is changed (KEY_TOUCH_FORCES_RESEED)
   .force_masks = false,     // Enable forced masking for the key (important for
                            // security during testing)
   .ctrl_aux_lock = false,  // Do not lock the auxiliary control settings,
                             // allowing further modifications
};


  // "Convert" key share byte arrays to `dif_aes_key_share_t`
  // Setup the key with one share being `kAesModesKey128` and the other share as zero
  dif_aes_key_share_t key;
  memcpy(key.share0, kAesModesKey128, sizeof(key.share0)); // Share 0 is the test key
  memset(key.share1, 0, sizeof(key.share1));        // Share 1 is zero

  // Debug: Print key being used for the encryption
  LOG_INFO("Using below key for encription key.share0:");
  aes_print_block((const unsigned char *)key.share0, 16);


  // Debug: Print key being used for the encryption
  LOG_INFO("Using below key for encription key.share1:");
  aes_print_block((const unsigned char *)key.share1, 16);


  // Encrypt the data and print the ciphertext
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                kTestTimeout);
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, NULL));

  // "Convert" plain data byte arrays to `dif_aes_data_t`.
  dif_aes_data_t in_data_plain;
  memcpy(in_data_plain.data, kAesModesPlainText, sizeof(in_data_plain.data));

  // Monitor AES registers after configuration
  LOG_INFO("AES registers after hardware initialized and reset and configured:");
  monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));

  LOG_INFO("Now Starting AES encription process");
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                kTestTimeout);

  // Load the plain text to trigger the encryption operation.
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                kTestTimeout);
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                               kTestTimeout);
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  LOG_INFO("AES encryption started.");
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));

  LOG_INFO("Ciphertext after encryption:");
  aes_print_block((const unsigned char *)in_data_plain.data, 16);

  // Read out the produced cipher text.
  dif_aes_data_t out_data;
  LOG_INFO("AES dif_aes_read_output:");
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data));

  // Finish the ECB encryption transaction.
  CHECK_DIF_OK(dif_aes_end(&aes));
  LOG_INFO("AES comparison out_data with CipherText:");
  CHECK_ARRAYS_EQ((uint8_t *)out_data.data, kAesModesCipherTextEcb128,
                  sizeof(out_data.data));

  // Setup ECB decryption transaction.
  LOG_INFO("AES set for decryption");
  // Setup AES for decryption
  transaction.operation = kDifAesOperationDecrypt;
  transaction.key_len = kDifAesKey128;  // Ensure 128-bit key length is explicitly set
  // Ensure manual operation
  transaction.key_provider = kDifAesKeySoftwareProvided;
  transaction.manual_operation = kDifAesManualOperationManual;

  // Reinitialize the AES with decryption settings
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, NULL));  // Start decryption
                                                              //
  // Monitor AES registers after decryption process
  LOG_INFO("AES registers after AES decryption configured");
  monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));

  // Load the previously produced cipher text to start the decryption operation.
  LOG_INFO("AES decryption waiting for Status Input Ready");
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                                kTestTimeout);
  CHECK_DIF_OK(dif_aes_load_data(&aes, out_data));

  LOG_INFO("Starting AES dif_aes_start:");
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));

  // Read out the produced plain text.
  LOG_INFO("AES decryption waiting for kDifAesStatusOutputValid");
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true,
                                kTestTimeout);
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data));

  // Finish the ECB encryption transaction.
  LOG_INFO("AES dif_aes_end");
  CHECK_DIF_OK(dif_aes_end(&aes));

  // Monitor AES registers after decryption process
  LOG_INFO("AES registers after AES decryption finished:");
  monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));

  LOG_INFO("Decrypted text:");
  aes_print_block((const unsigned char *)out_data.data, 16);

  LOG_INFO("AES decryption compare arrays out_data vs PlainText:");
  CHECK_ARRAYS_EQ((uint8_t *)out_data.data, kAesModesPlainText,
                  sizeof(out_data.data));

  return OK_STATUS(); // Return successful status
}

bool test_main(void) {
  return status_ok(execute_test()); // Execute the test and return status
}

