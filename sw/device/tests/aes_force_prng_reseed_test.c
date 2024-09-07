// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/sca/lib/simple_serial.h"
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

//static const unsigned char kAesModesCipherTextEcb128[16] = {
//    0x3a, 0xd7, 0x7b, 0xb4, 0x0d, 0x7a, 0x36, 0x60, 
//    0xa8, 0x9e, 0xca, 0xf3, 0x24, 0x66, 0xef, 0x97};

// Function to print AES blocks key and data
static void aes_print_block(const unsigned char *data, const int num_bytes) {
  for (int i = 0; i < num_bytes; i++) {
    LOG_INFO("%02x ", data[i]);
  }
  LOG_INFO("");  // Print newline after the block
}

//temp//// Function leveraged from aes_testutils_setup_encryption
//temp//status_t aes_testutils_setup_myencryption(dif_aes_transaction_t transaction,
//temp//                                        dif_aes_t *aes) {
//temp//  // Mask the key. Note that this should not be done manually. Software is
//temp//  // expected to get the key in two shares right from the beginning
//temp//  uint8_t key_share0[sizeof(kAesModesKey256)];
//temp//  for (int i = 0; i < sizeof(kAesModesKey256); ++i) {
//temp//    key_share0[i] = kAesModesKey256[i] ^ kKeyShare1[i];
//temp//  }
//temp//
//temp//  // "Convert" key share byte arrays to `dif_aes_key_share_t`
//temp//  memcpy(key.share0, key_share0, sizeof(key.share0));
//temp//  memcpy(key.share1, kKeyShare1, sizeof(key.share1));
//temp//
//temp//  AES_TESTUTILS_WAIT_FOR_STATUS(aes, kDifAesStatusIdle, true,
//temp//                                kAesTestutilsTimeout);
//temp//  CHECK_DIF_OK(dif_aes_start(aes, &transaction, &key, NULL));
//temp//
//temp//  // "Convert" plain data byte arrays to `dif_aes_data_t`
//temp//  dif_aes_data_t in_data_plain;
//temp//  memcpy(in_data_plain.data, kAesModesPlainText, sizeof(in_data_plain.data));
//temp//
//temp//  // Load the plain text to trigger the encryption operation
//temp//  AES_TESTUTILS_WAIT_FOR_STATUS(aes, kDifAesStatusIdle, true,
//temp//                                kAesTestutilsTimeout);
//temp//  AES_TESTUTILS_WAIT_FOR_STATUS(aes, kDifAesStatusInputReady, true,
//temp//                                kAesTestutilsTimeout);
//temp//  CHECK_DIF_OK(dif_aes_load_data(aes, in_data_plain));
//temp//
//temp//  return OK_STATUS();
//temp//}
/**
 *  set edn auto mode
 */
void set_edn_auto_mode(void) {
  const dif_entropy_src_t entropy_src = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR)};
  const dif_csrng_t csrng = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR)};
  const dif_edn_t edn0 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};
  const dif_edn_t edn1 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR)};

  // Disable the entropy complex
  CHECK_STATUS_OK(entropy_testutils_stop_all());

  // Enable ENTROPY_SRC
  CHECK_DIF_OK(dif_entropy_src_configure(
      &entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));

  // Enable CSRNG
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  // Enable EDNs in auto request mode
  // Re-enable EDN0 in auto mode.
  const dif_edn_auto_params_t edn0_params = {
      // EDN0 provides lower-quality entropy.  Let one generate command return 8
      // blocks, and reseed every 32 generates.
      .instantiate_cmd =
          {
              .cmd = 0x00000001 |  // Reseed from entropy source only.
                     kMultiBitBool4False << 8,
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .reseed_cmd =
          {
              .cmd = 0x00008002 |  // One generate returns 8 blocks, reseed
                                   // from entropy source only.
                     kMultiBitBool4False << 8,
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .generate_cmd =
          {
              .cmd = 0x00008003,  // One generate returns 8 blocks.
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .reseed_interval = 32,  // Reseed every 32 generates.
  };
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn0, edn0_params));

  // Re-enable EDN1 in auto mode.
  const dif_edn_auto_params_t edn1_params = {
      // EDN1 provides highest-quality entropy.  Let one generate command
      // return 1 block, and reseed after every generate.
      .instantiate_cmd =
          {
              .cmd = 0x00000001 |  // Reseed from entropy source only.
                     kMultiBitBool4False << 8,
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .reseed_cmd =
          {
              .cmd = 0x00001002 |  // One generate returns 1 block, reseed
                                   // from entropy source only.
                     kMultiBitBool4False << 8,
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .generate_cmd =
          {
              .cmd = 0x00001003,  // One generate returns 1 block.
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .reseed_interval = 4,  // Reseed after every 4 generates.
  };
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn1, edn1_params));
}


static dif_aes_t aes;
/**
 * Initializes the AES peripheral.
 */
static void init_aes(void) {
  SS_CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  SS_CHECK_DIF_OK(dif_aes_reset(&aes));
}


status_t execute_test(void) {
  // Initialize AES, EDN, CSRNG, and Entropy Source
  //dif_aes_t aes;
  dif_edn_t edn0, edn1;
  dif_csrng_t csrng;
  dif_entropy_src_t entropy_src;

  LOG_INFO("Starting AES PRNG reseed stall test with extra debug...");

  // Initialize all modules
  //CHECK_DIF_OK(dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  LOG_INFO("Initializing AES unit.");
  init_aes();

  CHECK_DIF_OK(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  CHECK_DIF_OK(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
  CHECK_DIF_OK(dif_csrng_init(mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(dif_entropy_src_init(mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));

  LOG_INFO("Modules initialized: AES, EDN0, EDN1, CSRNG, Entropy Source");

  // Configure AES for ECB mode, 128-bit key, and manual operation
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
    .manual_operation = kDifAesManualOperationAuto,  // Set AES to automatic
    //operation, where it starts processing as soon as data is available
    //.manual_operation =
    //    kDifAesManualOperationManual,  // Set AES to manual operation, where
                                       // software manually triggers the
                                       // operation
   .reseed_on_key_change = true,  // Enable PRNG reseeding every time the key
                                  // is changed (KEY_TOUCH_FORCES_RESEED)
   .force_masks = true,     // Enable forced masking for the key (important for
                            // security during testing)
   .ctrl_aux_lock = false,  // Do not lock the auxiliary control settings,
                             // allowing further modifications
  };

  LOG_INFO("AES transaction configured: ECB mode, 128-bit key, manual operation.");

  dif_aes_key_share_t key;
  memcpy(key.share0, kAesModesKey128, sizeof(key.share0)); // Share 0 is the test key
  memset(key.share1, 0, sizeof(key.share1));               // Share 1 is zero


  // Start AES with the given transaction
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kTestTimeout);
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, NULL));

  LOG_INFO("AES started: ECB encryption, waiting for input ready.");

  // Monitor AES registers
  monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));

  // "Convert" plain data byte arrays to `dif_aes_data_t`
  dif_aes_data_t in_data_plain;
  memcpy(in_data_plain.data, kAesModesPlainText, sizeof(in_data_plain.data));


  LOG_INFO("Now Starting AES encription process");
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                kTestTimeout);

  // Load the plain text to trigger the encryption operation
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                               kTestTimeout);
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  LOG_INFO("AES encryption started.");
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));
  // Monitor AES registers
  monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));

  if (transaction.force_masks) {
    LOG_INFO("Initializing entropy complex.");
    CHECK_STATUS_OK(aes_testutils_masking_prng_zero_output_seed());
    CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerPrngReseed));
    bool idle = false;
    do {
      CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusIdle, &idle));
    } while (!idle);
  }

  // // Trigger PRNG reseed request
  // LOG_INFO("Triggering PRNG reseed...");
  // CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerPrngReseed));

  // Disable EDN and CSRNG to simulate stalling
  LOG_INFO("Disabling EDN0, EDN1, and CSRNG...");
  CHECK_DIF_OK(dif_edn_stop(&edn0));
  CHECK_DIF_OK(dif_edn_stop(&edn1));
  CHECK_DIF_OK(dif_csrng_stop(&csrng));
  CHECK_DIF_OK(dif_entropy_src_stop(&entropy_src));

  busy_spin_micros(500);  // Sleep for 500 microseconds

  // Check AES registers again after EDN stop
  LOG_INFO("AES registers after disabling EDN and CSRNG:");
  monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));

  // Wait for AES stall status
  LOG_INFO("Waiting for AES stall signal...");
  bool stall = false;

  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusStall, true, kTestTimeout);
  CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusStall, &stall));

  if (stall) {
    LOG_INFO("AES encryption stalled as expected due to EDN being disabled.");
  } else {
    LOG_ERROR("AES encryption did not stall as expected.");
    // Print AES registers again if stall did not occur
    monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));
  }

  // Finish the function at this point to focus on stall detection
  return OK_STATUS();
}

bool test_main(void) {
  return status_ok(execute_test()); // Execute the test and return status
}

