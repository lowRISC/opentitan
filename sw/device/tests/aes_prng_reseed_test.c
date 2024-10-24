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
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/sca/lib/simple_serial.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_aes_t aes;
dif_aes_key_share_t key;
enum {
  kAesNumBlocks = 68,
  // NumBytes should be 1 i.e. 8 bits
  kDifAesBlockNumBytes = 4,
  disable_entropy_after_block = 32,
};

static const uint8_t kKeyShare1[16] = {
    0x0f, 0x1f, 0x2f, 0x3f, 0x4f, 0x5f, 0x6f, 0x7f,
    0x8f, 0x9f, 0xaf, 0xbf, 0xcf, 0xdf, 0xef, 0xff,
};

///////////////////////////////////////////////////////////////////////////////
static dif_edn_t edn0, edn1;
static dif_csrng_t csrng;
static dif_entropy_src_t entropy_src;
// Function to disable entropy complex
status_t disable_entropy_complex(void) {
  // Using entropy test utility to stop all EDN0, EDN1, CSRNG, and the Entropy
  // Source
  TRY(entropy_testutils_stop_all());
  LOG_INFO("The entire entropy complex is stopped");
  return OK_STATUS();
}

// Function to enable entropy complex
status_t enable_entropy_complex(void) {
  // Using entropy test utility to enable all EDN0, EDN1, CSRNG, and the
  // Entropy Source
  TRY(entropy_testutils_auto_mode_init());
  LOG_INFO("The entire entropy complex is enabled");
  return OK_STATUS();
}

// Function to generate a new key based on provided index value
void generate_new_key(dif_aes_key_share_t *key, int index) {
  uint8_t new_key_share0[sizeof(kAesModesKey128)];
  // Generate new key share0 by XOR-ing base key with kKeyShare1*index
  for (size_t i = 0; i < sizeof(kAesModesKey128); ++i) {
    new_key_share0[i] = kAesModesKey128[i] ^ kKeyShare1[i] * (uint8_t)(index);
  }
  // Update the key shares
  memcpy(key->share0, new_key_share0, sizeof(key->share0));
  memcpy(key->share1, kKeyShare1, sizeof(key->share1));
}

status_t execute_test(void) {
  bool aes_idle = false;
  bool input_ready = false;
  bool output_valid = false;

  LOG_INFO(
      "Testing aes_prng_reseed_test with number of blocks: %d (Block 0 to %d), "
      "and disabling entropy after block "
      "number: %d",
      kAesNumBlocks, kAesNumBlocks - 1, disable_entropy_after_block - 1);
  // Initialize AES
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));
  // Initialize EDN0, EDN1, CSRNG and Entropy Source
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));

  // Generate key with index 0
  generate_new_key(&key, 0);

  // Prepare transaction
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey128,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPer64Block,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = true,
      .force_masks = false,
      .ctrl_aux_lock = false,
  };
  // Start the AES operation
  // Wait for AES to be idle before starting encryption
  aes_idle = false;
  do {
    CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusIdle, &aes_idle));
  } while (!aes_idle);

  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, NULL));

  dif_aes_data_t plain_text[kAesNumBlocks];
  dif_aes_data_t cipher_text[kAesNumBlocks];

  // Initialize plaintext data dynamically
  // Create plaintext with random data
  dif_rv_core_ibex_t rv_core_ibex;
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));
  for (int i = 0; i < kAesNumBlocks; ++i) {
    for (int j = 0; j < kDifAesBlockNumBytes; ++j) {
      uint32_t rand;
      TRY(rv_core_ibex_testutils_get_rnd_data(&rv_core_ibex, 2000, &rand));
      plain_text[i].data[j] = rand;
    }
  }

  // Process the first two blocks using dif_aes_process_data()
  dif_aes_data_t aes_block_plain_text_12[2];
  dif_aes_data_t aes_block_cipher_text_12[2];

  // Collect the first two blocks
  aes_block_plain_text_12[0] = plain_text[0];
  aes_block_plain_text_12[1] = plain_text[1];

  // Encrypt the first two blocks
  LOG_INFO("Using dif_aes_process_data() for the first two blocks");
  CHECK_DIF_OK(dif_aes_process_data(&aes, aes_block_plain_text_12,
                                    aes_block_cipher_text_12, 2));

  // Store the encrypted data
  cipher_text[0] = aes_block_cipher_text_12[0];
  cipher_text[1] = aes_block_cipher_text_12[1];

  // Now start encryption process for the remaining blocks starting from i = 2
  // Start encryption process
  for (int i = 2; i < kAesNumBlocks; ++i) {
    // Wait for input ready
    input_ready = false;
    do {
      CHECK_DIF_OK(
          dif_aes_get_status(&aes, kDifAesStatusInputReady, &input_ready));
    } while (!input_ready);

    // Load data
    CHECK_DIF_OK(dif_aes_load_data(&aes, plain_text[i]));

    // Check for stall after entropy disabled
    if (i == disable_entropy_after_block) {
      output_valid = false;
      CHECK_DIF_OK(
          dif_aes_get_status(&aes, kDifAesStatusOutputValid, &output_valid));
      if (output_valid) {
        LOG_INFO(
            "AES encryption has output_valid as expected after entropy "
            "disabled at block %d",
            i);
      } else {
        LOG_ERROR("ERROR:AES encryption did not generate output_valid");
      }
    }

    // Wait for the AES module to resume and produce output valid
    output_valid = false;
    do {
      CHECK_DIF_OK(
          dif_aes_get_status(&aes, kDifAesStatusOutputValid, &output_valid));
    } while (!output_valid);

    // Read output data
    CHECK_DIF_OK(dif_aes_read_output(&aes, &cipher_text[i]));

    // Disable entropy complex after processing enough blocks
    if (i == disable_entropy_after_block - 1) {
      LOG_INFO("Disabling entropy complex to induce AES stall after block %d",
               disable_entropy_after_block - 1);
      CHECK_STATUS_OK(disable_entropy_complex());
      busy_spin_micros(1000);
    }
    if (i == 62) {
      LOG_INFO("Enabling entropy complex after block %d", i);
      CHECK_STATUS_OK(enable_entropy_complex());
      busy_spin_micros(500);
    }
  }

  // Finish the AES encryption operation
  LOG_INFO("End AES encryption operation");
  CHECK_DIF_OK(dif_aes_end(&aes));

  // Wait for AES to be idle to check aes encryption process has ended
  aes_idle = false;
  do {
    CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusIdle, &aes_idle));
  } while (!aes_idle);
  LOG_INFO("AES module is idle");

  return OK_STATUS();
}

bool test_main(void) {
  LOG_INFO("Entering AES aes_prng_reseed_test Test");

  return status_ok(execute_test());
}
