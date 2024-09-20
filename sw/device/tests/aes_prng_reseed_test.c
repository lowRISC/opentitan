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
  kNumTestConfigs = 2,
  kMaxChunkSize = 300,
};

typedef struct {
  dif_aes_mask_reseeding_t mask_reseeding;
  uint32_t kAesNumBlocks;
  // NumBytes in one block is 4x8 i.e. 32 bits in 1 block
  uint32_t kDifAesBlockNumBytes;
  uint32_t disable_entropy_after_block;
  uint32_t enable_entropy_at_block;
} aes_test_config_t;

aes_test_config_t test_configs[kNumTestConfigs] = {
    // Test 1 configuration with kDifAesReseedPer64Block
    {
        .mask_reseeding = kDifAesReseedPer64Block,
        .kAesNumBlocks = 68,
        .kDifAesBlockNumBytes = 4,
        .disable_entropy_after_block = 32,
        .enable_entropy_at_block = 63,
    },
    // Test 2 configuration with kDifAesReseedPer8kBlock
    {
        .mask_reseeding = kDifAesReseedPer8kBlock,
        .kAesNumBlocks = 8400,
        .kDifAesBlockNumBytes = 4,
        .disable_entropy_after_block = 41,
        .enable_entropy_at_block = 8191,
    },
};

static const uint8_t kKeyShare1[16] = {
    0x0f, 0x1f, 0x2f, 0x3f, 0x4f, 0x5f, 0x6f, 0x7f,
    0x8f, 0x9f, 0xaf, 0xbf, 0xcf, 0xdf, 0xef, 0xff,
};

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

// status_t execute_test(void) {
status_t execute_test(aes_test_config_t *config) {
  bool aes_idle = false;
  bool input_ready = false;
  bool output_valid = false;

  LOG_INFO(
      "Testing AES PRNG Reseed Test with number of blocks: %d (Block 0 to %d), "
      "and disabling entropy after block number: %d",
      config->kAesNumBlocks, config->kAesNumBlocks - 1,
      config->disable_entropy_after_block - 1);
  // Initialize AES
  TRY(dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  TRY(dif_aes_reset(&aes));
  // Initialize EDN0, EDN1, CSRNG and Entropy Source
  TRY(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  TRY(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
  TRY(dif_csrng_init(mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR),
                     &csrng));
  TRY(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));

  // Generate key with index 0
  generate_new_key(&key, 0);

  // Prepare transaction
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey128,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = config->mask_reseeding,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = true,
      .force_masks = false,
      .ctrl_aux_lock = false,
  };
  // Start the AES operation
  // Wait for AES to be idle before starting encryption
  aes_idle = false;
  do {
    TRY(dif_aes_get_status(&aes, kDifAesStatusIdle, &aes_idle));
  } while (!aes_idle);
  TRY(dif_aes_start(&aes, &transaction, &key, NULL));

  dif_aes_data_t plain_text[kMaxChunkSize];
  dif_aes_data_t cipher_text[kMaxChunkSize];

  uint32_t total_blocks = config->kAesNumBlocks;

  uint32_t blocks_processed = 0;

  // Initialize plaintext data dynamically
  // Create plaintext with random data
  dif_rv_core_ibex_t rv_core_ibex;
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));
  for (uint32_t i = 0; i < ARRAYSIZE(plain_text); ++i) {
    for (uint32_t j = 0; j < config->kDifAesBlockNumBytes; ++j) {
      uint32_t rand;
      TRY(rv_core_ibex_testutils_get_rnd_data(&rv_core_ibex, 2000, &rand));
      plain_text[i].data[j] = rand;
    }
  }

  // Now start encryption process for the blocks in chunks
  while (blocks_processed < total_blocks) {
    uint32_t blocks_to_process = total_blocks - blocks_processed;
    if (blocks_to_process > kMaxChunkSize) {
      blocks_to_process = kMaxChunkSize;
    }

    // Start encryption process
    // Process the blocks in this chunk
    for (uint32_t i = 0; i < blocks_to_process; ++i) {
      uint32_t block_index = blocks_processed + i;

      // Wait for input ready
      input_ready = false;
      do {
        TRY(dif_aes_get_status(&aes, kDifAesStatusInputReady, &input_ready));
      } while (!input_ready);

      // Load data
      TRY(dif_aes_load_data(&aes, plain_text[i]));

      // Disable entropy complex after processing enough blocks
      if (block_index == config->disable_entropy_after_block) {
        LOG_INFO("Disabling entropy complex to induce AES halt at block %d",
                 block_index);
        CHECK_STATUS_OK(disable_entropy_complex());
        busy_spin_micros(1000);
      }

      // Check for halt when PRNG reseed is required
      if (block_index == config->enable_entropy_at_block) {
        output_valid = false;
        TRY(dif_aes_get_status(&aes, kDifAesStatusOutputValid, &output_valid));
        CHECK(!output_valid,
              "ERROR: AES encryption did not halt when entropy was disabled at "
              "block %d",
              block_index);
        LOG_INFO("AES encryption is halted as expected at block %d",
                 block_index);

        // Re-enable the entropy complex
        LOG_INFO("Re-enabling entropy complex at block %d", block_index);
        CHECK_STATUS_OK(enable_entropy_complex());
        busy_spin_micros(500);
      }

      // Wait for the AES module to produce output valid
      output_valid = false;
      do {
        TRY(dif_aes_get_status(&aes, kDifAesStatusOutputValid, &output_valid));
      } while (!output_valid);

      // Read output data
      TRY(dif_aes_read_output(&aes, &cipher_text[i]));
    }
    // Update blocks_processed
    blocks_processed += blocks_to_process;
  }

  // Finish the AES encryption operation
  LOG_INFO("End AES encryption operation");
  TRY(dif_aes_end(&aes));

  // Wait for AES to be idle to check aes encryption process has ended
  aes_idle = false;
  do {
    TRY(dif_aes_get_status(&aes, kDifAesStatusIdle, &aes_idle));
  } while (!aes_idle);
  LOG_INFO("AES module is idle");

  // After ensuring the AES module is idle
  // Reset the AES module before starting decryption
  TRY(dif_aes_reset(&aes));

  return OK_STATUS();
}

bool test_main(void) {
  for (size_t i = 0; i < kNumTestConfigs; ++i) {
    aes_test_config_t *config = &test_configs[i];

    // Log the current test configuration
    LOG_INFO("Starting AES PRNG Reseed Test with mask_reseeding: %d",
             config->mask_reseeding);

    // Call execute_test with the current configuration
    CHECK_STATUS_OK(execute_test(config));
  }

  return true;
}
