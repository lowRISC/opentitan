// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
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
  kAesNumBlocks = 2,
  // NumBytes in one block is 4x8 i.e. 32 bits in 1 block
  kDifAesBlockNumBytes = 4,
  kDisableEntropyAtStartEn = 1,
};

static const uint8_t kKeyShare1[16] = {
    0x0f, 0x1f, 0x2f, 0x3f, 0x4f, 0x5f, 0x6f, 0x7f,
    0x8f, 0x9f, 0xaf, 0xbf, 0xcf, 0xdf, 0xef, 0xff,
};

// Function to generate a new key based on provided index value
void generate_new_key(dif_aes_key_share_t *key, int index) {
  uint8_t new_key_share0[sizeof(kAesModesKey128)];
  // Generate new key share0 by XOR-ing base key with kKeyShare1*index
  for (size_t i = 0; i < sizeof(kAesModesKey128); ++i) {
    new_key_share0[i] = kAesModesKey128[i] ^ kKeyShare1[i] * (uint8_t)(index);
  }
  // Updating the key shares
  memcpy(key->share0, new_key_share0, sizeof(key->share0));
  memcpy(key->share1, kKeyShare1, sizeof(key->share1));
}

status_t execute_test(void) {
  bool aes_idle = false;
  bool input_ready = false;
  bool output_valid = false;

  // Initialize AES
  TRY(dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  TRY(dif_aes_reset(&aes));

  // Generate key with index 0
  generate_new_key(&key, 0);

  // Prepare transaction
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey128,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = true,
      .force_masks = true,
      .ctrl_aux_lock = false,
  };

  dif_aes_data_t plain_text[kAesNumBlocks];
  dif_aes_data_t cipher_text[kAesNumBlocks];

  // Initialize plaintext data dynamically
  // Create plaintext with random data
  dif_rv_core_ibex_t rv_core_ibex;
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));
  for (uint32_t i = 0; i < ARRAYSIZE(plain_text); ++i) {
    for (uint32_t j = 0; j < kDifAesBlockNumBytes; ++j) {
      uint32_t rand;
      TRY(rv_core_ibex_testutils_get_rnd_data(&rv_core_ibex, 2000, &rand));
      plain_text[i].data[j] = rand;
    }
  }

  // Start the AES operation
  // Wait for AES to be idle before starting encryption
  aes_idle = false;
  do {
    TRY(dif_aes_get_status(&aes, kDifAesStatusIdle, &aes_idle));
  } while (!aes_idle);

  TRY(dif_aes_start(&aes, &transaction, &key, NULL));

  // Variables for status checks
  bool stall = false;
  uint32_t num_of_blocks_loaded = 0;

  // Load multiple input blocks without reading output data
  // to generate STALL status bit assertion
  LOG_INFO("Loading %d blocks without reading output to create back pressure",
           kAesNumBlocks);
  for (uint32_t i = 0; i < kAesNumBlocks; ++i) {
    // Wait for input ready
    input_ready = false;
    do {
      TRY(dif_aes_get_status(&aes, kDifAesStatusInputReady, &input_ready));
    } while (!input_ready);

    // Load data
    TRY(dif_aes_load_data(&aes, plain_text[i]));
    num_of_blocks_loaded++;
    busy_spin_micros(1000);

    // Check for STALL condition
    TRY(dif_aes_get_status(&aes, kDifAesStatusStall, &stall));
    if (i > 0) {
      TRY_CHECK(
          stall,
          "ERROR: AES module not STALLED as expected after loading block %d",
          i);
      LOG_INFO("AES module is stalled as expected after loading block %d", i);
      break;
    }
  }

  if (stall) {
    // Read output data to clear stall
    uint32_t num_of_blocks_read = 0;

    while (num_of_blocks_read < num_of_blocks_loaded) {
      // Wait for output valid
      output_valid = false;
      do {
        TRY(dif_aes_get_status(&aes, kDifAesStatusOutputValid, &output_valid));
      } while (!output_valid);

      // Read output data
      TRY(dif_aes_read_output(&aes, &cipher_text[num_of_blocks_read]));
      num_of_blocks_read++;

      // Check if STALL bit is cleared
      TRY(dif_aes_get_status(&aes, kDifAesStatusStall, &stall));
      TRY_CHECK(!stall, "ERROR: Block %u not successfully read",
                num_of_blocks_read - 1);
    }
  } else {
    TRY_CHECK(stall, "ERROR:STALL condition did not occur...");
  }

  // Finish the AES encryption operation
  LOG_INFO("End AES encryption operation");
  TRY(dif_aes_end(&aes));

  // Wait for AES to be idle before starting decryption
  aes_idle = false;
  do {
    TRY(dif_aes_get_status(&aes, kDifAesStatusIdle, &aes_idle));
  } while (!aes_idle);
  LOG_INFO("AES module is idle");

  return OK_STATUS();
}

bool test_main(void) {
  LOG_INFO("Entering AES aes_stall_test Test");

  return status_ok(execute_test());
}
