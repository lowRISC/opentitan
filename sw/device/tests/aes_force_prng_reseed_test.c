// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/sca/lib/simple_serial.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kTestTimeout = 1000 * 1000,  // Timeout for waiting for AES operations
};

static dif_aes_t aes;
static dif_edn_t edn0, edn1;
static dif_csrng_t csrng;
static dif_entropy_src_t entropy_src;

// Function to fetch and log CSRNG internal state
static void log_csrng_internal_state(const dif_csrng_t *csrng) {
  dif_csrng_internal_state_t csrng_state;
  dif_csrng_internal_state_id_t instance_id = kCsrngInternalStateIdSw;

  CHECK_DIF_OK(dif_csrng_get_internal_state(csrng, instance_id, &csrng_state));

  LOG_INFO("CSRNG internal state: 0x%x", csrng_state);
}

void monitor_entropy_sources(void) {
  // EDN status monitoring
  bool edn_status0, edn_status1;
  CHECK_DIF_OK(dif_edn_get_status(&edn0, kDifEdnStatusReady, &edn_status0));
  CHECK_DIF_OK(dif_edn_get_status(&edn1, kDifEdnStatusReady, &edn_status1));
  LOG_INFO("EDN0 status: 0x%x", edn_status0);
  LOG_INFO("EDN1 status: 0x%x", edn_status1);
}

// Function to check the status of EDN
static void monitor_edn_status(const dif_edn_t *edn0, const dif_edn_t *edn1) {
  bool edn_status0, edn_status1;

  // Check EDN0 status using kDifEdnStatusReady flag
  CHECK_DIF_OK(dif_edn_get_status(edn0, kDifEdnStatusReady, &edn_status0));
  LOG_INFO("EDN0 status (Ready): 0x%x", edn_status0);

  // Check EDN1 status using kDifEdnStatusReady flag
  CHECK_DIF_OK(dif_edn_get_status(edn1, kDifEdnStatusReady, &edn_status1));
  LOG_INFO("EDN1 status (Ready): 0x%x", edn_status1);
}

// AES key used for the test
static const unsigned char kAesModesKey128[16] = {
    0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
    0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c};

static const unsigned char kAesModesPlainText[16] = {
    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
    0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
};

static const unsigned char kAesModesCipherTextEcb128[16] = {
    0x3a, 0xd7, 0x7b, 0xb4, 0x0d, 0x7a, 0x36, 0x60,
    0xa8, 0x9e, 0xca, 0xf3, 0x24, 0x66, 0xef, 0x97};

/*
The mask share, used to mask kKey. Note that the masking should not be done
manually. Software is expected to get the key in two shares right from the
beginning.
*/
static const uint8_t kKeyShare1[] = {
    0x0f, 0x1f, 0x2f, 0x3F, 0x4f, 0x5f, 0x6f, 0x7f, 0x8f, 0x9f, 0xaf,
    0xbf, 0xcf, 0xdf, 0xef, 0xff, 0x0a, 0x1a, 0x2a, 0x3a, 0x4a, 0x5a,
    0x6a, 0x7a, 0x8a, 0x9a, 0xaa, 0xba, 0xca, 0xda, 0xea, 0xfa,
};

// Function to print AES blocks key and data
static void aes_print_block(const unsigned char *data, const int num_bytes) {
  for (int i = 0; i < num_bytes; i++) {
    LOG_INFO("%02x ", data[i]);
  }
  LOG_INFO("");
}

status_t execute_test(void) {
  // Initialize AES, EDN, CSRNG, and Entropy Source

  // Initialize all modules
  LOG_INFO("Initializing AES unit.");
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));
  LOG_INFO("Module initialized: AES");
  LOG_INFO("Starting AES PRNG reseed stall test with extra debug...");
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  LOG_INFO("Modules initialized: EDN0, EDN1, CSRNG, Entropy Source");

  // Configure AES for ECB mode, 128-bit key, and manual operation
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey128,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationManual,
      .reseed_on_key_change = true,
      .force_masks = false,
      .ctrl_aux_lock = false,
  };

  LOG_INFO(
      "AES transaction configured: ECB mode, 128-bit key, manual operation.");

  // Disable EDN and CSRNG to simulate stalling
  LOG_INFO("Disabling EDN0, EDN1...");
  CHECK_DIF_OK(dif_edn_stop(&edn0));
  CHECK_DIF_OK(dif_edn_stop(&edn1));
  busy_spin_micros(500);

  LOG_INFO("Conditionally checking AES status after stopping EDN and CSRNG.");
  LOG_INFO("Waiting for AES to stall after PRNG reseed request...");
  bool stall = false;
  CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusStall, &stall));

  if (stall) {
    LOG_INFO("AES encryption has stalled as expected.");
  } else {
    LOG_ERROR(
        "ERROR:AES encryption did not stall as expected after EDN stop! Lets "
        "proceed "
        "for now to verify further steps...");
  }

  log_csrng_internal_state(&csrng);
  monitor_entropy_sources();

  // Expanding aes_testutils_setup_encryption T1 to T8:
  // T: Start of aes_testutils_setup_encryption function steps
  // T1: Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.
  uint8_t key_share0[sizeof(kAesModesKey128)];
  for (int i = 0; i < sizeof(kAesModesKey128); ++i) {
    key_share0[i] = kAesModesKey128[i] ^ kKeyShare1[i];
  }

  // T2: "Convert" key share byte arrays to `dif_aes_key_share_t`.
  dif_aes_key_share_t key;
  memcpy(key.share0, key_share0, sizeof(key.share0));
  memcpy(key.share1, kKeyShare1, sizeof(key.share1));

  // T3:  Wait for status kDifAesStatusIdle
  // Start AES with the given transaction
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kTestTimeout);

  // T4: dif_aes_start
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, NULL));

  LOG_INFO("Disabling CSRNG...");
  CHECK_DIF_OK(dif_csrng_stop(&csrng));
  CHECK_DIF_OK(dif_entropy_src_stop(&entropy_src));

  // Re-enable Entropy Source and CSRNG in the proper sequence
  LOG_INFO("Re-initializing Entropy Source and CSRNG...");

  // Initialize and configure Entropy Source
  dif_entropy_src_config_t entropy_src_config =
      entropy_testutils_config_default();
  CHECK_DIF_OK(dif_entropy_src_configure(&entropy_src, entropy_src_config,
                                         kDifToggleEnabled));

  // Initialize and start CSRNG
  CHECK_DIF_OK(dif_csrng_configure(&csrng));
  // set_edn_auto_mode();
  LOG_INFO("Setting EDN to auto mode...");
  TRY(entropy_testutils_auto_mode_init());
  // CHECK_DIF_OK(entropy_testutils_auto_mode_init());
  monitor_edn_status(&edn0, &edn1);

  // Trigger PRNG reseed request
  LOG_INFO("Triggering PRNG reseed...");
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerPrngReseed));

  // T5: "Convert" plain data byte arrays to `dif_aes_data_t`
  dif_aes_data_t in_data_plain;
  memcpy(in_data_plain.data, kAesModesPlainText, sizeof(in_data_plain.data));

  // T6: Wait ofr Status kDifAesStatusIdle
  LOG_INFO(
      "Now Starting AES encryption process firstly by observing if AES is in "
      "Idle state");
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kTestTimeout);

  // T7: Wait for Status input DifAesStatusInputReady
  LOG_INFO("AES started: ECB encryption, waiting for input ready.");
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                                kTestTimeout);
  // T8: Load the plain text to trigger the encryption operation
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  // Trigger AES reseed request, specific for manual operation case
  LOG_INFO("AES encryption started.");
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));

  busy_spin_micros(500);

  LOG_INFO("Disabling CSRNG...");
  CHECK_DIF_OK(dif_csrng_stop(&csrng));
  CHECK_DIF_OK(dif_entropy_src_stop(&entropy_src));

  // Re-enable Entropy Source and CSRNG in the proper sequence
  LOG_INFO("Re-initializing Entropy Source and CSRNG...");
  // Initialize and configure Entropy Source
  dif_entropy_src_config_t entropy_src_config_1 =
      entropy_testutils_config_default();
  CHECK_DIF_OK(dif_entropy_src_configure(&entropy_src, entropy_src_config_1,
                                         kDifToggleEnabled));
  // Initialize and start CSRNG
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  LOG_INFO("Setting EDN to auto mode...");
  TRY(entropy_testutils_auto_mode_init());
  // CHECK_DIF_OK(entropy_testutils_auto_mode_init());
  monitor_edn_status(&edn0, &edn1);

  // Read out the produced cipher text.
  dif_aes_data_t out_data;
  LOG_INFO("AES dif_aes_read_output:");
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data));

  LOG_INFO("Encrypted text:");
  aes_print_block((const unsigned char *)out_data.data, 16);

  // Finish the ECB encryption transaction.
  CHECK_DIF_OK(dif_aes_end(&aes));
  LOG_INFO("AES comparison out_data with CipherText:");
  CHECK_ARRAYS_EQ((uint8_t *)out_data.data, kAesModesCipherTextEcb128,
                  sizeof(out_data.data));

  return OK_STATUS();
}

bool test_main(void) { return status_ok(execute_test()); }
