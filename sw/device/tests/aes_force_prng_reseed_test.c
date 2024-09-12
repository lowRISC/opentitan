// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
/* # Procedure:
   #         -Configures the auxiliary options for AES to enable KEY_TOUCH_FORCES_RESEED
   #         -Disable the EDN using dif_edn_stop()
   #         -Configure the encryption operation, mode, key length, and set the engine to manual
   #          operation.
   #         -Set up encryption using aes_testutils_setup_encryption()
   #           -At this point dif_aes_start() will write the key register which will trigger reseed
   #            request. This request will stall the encryption until EDN is re-enabled.
   #         -Verify that the encryption stalls.
   #         -Re-enable EDN. In order to do this it is required to first disable and re-enable the
   #          CSRNG. In order to re-enable CSRNG, it is required to first disable and re-enable
   #          the entropy source. The following sequence of steps should be used:
   #             -Disable CSRNG
   #             -Disable Entropy Source
   #             -Enable Entropy Source
   #             -Enable CSRNG
   #             -Enable EDN
   #         -Verify that the AES completes encryption.
*/


#define RESEED_TEST_EN 1  // Set to 1 to enable, 0 to disable
#define DEBUG_EN 0  // Set to 1 to enable, 0 to disable
#define TRYSETTING1_EN 1 // Set to 1 to enable, 0 to disable

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
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"

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

static  dif_aes_t aes;
#if RESEED_TEST_EN
  static  dif_edn_t edn0, edn1;
  static  dif_csrng_t csrng;
  static  dif_entropy_src_t entropy_src;

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
    CHECK_DIF_OK(dif_edn_get_status(&edn0, kDifEdnStatusReady, &edn_status0)); // Provide flag for status
    CHECK_DIF_OK(dif_edn_get_status(&edn1, kDifEdnStatusReady, &edn_status1)); // Provide flag for status
    LOG_INFO("EDN0 status: 0x%x", edn_status0);
    LOG_INFO("EDN1 status: 0x%x", edn_status1);
  }
  
  // Register Offsets based on the OpenTitan documentation for EDN
  #define EDN_INTR_STATE_REG_OFFSET 0x0
  #define EDN_CTRL_REG_OFFSET 0x14
  #define EDN_SW_CMD_REQ_REG_OFFSET 0x20
  #define EDN_SW_CMD_STS_REG_OFFSET 0x24  
  #define EDN_RESEED_CMD_REG_OFFSET 0x2C
  #define EDN_MAIN_SM_STATE_REG_OFFSET 0x44
  
  // Function to monitor and log the value of specific EDN registers.
  static void monitor_edn_registers(mmio_region_t edn_base) {
    //Base address to integer for comparison
    uintptr_t base_addr = (uintptr_t)edn_base.base;
  
    // Check if the base address belongs to EDN0 or EDN1
    if (base_addr == TOP_EARLGREY_EDN0_BASE_ADDR) {
      LOG_INFO("Register values for EDN0:");
    } else if (base_addr == TOP_EARLGREY_EDN1_BASE_ADDR) {
      LOG_INFO("Register values for EDN1:");
    } else {
      LOG_ERROR("Unknown EDN base address!");
      return;
    }
    uint32_t ctrl = mmio_region_read32(edn_base, EDN_CTRL_REG_OFFSET);
    uint32_t status = mmio_region_read32(edn_base, EDN_SW_CMD_STS_REG_OFFSET);
    uint32_t intr_state = mmio_region_read32(edn_base, EDN_INTR_STATE_REG_OFFSET);
    uint32_t main_sm_state = mmio_region_read32(edn_base, EDN_MAIN_SM_STATE_REG_OFFSET);
    uint32_t reseed_cmd = mmio_region_read32(edn_base, EDN_RESEED_CMD_REG_OFFSET); 
    uint32_t sw_cmd_req = mmio_region_read32(edn_base, EDN_MAIN_SM_STATE_REG_OFFSET); 
    
    LOG_INFO("EDN_CTRL: 0x%x", ctrl);
    LOG_INFO("EDN_STATUS: 0x%x", status);
    LOG_INFO("SW_CMD_REQ: 0x%x", sw_cmd_req);
    LOG_INFO("EDN_INTR_STATE: 0x%x", intr_state);
    LOG_INFO("EDN_MAIN_SM_STATE: 0x%x", main_sm_state);
    LOG_INFO("EDN_RESEED_CMD: 0x%x", reseed_cmd);  // Log RESEED_CMD register
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
#endif

// AES key used for the test
static const unsigned char kAesModesKey128[16] = {
    0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
    0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c};
//static const unsigned char  kAesModesKey256[64] = {
//    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e,
//    0x11, 0x73, 0x93, 0x17, 0x2a, 0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03,
//    0xac, 0x9c, 0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51, 0x30,
//    0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11, 0xe5, 0xfb, 0xc1, 0x19,
//    0x1a, 0x0a, 0x52, 0xef, 0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f, 0x9b,
//    0x17, 0xad, 0x2b, 0x41, 0x7b, 0xe6, 0x6c, 0x37, 0x10};

static const unsigned char kAesModesPlainText[16] = {
    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 
    0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,};

static const unsigned char kAesModesCipherTextEcb128[16] = {
    0x3a, 0xd7, 0x7b, 0xb4, 0x0d, 0x7a, 0x36, 0x60, 
    0xa8, 0x9e, 0xca, 0xf3, 0x24, 0x66, 0xef, 0x97};

// The mask share, used to mask kKey. Note that the masking should not be done
// manually. Software is expected to get the key in two shares right from the
// beginning.
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
  LOG_INFO("");  // Print newline after the block
}

status_t execute_test(void) {
  // Initialize AES, EDN, CSRNG, and Entropy Source
  #if RESEED_TEST_EN
    LOG_INFO("Test with RESEED_TEST_EN ");
  #endif
  #if DEBUG_EN
    LOG_INFO("Test with DEBUG_EN ");
  #endif
  #if TRYSETTING1_EN
    LOG_INFO("Test with TRYSETTING1_EN ");
  #endif

  // Initialize all modules
  LOG_INFO("Initializing AES unit.");
  CHECK_DIF_OK(dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR),
                            &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes)); // Reset AES to a known state
  LOG_INFO("Module initialized: AES");
                                    
  #if RESEED_TEST_EN
    LOG_INFO("Starting AES PRNG reseed stall test with extra debug...");
    CHECK_DIF_OK(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
    CHECK_DIF_OK(dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
    CHECK_DIF_OK(dif_csrng_init(mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
    CHECK_DIF_OK(dif_entropy_src_init(mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
    LOG_INFO("Modules initialized: EDN0, EDN1, CSRNG, Entropy Source");
  #endif

  // Configure AES for ECB mode, 128-bit key, and manual operation
  dif_aes_transaction_t transaction = {
    .operation =
        kDifAesOperationEncrypt,  // Set the AES operation to encryption
    .mode =
        kDifAesModeEcb,  // Use Electronic Codebook (ECB) mode for encryption
    .key_len = kDifAesKey128,  // Use a 128-bit key for encryption
    //.key_len = kDifAesKey256,  // Use a 256-bit key for encryption
    .key_provider = kDifAesKeySoftwareProvided,  // The encryption key is
                                                 // provided by software
    //.mask_reseeding = kDifAesReseedPer64Block,   // Configure the PRNG to reseed
    //                                             // every 64 blocks
    .mask_reseeding = kDifAesReseedPerBlock,  // Resseed PRNG every block (128 bits)                                                 
    //operation, where it starts processing as soon as data is available
    //.manual_operation = kDifAesManualOperationAuto,  // Set AES to automatic
    .manual_operation =
        kDifAesManualOperationManual,  // Set AES to manual operation, where
                                       // software manually triggers the
                                       // operation
   .reseed_on_key_change = true,  // Enable PRNG reseeding every time the key
                                  // is changed (KEY_TOUCH_FORCES_RESEED)
   // Setting force_masks to false as per disucsseion
   .force_masks = false,     // Enable forced masking for the key (important for
                            // security during testing)
   .ctrl_aux_lock = false,  // Do not lock the auxiliary control settings,
                             // allowing further modifications
  };

  LOG_INFO("AES transaction configured: ECB mode, 128-bit key, manual operation.");

  #if RESEED_TEST_EN
    #if DEBUG_EN
      // Log CSRNG internal state after stopping
      // log_csrng_internal_state(&csrng);
      // status for entropy sources
      monitor_edn_registers(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR));
      monitor_edn_registers(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR));
      monitor_entropy_sources();
    #endif

    // Disable EDN and CSRNG to simulate stalling
    LOG_INFO("Disabling EDN0, EDN1...");
    CHECK_DIF_OK(dif_edn_stop(&edn0));
    CHECK_DIF_OK(dif_edn_stop(&edn1));
    //as per desc not here  LOG_INFO("Disabling CSRNG...");
    //as per desc not here  CHECK_DIF_OK(dif_csrng_stop(&csrng));
    //as per desc not here  CHECK_DIF_OK(dif_entropy_src_stop(&entropy_src));
  
    busy_spin_micros(500);  // Sleep for 500 microseconds

    LOG_INFO("Conditionally checking AES status after stopping EDN and CSRNG.");
    //AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusStall, true, kTestTimeout);
    LOG_INFO("Waiting for AES to stall after PRNG reseed request...");
    bool stall = false;
    CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusStall, &stall));
    
    if (stall) {
      LOG_INFO("AES encryption has stalled as expected.");
    } else {
      LOG_ERROR("AES encryption did not stall as expected after EDN stop! Lets proceed for now...");
      monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));  // Check AES status again
    }
  #endif

  #if DEBUG_EN
    log_csrng_internal_state(&csrng);
    monitor_edn_registers(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR));
    monitor_edn_registers(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR));
    monitor_entropy_sources();
  #endif

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

  // working alternative style// memcpy(key.share0, kAesModesKey128, sizeof(key.share0)); // Share 0 is the test key
  // working alternative style// memset(key.share1, 0, sizeof(key.share1));               // Share 1 is zero

  // T3:  Wait for status kDifAesStatusIdle
  // Start AES with the given transaction
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kTestTimeout);

  // T4: dif_aes_start
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, NULL));

  #if TRYSETTING1_EN
    LOG_INFO("Disabling CSRNG...");
    CHECK_DIF_OK(dif_csrng_stop(&csrng));
    CHECK_DIF_OK(dif_entropy_src_stop(&entropy_src));
    
    // Re-enable Entropy Source and CSRNG in the proper sequence
    LOG_INFO("Re-initializing Entropy Source and CSRNG...");
    
    // Initialize and configure Entropy Source
    dif_entropy_src_config_t entropy_src_config = entropy_testutils_config_default();
    CHECK_DIF_OK(dif_entropy_src_configure(&entropy_src, entropy_src_config, kDifToggleEnabled));  // Re-enable Entropy Source
    
    // Initialize and start CSRNG
    CHECK_DIF_OK(dif_csrng_configure(&csrng));  // Configure CSRNG
                                            //
    //set_edn_auto_mode();
    LOG_INFO("Setting EDN to auto mode...");
    TRY(entropy_testutils_auto_mode_init());
    //CHECK_DIF_OK(entropy_testutils_auto_mode_init());
    monitor_edn_status(&edn0, &edn1);
  #endif

  // Trigger PRNG reseed request
  LOG_INFO("Triggering PRNG reseed...");
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerPrngReseed));

  // T5: "Convert" plain data byte arrays to `dif_aes_data_t`
  dif_aes_data_t in_data_plain;
  memcpy(in_data_plain.data, kAesModesPlainText, sizeof(in_data_plain.data));

  // Monitor AES registers
  monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));

  // T6: Wait ofr Status kDifAesStatusIdle
  LOG_INFO("Now Starting AES encryption process firstly by observing if AES is in Idle state");
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                kTestTimeout);

  // T7: Wait for Status input DifAesStatusInputReady
  LOG_INFO("AES started: ECB encryption, waiting for input ready.");
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                               kTestTimeout);
  // T8: Load the plain text to trigger the encryption operation
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  // Trigger AES reseed request, specific for manual operation case as per documentation
  LOG_INFO("AES encryption started.");
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));
  // Monitor AES registers
  monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));

  #if RESEED_TEST_EN
    //nr TRY(entropy_testutils_boot_mode_init());
    //nr CHECK_STATUS_OK(aes_testutils_masking_prng_zero_output_seed());
    //nr busy_spin_micros(500);  // Sleep for 500 microseconds

    busy_spin_micros(500);  // Sleep for 500 microseconds
                            //
    #if DEBUG_EN
      // Log CSRNG internal state after stopping
      log_csrng_internal_state(&csrng);
      monitor_edn_registers(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR));
      monitor_edn_registers(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR));
      monitor_entropy_sources();

      // Check AES registers again after EDN stop
      LOG_INFO("AES registers:");
      monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));
    #endif

    // temp // // Wait for AES stall status
    // temp // LOG_INFO("Waiting for AES stall signal...");
    // temp // bool stall = false;
    // temp // 
    // temp // AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusStall, true, kTestTimeout);
    // temp // CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusStall, &stall));
    // temp // 
    // temp // if (stall) {
    // temp //   LOG_INFO("AES encryption stalled as expected due to EDN being disabled.");
    // temp // } else {
    // temp //   LOG_ERROR("AES encryption did not stall as expected.");
    // temp //   // Print AES registers again if stall did not occur
    // temp //   monitor_aes_registers(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR));
    // temp // }
    
    LOG_INFO("Disabling CSRNG...");
    CHECK_DIF_OK(dif_csrng_stop(&csrng));
    CHECK_DIF_OK(dif_entropy_src_stop(&entropy_src));
    
    // Re-enable Entropy Source and CSRNG in the proper sequence
    LOG_INFO("Re-initializing Entropy Source and CSRNG...");
    
    // Initialize and configure Entropy Source
    dif_entropy_src_config_t entropy_src_config_1 = entropy_testutils_config_default();
    CHECK_DIF_OK(dif_entropy_src_configure(&entropy_src, entropy_src_config_1, kDifToggleEnabled));  // Re-enable Entropy Source
    
    // Initialize and start CSRNG
    CHECK_DIF_OK(dif_csrng_configure(&csrng));  // Configure CSRNG
                                            //
    //set_edn_auto_mode();
    LOG_INFO("Setting EDN to auto mode...");
    TRY(entropy_testutils_auto_mode_init());
    //CHECK_DIF_OK(entropy_testutils_auto_mode_init());
    monitor_edn_status(&edn0, &edn1);
  #endif

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

  //
  return OK_STATUS();
}

bool test_main(void) {
  return status_ok(execute_test()); // Execute the test and return status
}

/*
 * Output of the test case run
I00001 ottf_main.c:154] Running sw/device/tests/aes_force_prng_reseed_test.c
I00002 aes_force_prng_reseed_test.c:193] Test with RESEED_TEST_EN 
I00003 aes_force_prng_reseed_test.c:199] Test with TRYSETTING1_EN 
I00004 aes_force_prng_reseed_test.c:203] Initializing AES unit.
I00005 aes_force_prng_reseed_test.c:207] Module initialized: AES
I00006 aes_force_prng_reseed_test.c:210] Starting AES PRNG reseed stall test with extra debug...
I00007 aes_force_prng_reseed_test.c:215] Modules initialized: EDN0, EDN1, CSRNG, Entropy Source
I00008 aes_force_prng_reseed_test.c:246] AES transaction configured: ECB mode, 128-bit key, manual operation.
I00009 aes_force_prng_reseed_test.c:259] Disabling EDN0, EDN1...
I00010 aes_force_prng_reseed_test.c:268] Conditionally checking AES status after stopping EDN and CSRNG.
I00011 aes_force_prng_reseed_test.c:270] Waiting for AES to stall after PRNG reseed request...
E00012 aes_force_prng_reseed_test.c:277] AES encryption did not stall as expected after EDN stop! Lets proceed for now...
I00013 aes_force_prng_reseed_test.c:64] REGISTER AES_CTRL_SHADOWED: 0x1481
I00014 aes_force_prng_reseed_test.c:65] REGISTER AES_CTRL_AUX_SHADOWED: 0x1
I00015 aes_force_prng_reseed_test.c:66] REGISTER AES_STATUS: 0x11
I00016 aes_force_prng_reseed_test.c:67] REGISTER AES_TRIGGER: 0x0
I00017 aes_force_prng_reseed_test.c:68] REGISTER AES_CTRL_AUX_REGWEN: 0x1
I00018 aes_force_prng_reseed_test.c:315] Disabling CSRNG...
I00019 aes_force_prng_reseed_test.c:320] Re-initializing Entropy Source and CSRNG...
I00020 aes_force_prng_reseed_test.c:330] Setting EDN to auto mode...
I00021 aes_force_prng_reseed_test.c:145] EDN0 status (Ready): 0x0
I00022 aes_force_prng_reseed_test.c:149] EDN1 status (Ready): 0x0
I00023 aes_force_prng_reseed_test.c:337] Triggering PRNG reseed...
I00024 aes_force_prng_reseed_test.c:64] REGISTER AES_CTRL_SHADOWED: 0x9105
I00025 aes_force_prng_reseed_test.c:65] REGISTER AES_CTRL_AUX_SHADOWED: 0x1
I00026 aes_force_prng_reseed_test.c:66] REGISTER AES_STATUS: 0x11
I00027 aes_force_prng_reseed_test.c:67] REGISTER AES_TRIGGER: 0x0
I00028 aes_force_prng_reseed_test.c:68] REGISTER AES_CTRL_AUX_REGWEN: 0x1
I00029 aes_force_prng_reseed_test.c:348] Now Starting AES encryption process firstly by observing if AES is in Idle state
I00030 aes_force_prng_reseed_test.c:353] AES started: ECB encryption, waiting for input ready.
I00031 aes_force_prng_reseed_test.c:360] AES encryption started.
I00032 aes_force_prng_reseed_test.c:64] REGISTER AES_CTRL_SHADOWED: 0x9105
I00033 aes_force_prng_reseed_test.c:65] REGISTER AES_CTRL_AUX_SHADOWED: 0x1
I00034 aes_force_prng_reseed_test.c:66] REGISTER AES_STATUS: 0x10
I00035 aes_force_prng_reseed_test.c:67] REGISTER AES_TRIGGER: 0x0
I00036 aes_force_prng_reseed_test.c:68] REGISTER AES_CTRL_AUX_REGWEN: 0x1
I00037 aes_force_prng_reseed_test.c:399] Disabling CSRNG...
I00038 aes_force_prng_reseed_test.c:404] Re-initializing Entropy Source and CSRNG...
I00039 aes_force_prng_reseed_test.c:414] Setting EDN to auto mode...
I00040 aes_force_prng_reseed_test.c:145] EDN0 status (Ready): 0x0
I00041 aes_force_prng_reseed_test.c:149] EDN1 status (Ready): 0x0
I00042 aes_force_prng_reseed_test.c:422] AES dif_aes_read_output:
I00043 aes_force_prng_reseed_test.c:425] Encrypted text:
I00044 aes_force_prng_reseed_test.c:185] 3a 
I00045 aes_force_prng_reseed_test.c:185] d7 
I00046 aes_force_prng_reseed_test.c:185] 7b 
I00047 aes_force_prng_reseed_test.c:185] b4 
I00048 aes_force_prng_reseed_test.c:185] 0d 
I00049 aes_force_prng_reseed_test.c:185] 7a 
I00050 aes_force_prng_reseed_test.c:185] 36 
I00051 aes_force_prng_reseed_test.c:185] 60 
I00052 aes_force_prng_reseed_test.c:185] a8 
I00053 aes_force_prng_reseed_test.c:185] 9e 
I00054 aes_force_prng_reseed_test.c:185] ca 
I00055 aes_force_prng_reseed_test.c:185] f3 
I00056 aes_force_prng_reseed_test.c:185] 24 
I00057 aes_force_prng_reseed_test.c:185] 66 
I00058 aes_force_prng_reseed_test.c:185] ef 
I00059 aes_force_prng_reseed_test.c:185] 97 
I00060 aes_force_prng_reseed_test.c:187] 
I00061 aes_force_prng_reseed_test.c:430] AES comparison out_data with CipherText:
I00062 ottf_main.c:109] Finished sw/device/tests/aes_force_prng_reseed_test.c
I00063 status.c:28] PASS!
*/
