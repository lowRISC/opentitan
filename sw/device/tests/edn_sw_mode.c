// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/edn_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "edn_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define TIMEOUT (10 * 1000 * 1000)
// AES with Domain-Oriented Masking (DOM) takes 72 cycles per 16B data
// block for a 256 bit key. Multiply this number by 20, to be on the safe side,
// to get the number of micro seconds for the timeout.
#define PLAIN_TEXT_BYTES (4 * 4)
#define TIMEOUT_AES (72 * (PLAIN_TEXT_BYTES / 16) * 20)

static dif_entropy_src_t entropy_src;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_aes_t aes;

OTTF_DEFINE_TEST_CONFIG();

// Initializes the peripherals used in this test.
static void init_peripherals(void) {
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
}

// Wrapper function for the AES_TESTUTILS_WAIT_FOR_STATUS macro.
static status_t aes_wait_for_status(dif_aes_status_t aes_state, bool flag,
                                    uint32_t timeout) {
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, aes_state, flag, timeout);
  return OK_STATUS();
}

// Generate bits in SW mode.
static void edn_generate_sw_bits(void) {
  dif_edn_seed_material_t seed0 = edn_testutils_seed_material_build(true);
  const dif_edn_entropy_src_toggle_t entropy_src_enable =
      kDifEdnEntropySrcToggleEnable;
  CHECK_DIF_OK(dif_edn_instantiate(&edn0, entropy_src_enable, &seed0));
  CHECK_DIF_OK(dif_edn_generate_start(&edn0, kDifEntropySeedMaterialMaxGlen));
}

// Configure the entropy complex.
static void entropy_config(void) {
  // Disable the entropy complex.
  CHECK_STATUS_OK(entropy_testutils_stop_all());
  // Enable ENTROPY_SRC in FIPS mode.
  CHECK_DIF_OK(dif_entropy_src_configure(
      &entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));
  // Enable CSRNG.
  CHECK_DIF_OK(dif_csrng_configure(&csrng));
  // Enable EDN1 in auto request mode. This does not generate entropy for AES.
  CHECK_DIF_OK(
      dif_edn_set_auto_mode(&edn1, edn_testutils_auto_params_build(true)));
  // Enable EDN0 in software port mode.
  CHECK_DIF_OK(dif_edn_configure(&edn0));
}

static void execute_test(void) {
  // Trigger the execution of AES to test EDN0. Consecutively,
  // verify that it hangs.
  LOG_INFO("aes_trigger_execution start");
  // Setup ECB encryption transaction.
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey256,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  CHECK_STATUS_OK(aes_testutils_setup_encryption(transaction, &aes));

  // Wait for AES to stall.
  status_t status = aes_wait_for_status(kDifAesStatusIdle, true, TIMEOUT_AES);

  // We only care about the MSB and the 5 LSB.
  // MSB is the error flag and the 5 LSB are the error code.
  bool error_flag = (status.value >> 31) & 0x1;
  absl_status_t error_code = status.value & 0x1f;
  CHECK(error_flag && (error_code == kDeadlineExceeded));

  // Provide the required commands to EDN0, via SW_CMD_REQ register,
  // to start generating and delivering entropy to AES.
  LOG_INFO("edn_generate_sw_bits start");
  edn_generate_sw_bits();
  aes_wait_for_status(kDifAesStatusOutputValid, true, TIMEOUT);

  CHECK_STATUS_OK(aes_testutils_decrypt_ciphertext(transaction, &aes));
}

bool test_main(void) {
  LOG_INFO("init_peripherals start");
  init_peripherals();
  // Disable and restart the entropy complex.
  LOG_INFO("entropy_config start");
  entropy_config();
  // Execute the main body of the test.
  execute_test();
  return true;
}
