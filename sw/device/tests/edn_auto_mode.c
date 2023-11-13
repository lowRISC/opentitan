// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/edn_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/otbn_randomness_impl.h"

#include "edn_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kTimeout = (10 * 1000 * 1000),
  kOtbnRounds = 2,
  kOtbnRandomnessIterations = 1,
  kTestProcedureRepetitions = 2,
};

static dif_entropy_src_t entropy_src;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_aes_t aes;
static dif_otbn_t otbn;
static dif_rv_core_ibex_t rv_core_ibex;

// AES ECB encryption transaction.
static dif_aes_transaction_t transaction = {
    .operation = kDifAesOperationEncrypt,
    .mode = kDifAesModeEcb,
    .key_len = kDifAesKey256,
    .key_provider = kDifAesKeySoftwareProvided,
    .mask_reseeding = kDifAesReseedPerBlock,
    .manual_operation = kDifAesManualOperationAuto,
    .reseed_on_key_change = true,
    .ctrl_aux_lock = false,
};

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
  CHECK_DIF_OK(
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));
}

static void configure_otbn(void) {
  otbn_randomness_test_prepare(&otbn, kOtbnRandomnessIterations);
}

// configure the entropy complex
static void entropy_config(void) {
  dif_edn_auto_params_t edn_params0 =
      edn_testutils_auto_params_build(false, /*res_itval=*/0, /*glen_val=*/0);
  dif_edn_auto_params_t edn_params1 =
      edn_testutils_auto_params_build(false, /*res_itval=*/0, /*glen_val=*/0);
  // Disable the entropy complex
  CHECK_STATUS_OK(entropy_testutils_stop_all());
  // Enable ENTROPY_SRC in FIPS mode
  CHECK_DIF_OK(dif_entropy_src_configure(
      &entropy_src, entropy_testutils_config_default(), kDifToggleEnabled));
  // Enable CSRNG
  CHECK_DIF_OK(dif_csrng_configure(&csrng));
  // Enable EDNs in auto request mode
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn0, edn_params0));
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn1, edn_params1));
  CHECK_DIF_OK(dif_aes_reset(&aes));
}

static status_t stress_test_edns(void) {
  int otbn_execute_rounds = kOtbnRounds;
  dif_rv_core_ibex_rnd_status_t ibex_rnd_status;
  dif_otbn_status_t otbn_status;
  uint32_t ibex_rnd_data;
  dif_aes_data_t out_data;
  // Start AES at least once.
  LOG_INFO("aes_testutils_setup_encryption round %d", otbn_execute_rounds);
  CHECK_STATUS_OK(aes_testutils_setup_encryption(transaction, &aes));
  while (otbn_execute_rounds) {
    LOG_INFO("dif_otbn_get_status round %d", otbn_execute_rounds);
    CHECK_DIF_OK(dif_otbn_get_status(&otbn, &otbn_status));
    if (otbn_status == kDifOtbnStatusIdle) {
      LOG_INFO("otbn_testutils_execute round %d", otbn_execute_rounds);
      CHECK_STATUS_OK(otbn_testutils_execute(&otbn));
      otbn_execute_rounds--;
    }
    if (aes_testutils_get_status(&aes, kDifAesStatusOutputValid)) {
      LOG_INFO("dif_aes_read_output round %d", otbn_execute_rounds);
      // Read out the produced cipher text.
      CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data));
      LOG_INFO("aes_testutils_setup_encryption round %d", otbn_execute_rounds);
      // Start a new AES encryption.
      CHECK_STATUS_OK(aes_testutils_setup_encryption(transaction, &aes));
    }

    CHECK_DIF_OK(
        dif_rv_core_ibex_get_rnd_status(&rv_core_ibex, &ibex_rnd_status));
    if (ibex_rnd_status == kDifRvCoreIbexRndStatusValid)
      CHECK_DIF_OK(
          dif_rv_core_ibex_read_rnd_data(&rv_core_ibex, &ibex_rnd_data));
  }
  // Verify that all entropy consuming endpoints can finish their operations
  // and do not hang.
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(&otbn, kDifOtbnErrBitsNoError));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true, kTimeout);
  IBEX_TRY_SPIN_FOR(rv_core_ibex_testutils_is_rnd_data_valid(&rv_core_ibex),
                    kTimeout);

  return OK_STATUS();
}

bool test_main(void) {
  int repetitions = kTestProcedureRepetitions;
  LOG_INFO("init_peripherals start");
  init_peripherals();
  // Prepare the OTBN for execution.
  configure_otbn();
  // Start the procedure multiple times, with different EDN configurations.
  while (repetitions) {
    // Disable and restart the entropy complex.
    LOG_INFO("entropy_config start");
    entropy_config();
    // Trigger the execution of the OTBN, AES and IBEX, consuming entropy
    // to stress test the EDNs.
    LOG_INFO("stress_test_edns start");
    stress_test_edns();
    repetitions--;
  }

  return true;
}
