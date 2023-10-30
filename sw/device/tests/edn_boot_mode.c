// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/edn_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/otbn_randomness_impl.h"

#include "edn_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kEdnBootModeTimeout = (10 * 1000 * 1000),
  kEdnBootModeOtbnRandomnessIterations = 1,
};

static dif_entropy_src_t entropy_src;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_otbn_t otbn;
static dif_rv_core_ibex_t rv_core_ibex;

dif_entropy_src_config_t entropy_src_config = {
    .fips_enable = false,
    .route_to_firmware = false,
    .bypass_conditioner = false,
    .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
    .health_test_window_size = 0x0200,
    .alert_threshold = 2,
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
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));
}

static void configure_otbn(void) {
  otbn_randomness_test_prepare(&otbn, kEdnBootModeOtbnRandomnessIterations);
}

// configure the entropy complex
static status_t entropy_config(unsigned int round) {
  // EDN params with high values for glen so we don't have to reseed.
  dif_edn_auto_params_t edn_params0 = edn_testutils_auto_params_build(
      true, /*res_itval=*/32, /*glen_val=*/4095);
  dif_edn_auto_params_t edn_params1 = edn_testutils_auto_params_build(
      true, /*res_itval=*/32, /*glen_val=*/4095);
  // Disable the entropy complex.
  TRY(entropy_testutils_stop_all());
  // Enable ENTROPY_SRC in Non-FIPS/FIPS mode based on the value of round.
  entropy_src_config.fips_enable = (round != 1);
  CHECK_DIF_OK(dif_entropy_src_configure(&entropy_src, entropy_src_config,
                                         kDifToggleEnabled));
  // Enable CSRNG.
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  if (round == 1) {
    // Enable EDN1 (the one connected to OTBN RND) in boot-time request mode.
    CHECK_DIF_OK(dif_edn_set_boot_mode(&edn1));
    CHECK_DIF_OK(dif_edn_configure(&edn1));
    EDN_TESTUTILS_WAIT_FOR_STATUS(&edn1, kDifEdnSmStateBootGenAckWait, true,
                                  kEdnBootModeTimeout);
    // Re-enable ENTROPY_SRC in FIPS mode.
    CHECK_DIF_OK(dif_entropy_src_stop(&entropy_src));
    entropy_src_config.fips_enable = true;
    CHECK_DIF_OK(dif_entropy_src_configure(&entropy_src, entropy_src_config,
                                           kDifToggleEnabled));
    // Enable EDN0 in auto request mode.
    CHECK_DIF_OK(dif_edn_set_auto_mode(&edn0, edn_params0));
  }

  if (round == 2) {
    // Enable EDN1 (the one connected to OTBN RND) in auto request mode.
    CHECK_DIF_OK(dif_edn_set_auto_mode(&edn1, edn_params1));
    EDN_TESTUTILS_WAIT_FOR_STATUS(&edn1, kDifEdnSmStateAutoAckWait, true,
                                  kEdnBootModeTimeout);
    // Re-enable ENTROPY_SRC in Non-FIPS mode.
    CHECK_DIF_OK(dif_entropy_src_stop(&entropy_src));
    entropy_src_config.fips_enable = false;
    CHECK_DIF_OK(dif_entropy_src_configure(&entropy_src, entropy_src_config,
                                           kDifToggleEnabled));
    // Enable EDN0 in boot-time request mode.
    CHECK_DIF_OK(dif_edn_set_boot_mode(&edn0));
    CHECK_DIF_OK(dif_edn_configure(&edn0));
    EDN_TESTUTILS_WAIT_FOR_STATUS(&edn0, kDifEdnSmStateBootGenAckWait, true,
                                  kEdnBootModeTimeout);
  }

  if (round == 3) {
    // Enable both EDNs in auto request mode.
    CHECK_DIF_OK(dif_edn_set_auto_mode(&edn0, edn_params0));
    CHECK_DIF_OK(dif_edn_set_auto_mode(&edn1, edn_params1));
  }

  return OK_STATUS();
}

static void consume_entropy(unsigned int round,
                            dif_otbn_err_bits_t otbn_err_val,
                            dif_rv_core_ibex_rnd_status_t ibex_rnd_fips) {
  uint32_t ibex_rnd_data;
  dif_rv_core_ibex_rnd_status_t ibex_rnd_status;
  dif_otbn_irq_state_snapshot_t intr_state;
  CHECK_STATUS_OK(entropy_config(round));
  // Launch an OTBN program consuming entropy via both
  // the RND and the URND interface.
  CHECK_STATUS_OK(otbn_testutils_execute(&otbn));
  // Verify that the OTBN finishes with the expected error values
  // and interrupt flags.
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(&otbn, otbn_err_val));
  CHECK_DIF_OK(dif_otbn_irq_get_state(&otbn, &intr_state));
  CHECK(intr_state & 0x1);
  CHECK_DIF_OK(dif_otbn_irq_acknowledge_all(&otbn));
  // Read rnd data through the IBEX and verify if the FIPS compliance
  // status is as expected.
  // The first read gets rid of leftover entropy from previous configurations
  // of the entropy complex.
  CHECK_DIF_OK(dif_rv_core_ibex_read_rnd_data(&rv_core_ibex, &ibex_rnd_data));
  IBEX_SPIN_FOR(rv_core_ibex_testutils_is_rnd_data_valid(&rv_core_ibex),
                kEdnBootModeTimeout);
  CHECK_DIF_OK(
      dif_rv_core_ibex_get_rnd_status(&rv_core_ibex, &ibex_rnd_status));
  // The second read now contains the entropy from the current configuration.
  CHECK_DIF_OK(dif_rv_core_ibex_read_rnd_data(&rv_core_ibex, &ibex_rnd_data));
  CHECK((ibex_rnd_status & kDifRvCoreIbexRndStatusFipsCompliant) ==
        ibex_rnd_fips);
}

bool test_main(void) {
  init_peripherals();
  // Prepare the OTBN for execution.
  configure_otbn();
  // Run the Procedure and check if EDN1 produces FIPS non-compliant entropy.
  consume_entropy(/*round=*/1, kDifOtbnErrBitsRndFipsChkFail,
                  kDifRvCoreIbexRndStatusFipsCompliant);
  // Run the Procedure and check if EDN0 produces FIPS non-compliant entropy.
  consume_entropy(/*round=*/2, kDifOtbnErrBitsNoError, 0);
  // Run the Procedure and check if both EDNs produce FIPS compliant entropy.
  consume_entropy(/*round=*/3, kDifOtbnErrBitsNoError,
                  kDifRvCoreIbexRndStatusFipsCompliant);

  return true;
}
