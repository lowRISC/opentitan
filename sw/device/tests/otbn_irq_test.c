// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top/dt/api.h"
#include "hw/top/dt/otbn.h"
#include "hw/top/dt/rv_plic.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTBN_DECLARE_APP_SYMBOLS(err_test);

static const otbn_app_t kAppErrTest = OTBN_APP_T_INIT(err_test);
static const uint32_t kPlicTarget = 0;

OTTF_DEFINE_TEST_CONFIG();

static dif_rv_plic_t plic;
static dif_otbn_t otbn;
static dt_otbn_t kOtbnDt = (dt_otbn_t)0;

static volatile bool otbn_finished;

/**
 * Get OTBN error bits; check they match expected_err_bits.
 */
static void check_otbn_err_bits(dif_otbn_t *otbn,
                                dif_otbn_err_bits_t expected_err_bits) {
  dif_otbn_err_bits_t otbn_err_bits;
  CHECK_DIF_OK(dif_otbn_get_err_bits(otbn, &otbn_err_bits));
  CHECK(otbn_err_bits == expected_err_bits,
        "dif_otbn_get_err_bits() produced unexpected error bits: %x",
        otbn_err_bits);
}

/**
 * Get the OTBN instruction count; check that it matches expected_insn_cnt.
 */
static void check_otbn_insn_cnt(dif_otbn_t *otbn, uint32_t expected_insn_cnt) {
  uint32_t insn_cnt;
  CHECK_DIF_OK(dif_otbn_get_insn_cnt(otbn, &insn_cnt));
  CHECK(insn_cnt == expected_insn_cnt,
        "Expected to execute %d instructions, but got %d.", expected_insn_cnt,
        insn_cnt);
}

/**
 * Get OTBN's status; check that it matches expected_status.
 */
static void check_otbn_status(dif_otbn_t *otbn,
                              dif_otbn_status_t expected_status) {
  dif_otbn_status_t status;
  CHECK_DIF_OK(dif_otbn_get_status(otbn, &status));
  CHECK(status == expected_status, "Unexpected status: expected %d but got %d.",
        expected_status, status);
}

/**
 * Run a binary on OTBN, waiting for completion by interrupt.
 *
 * Once the binary has finished, check for expected status, error bits and
 * instruction count.
 */
static void run_test_with_irqs(dif_otbn_t *otbn, otbn_app_t app,
                               dif_otbn_status_t expected_status,
                               dif_otbn_err_bits_t expected_err_bits,
                               uint32_t expected_insn_cnt) {
  // Clear the otbn_finished flag: we'll set it in the interrupt handler when
  // we see the Done interrupt fire.
  otbn_finished = false;

  // Expect the recoverable error alert only if errors are expected.
  if (expected_err_bits != kDifOtbnErrBitsNoError) {
    CHECK_STATUS_OK(ottf_alerts_expect_alert_start(
        dt_otbn_alert_to_alert_id(kOtbnDt, kDtOtbnAlertRecov)));
  }

  CHECK_STATUS_OK(otbn_testutils_load_app(otbn, app));

  // If the CTRL.SOFTWARE_ERRS_FATAL flag is set, a software error will be
  // promoted to a fatal error (which, among other things, bricks OTBN until
  // next reset). Make sure that's not turned on.
  CHECK(dif_otbn_set_ctrl_software_errs_fatal(otbn, false) == kDifOk);

  // Enable Done interrupt
  CHECK_DIF_OK(
      dif_otbn_irq_set_enabled(otbn, kDifOtbnIrqDone, kDifToggleEnabled));

  // Start OTBN
  CHECK_STATUS_OK(otbn_testutils_execute(otbn));

  // At this point, OTBN should be running. Wait for an interrupt that says
  // it's done.
  ATOMIC_WAIT_FOR_INTERRUPT(otbn_finished);

  if (expected_err_bits != kDifOtbnErrBitsNoError) {
    CHECK_STATUS_OK(ottf_alerts_expect_alert_finish(
        dt_otbn_alert_to_alert_id(kOtbnDt, kDtOtbnAlertRecov)));
  }

  check_otbn_status(otbn, expected_status);
  check_otbn_err_bits(otbn, expected_insn_cnt);
  check_otbn_insn_cnt(otbn, expected_err_bits);
}

/**
 * Initialize PLIC and enable OTBN interrupt.
 */
static void plic_init_with_irqs(void) {
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kDtRvPlic, &plic));

  dif_rv_plic_irq_id_t irq_id = dt_otbn_irq_to_plic_id(kOtbnDt, kDtOtbnIrqDone);

  // Set interrupt priority to be positive
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&plic, irq_id, 0x1));

  // Enable the interrupt
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&plic, irq_id, kPlicTarget,
                                           kDifToggleEnabled));

  // Set the threshold for Ibex to 0.
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&plic, kPlicTarget, 0x0));
}

/**
 * The ISR for this test.
 *
 * This function overrides the default OTTF external ISR.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid != dt_otbn_instance_id(kOtbnDt)) {
    return false;
  }

  // Check this is the interrupt we expected
  dif_otbn_irq_t otbn_irq = dt_otbn_irq_from_plic_id(kOtbnDt, irq_id);
  if (otbn_irq != kDtOtbnIrqDone) {
    return false;
  }

  // otbn_finished should currently be false (we're supposed to clear it before
  // starting OTBN)
  CHECK(!otbn_finished);

  // Set otbn_finished, which we'll pick up in run_test_with_irqs.
  otbn_finished = true;

  CHECK_DIF_OK(dif_otbn_irq_acknowledge(&otbn, otbn_irq));

  return true;
}

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  plic_init_with_irqs();

  CHECK_DIF_OK(dif_otbn_init_from_dt(kOtbnDt, &otbn));

  // Enable the external IRQ (so that we see the interrupt from the PLIC)
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  run_test_with_irqs(&otbn, kAppErrTest, kDifOtbnStatusIdle,
                     kDifOtbnErrBitsBadDataAddr, 1);

  return true;
}
