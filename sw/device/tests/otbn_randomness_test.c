// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "devicetables.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/otbn_randomness_impl.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kPlicTarget = 0,
};

static dif_clkmgr_t clkmgr;
static const dif_clkmgr_hintable_clock_t kOtbnClock =
    kTopEarlgreyHintableClocksMainOtbn;

static const dt_otbn_t *kOtbnDt = &kDtOtbn[0];
static const dt_rv_plic_t *kRvPlicDt = &kDtRvPlic[0];
static const dt_clkmgr_t *kClkmgrDt = &kDtClkmgr[0];
static dif_rv_plic_t plic;
static dif_otbn_t otbn;
/**
 * These variables are used for ISR communication hence they are volatile.
 */
static volatile bool irq_otbn_done;

/**
 * Provides external IRQ handling for otbn tests.
 *
 * This function overrides the default OTTF external ISR.
 *
 * It performs the following:
 * 1. Claims the IRQ fired (finds PLIC IRQ index).
 * 2. Compute the OTBN peripheral.
 * 3. Compute the otbn irq.
 * 4. Clears the IRQ at the peripheral.
 * 5. Completes the IRQ service at PLIC.
 */
void ottf_external_isr(uint32_t *exc_info) {
  dif_rv_plic_irq_id_t irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  if (irq_id == dt_otbn_irq_to_plic_id(kOtbnDt, kDtOtbnIrqDone)) {
    irq_otbn_done = true;
  }

  // Otbn clock is disabled, so we can not acknowledge the irq. Disabling it to
  // avoid an infinite loop here.
  irq_global_ctrl(false);
  irq_external_ctrl(false);

  // Complete the IRQ by writing the IRQ source to the Ibex register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));
}

static void otbn_wait_for_done_irq(dif_otbn_t *otbn) {
  // Clear the otbn irq variable: we'll set it in the interrupt handler when
  // we see the Done interrupt fire.
  irq_otbn_done = false;
  CHECK_DIF_OK(
      dif_otbn_irq_set_enabled(otbn, kDifOtbnIrqDone, kDifToggleEnabled));

  // OTBN should be running. Wait for an interrupt that says
  // it's done.
  ATOMIC_WAIT_FOR_INTERRUPT(irq_otbn_done);
}

static void otbn_init_irq(void) {
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &plic));

  // Set interrupt priority to be positive.
  dif_rv_plic_irq_id_t irq_id = dt_otbn_irq_to_plic_id(kOtbnDt, kDtOtbnIrqDone);
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&plic, irq_id, 0x1));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&plic, irq_id, kPlicTarget,
                                           kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&plic, kPlicTarget, 0x0));

  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

status_t initialize_clkmgr(void) {
  CHECK_DIF_OK(dif_clkmgr_init_from_dt(kClkmgrDt, &clkmgr));

  // Get initial hint and enable for OTBN clock and check both are enabled.
  dif_toggle_t clock_hint_state;
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_hint(&clkmgr, kOtbnClock,
                                                  &clock_hint_state));
  CHECK(clock_hint_state == kDifToggleEnabled);
  return CLKMGR_TESTUTILS_CHECK_CLOCK_HINT(clkmgr, kOtbnClock,
                                           kDifToggleEnabled);
}

status_t execute_test(void) {
  // Write the OTBN clk hint to 0 within clkmgr to indicate OTBN clk can be
  // gated and verify that the OTBN clk hint status within clkmgr reads 0 (OTBN
  // is idle).
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kOtbnClock, kDifToggleDisabled, kDifToggleDisabled);

  // Write the OTBN clk hint to 1 within clkmgr to indicate OTBN clk can be
  // enabled.
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kOtbnClock, kDifToggleEnabled, kDifToggleEnabled);

  // Start an OTBN operation, write the OTBN clk hint to 0 within clkmgr and
  // verify that the OTBN clk hint status within clkmgr reads 1 (OTBN is not
  // idle).
  otbn_randomness_test_start(&otbn, /*iters=*/0);

  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kOtbnClock, kDifToggleDisabled, kDifToggleEnabled);

  // After the OTBN operation is complete, verify that the OTBN clk hint status
  // within clkmgr now reads 0 again (OTBN is idle).
  otbn_wait_for_done_irq(&otbn);
  CLKMGR_TESTUTILS_CHECK_CLOCK_HINT(clkmgr, kOtbnClock, kDifToggleDisabled);

  // Write the OTBN clk hint to 1, read and check the OTBN output for
  // correctness.
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kOtbnClock, kDifToggleEnabled, kDifToggleEnabled);

  otbn_randomness_test_log_results(&otbn);

  // Check for successful test execution (self-reported).
  TRY_CHECK(otbn_randomness_test_end(&otbn, /*skip_otbn_done_check=*/true));
  return OK_STATUS();
}

bool test_main(void) {
  // Initialize EDN in auto mode.
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  CHECK_STATUS_OK(initialize_clkmgr());

  CHECK_DIF_OK(dif_otbn_init_from_dt(kOtbnDt, &otbn));

  otbn_init_irq();
  return status_ok(execute_test());
}
