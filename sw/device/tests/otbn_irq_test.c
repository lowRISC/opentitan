// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTBN_DECLARE_APP_SYMBOLS(err_test);

static const otbn_app_t kAppErrTest = OTBN_APP_T_INIT(err_test);

const test_config_t kTestConfig;

static dif_rv_plic_t plic;
static volatile bool otbn_finished;

/**
 * Get OTBN error bits; check they match expected_err_bits.
 */
static void check_otbn_err_bits(otbn_t *otbn_ctx,
                                dif_otbn_err_bits_t expected_err_bits) {
  dif_otbn_err_bits_t otbn_err_bits;
  CHECK_DIF_OK(dif_otbn_get_err_bits(&otbn_ctx->dif, &otbn_err_bits));
  CHECK(otbn_err_bits == expected_err_bits,
        "dif_otbn_get_err_bits() produced unexpected error bits: %x",
        otbn_err_bits);
}

/**
 * Get the OTBN instruction count; check that it matches expected_insn_cnt.
 */
static void check_otbn_insn_cnt(otbn_t *otbn_ctx, uint32_t expected_insn_cnt) {
  uint32_t insn_cnt;
  CHECK_DIF_OK(dif_otbn_get_insn_cnt(&otbn_ctx->dif, &insn_cnt));
  CHECK(insn_cnt == expected_insn_cnt,
        "Expected to execute %d instructions, but got %d.", expected_insn_cnt,
        insn_cnt);
}

/**
 * Get OTBN's status; check that it matches expected_status.
 */
static void check_otbn_status(otbn_t *otbn_ctx,
                              dif_otbn_status_t expected_status) {
  dif_otbn_status_t status;
  CHECK_DIF_OK(dif_otbn_get_status(&otbn_ctx->dif, &status));
  CHECK(status == expected_status, "Unexpected status: expected %d but got %d.",
        expected_status, status);
}

/**
 * Run a binary on OTBN, waiting for completion by interrupt.
 *
 * Once the binary has finished, check for expected status, error bits and
 * instruction count.
 */
static void run_test_with_irqs(otbn_t *otbn_ctx, otbn_app_t app,
                               dif_otbn_status_t expected_status,
                               dif_otbn_err_bits_t expected_err_bits,
                               uint32_t expected_insn_cnt) {
  // Clear the otbn_finished flag: we'll set it in the interrupt handler when
  // we see the Done interrupt fire.
  otbn_finished = false;

  CHECK(otbn_load_app(otbn_ctx, app) == kOtbnOk);

  // If the the CTRL.SOFTWARE_ERRS_FATAL flag is set, a software error will be
  // promoted to a fatal error (which, among other things, bricks OTBN until
  // next reset). Make sure that's not turned on.
  CHECK(dif_otbn_set_ctrl_software_errs_fatal(&otbn_ctx->dif, false) == kDifOk);

  // Enable Done interrupt
  CHECK_DIF_OK(dif_otbn_irq_set_enabled(&otbn_ctx->dif, kDifOtbnIrqDone,
                                        kDifToggleEnabled));

  // Start OTBN
  CHECK(otbn_execute(otbn_ctx) == kOtbnOk);

  // At this point, OTBN should be running. Wait for an interrupt that says
  // it's done.
  for (;;) {
    // This looks a bit odd, but is needed to avoid a race condition where the
    // OTBN interrupt comes in after we load the otbn_finished flag but before
    // we run the WFI instruction. The trick is that WFI returns when an
    // interrupt comes in even if interrupts are globally disabled, which means
    // that the WFI can actually sit *inside* the critical section.
    irq_global_ctrl(false);
    if (otbn_finished)
      break;
    wait_for_interrupt();
    irq_global_ctrl(true);
  }
  irq_global_ctrl(true);

  check_otbn_status(otbn_ctx, expected_status);
  check_otbn_err_bits(otbn_ctx, expected_insn_cnt);
  check_otbn_insn_cnt(otbn_ctx, expected_err_bits);
}

/**
 * Initialize PLIC and enable OTBN interrupt.
 */
static void plic_init_with_irqs(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));

  dif_rv_plic_irq_id_t irq_id = kTopEarlgreyPlicIrqIdOtbnDone;

  // Set interrupt priority to be positive
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&plic, irq_id, 0x1));

  // Enable the interrupt
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      &plic, irq_id, kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));

  // Set the threshold for Ibex to 0.
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(
      &plic, kTopEarlgreyPlicTargetIbex0, 0x0));
}

/**
 * The ISR for this test.
 *
 * This function overrides the default OTTF external ISR.
 */
void ottf_external_isr(void) {
  // Find which interrupt fired at PLIC by claiming it.
  dif_rv_plic_irq_id_t irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(&plic, kTopEarlgreyPlicTargetIbex0, &irq_id));

  // Check it was from OTBN
  top_earlgrey_plic_peripheral_t peri =
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];
  CHECK(peri == kTopEarlgreyPlicPeripheralOtbn,
        "Interrupt from incorrect peripheral: (exp: %d, obs: %s)",
        kTopEarlgreyPlicPeripheralOtbn, peri);

  // Check this is the interrupt we expected
  CHECK(irq_id == kTopEarlgreyPlicIrqIdOtbnDone);

  // otbn_finished should currently be false (we're supposed to clear it before
  // starting OTBN)
  CHECK(!otbn_finished);

  // Set otbn_finished, which we'll pick up in run_test_with_irqs.
  otbn_finished = true;
}

bool test_main() {
  entropy_testutils_boot_mode_init();
  plic_init_with_irqs();

  // Enable the external IRQ (so that we see the interrupt from the PLIC)
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  mmio_region_t base_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR);

  otbn_t otbn_ctx;
  CHECK(otbn_init(&otbn_ctx, base_addr) == kOtbnOk);

  run_test_with_irqs(&otbn_ctx, kAppErrTest, kDifOtbnStatusIdle,
                     kDifOtbnErrBitsBadDataAddr, 1);

  return true;
}
