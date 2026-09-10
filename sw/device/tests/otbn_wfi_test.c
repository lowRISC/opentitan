// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

/**
 * This test exercises OTBN's WFI (Wait For Interrupt) instruction.
 * The simple OTBN test program sw/otbn/wif/wfi_test.s is run (see its code for
 * the test details). The host waits for the first pause by polling and for the
 * 2nd pause by waiting for the DONE interrupt.
 */
OTTF_DEFINE_TEST_CONFIG();

OTBN_DECLARE_APP_SYMBOLS(wfi_test);
OTBN_DECLARE_SYMBOL_ADDR(wfi_test, input);
OTBN_DECLARE_SYMBOL_ADDR(wfi_test, output);

static const otbn_app_t kAppWfiTest = OTBN_APP_T_INIT(wfi_test);
static const otbn_addr_t kInput = OTBN_ADDR_T_INIT(wfi_test, input);
static const otbn_addr_t kOutput = OTBN_ADDR_T_INIT(wfi_test, output);

// The two random / magic values the host writes to DMEM.
static const uint32_t kMagic1Value = 0xf00dcafe;
static const uint32_t kMagic2Value = 0xdeadbeef;

/**
 * Waits until OTBN stops executing the current program.
 *
 * First waits for the EXECUTE command to take effect (OTBN leaves IDLE), then
 * waits until OTBN is no longer busy executing. It stops executing because it
 * either paused on a WFI, finished, or locked up.
 */
static status_t otbn_wait_while_executing(const dif_otbn_t *otbn,
                                          dif_otbn_status_t *status) {
  do {
    TRY(dif_otbn_get_status(otbn, status));
  } while (*status == kDifOtbnStatusIdle);
  while (*status == kDifOtbnStatusBusyExecute) {
    TRY(dif_otbn_get_status(otbn, status));
  }
  return OK_STATUS();
}

bool test_main(void) {
  dif_otbn_t otbn;
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  CHECK_DIF_OK(dif_otbn_init_from_dt(kDtOtbn, &otbn));

  // Clear any stale interrupt state so we can observe the WFI-driven pause.
  CHECK_DIF_OK(dif_otbn_irq_acknowledge_all(&otbn));

  // Load the app.
  CHECK_STATUS_OK(otbn_testutils_load_app(&otbn, kAppWfiTest));

  // Enable OTBN's WFI instruction.
  CHECK_DIF_OK(dif_otbn_set_ctrl_wfi_enable(&otbn, true));

  // Write the 1st value to DMEM.
  CHECK_STATUS_OK(otbn_testutils_write_data(&otbn, sizeof(kMagic1Value),
                                            &kMagic1Value, kInput));

  // Start execution.
  CHECK_STATUS_OK(otbn_testutils_execute(&otbn));

  // Wait for OTBN to stop executing and confirm it entered the PAUSED state.
  dif_otbn_status_t status;
  CHECK_STATUS_OK(otbn_wait_while_executing(&otbn, &status));
  CHECK(status == kDifOtbnStatusPaused,
        "OTBN did not pause on WFI, status = 0x%x", status);

  // Check that the WFI instruction raised the `done` interrupt.
  bool irq_pending;
  CHECK_DIF_OK(dif_otbn_irq_is_pending(&otbn, kDifOtbnIrqDone, &irq_pending));
  CHECK(irq_pending, "OTBN did not raise the done interrupt when pausing.");
  CHECK_DIF_OK(dif_otbn_irq_acknowledge(&otbn, kDifOtbnIrqDone));

  // Read back the copied input value
  uint32_t output;
  CHECK_STATUS_OK(
      otbn_testutils_read_data(&otbn, sizeof(output), kOutput, &output));
  CHECK(output == kMagic1Value, "DMEM output = 0x%08x, expected 0x%08x", output,
        kMagic1Value);

  // Write the 2nd magic value into `input`. Then resume execution.
  CHECK_STATUS_OK(otbn_testutils_write_data(&otbn, sizeof(kMagic2Value),
                                            &kMagic2Value, kInput));

  CHECK_DIF_OK(dif_otbn_write_cmd(&otbn, kDifOtbnCmdResume));

  // Wait on the done interrupt until OTBN pauses again on the 2nd WFI. We
  // acknowledged the interrupt after the 1st pause, so a fresh pending done
  // signals the 2nd pause.
  do {
    CHECK_DIF_OK(dif_otbn_irq_is_pending(&otbn, kDifOtbnIrqDone, &irq_pending));
  } while (!irq_pending);

  // Check if OTBN is paused and did not finish or lock up.
  CHECK_DIF_OK(dif_otbn_get_status(&otbn, &status));
  CHECK(status == kDifOtbnStatusPaused,
        "OTBN did not pause on the 2nd WFI, status = 0x%x", status);
  CHECK_DIF_OK(dif_otbn_irq_acknowledge(&otbn, kDifOtbnIrqDone));

  // Check if the 2nd value was copied.
  CHECK_STATUS_OK(
      otbn_testutils_read_data(&otbn, sizeof(output), kOutput, &output));
  CHECK(output == kMagic2Value, "DMEM output = 0x%08x, expected 0x%08x", output,
        kMagic2Value);

  // Resume execution and wait for the program to finish without errors.
  CHECK_DIF_OK(dif_otbn_write_cmd(&otbn, kDifOtbnCmdResume));
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(&otbn, kDifOtbnErrBitsNoError));

  LOG_INFO("OTBN WFI test passed: paused and resumed correctly.");
  return true;
}
