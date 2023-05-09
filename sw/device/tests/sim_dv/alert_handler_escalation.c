// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "alert_handler_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"  // Generated.

/*
  - Verify the first escalation results in NMI interrupt serviced by the CPU.
  - Verify the second results in device being put in escalate state, via the LC
  JTAG TAP.
  - Verify the third results in chip reset.
  - Ensure that all escalation handshakes complete without errors.

  The first escalation is checked via the entry of the NMI handler and polling
  by dv. The second escalation is directly checked by dv. The third escalation
  is checked via reset reason.
 */

OTTF_DEFINE_TEST_CONFIG();

static dif_clkmgr_t clkmgr;
static dif_keymgr_t keymgr;
static dif_rstmgr_t rstmgr;
static dif_alert_handler_t alert_handler;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_uart_t uart;

typedef struct node {
  const char *name;
  dif_alert_handler_alert_t alert;
  dif_alert_handler_class_t class;
} node_t;

static const dif_alert_handler_escalation_phase_t kEscProfiles[] = {
    // TODO:
    // this first/second duration must be long enough to
    // accommodate a jtag transaction
    // how can this be done in a non-hardcoded way?
    {.phase = kDifAlertHandlerClassStatePhase0,
     .signal = 0,
     .duration_cycles = 10000},
    {.phase = kDifAlertHandlerClassStatePhase1,
     .signal = 1,
     .duration_cycles = 10000},
    {.phase = kDifAlertHandlerClassStatePhase2,
     .signal = 3,
     .duration_cycles = 3000}};

static const dif_alert_handler_class_config_t kConfigProfiles[] = {{
    .auto_lock_accumulation_counter = kDifToggleDisabled,
    .accumulator_threshold = 0,
    .irq_deadline_cycles = 0,
    .escalation_phases = kEscProfiles,
    .escalation_phases_len = 3,
    .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
}};

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
void ottf_external_nmi_handler(void) {
  // DO NOT REMOVE, DV sync message
  LOG_INFO("You are experiencing an NMI");

  // Now intentionally hang the device
  CHECK_DIF_OK(dif_clkmgr_gateable_clock_set_enabled(
      &clkmgr, kTopEarlgreyGateableClocksIoDiv4Peri, kDifToggleDisabled));

  // access uart after clocks have been disabled
  CHECK_DIF_OK(dif_uart_disable_rx_timeout(&uart));
  LOG_FATAL("This message should never be seen");
}

bool test_main(void) {
  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));

  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart));

  CHECK_DIF_OK(dif_keymgr_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), &keymgr));

  // Check if there was a HW reset caused by the escalation.
  dif_rstmgr_reset_info_bitfield_t rst_info;
  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  if (rst_info & kDifRstmgrResetInfoPor) {
    // set the alert we care about to class A
    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        &alert_handler, kTopEarlgreyAlertIdRvCoreIbexRecovSwErr,
        kDifAlertHandlerClassA, /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleEnabled));

    // configurate class A
    CHECK_DIF_OK(dif_alert_handler_configure_class(
        &alert_handler, kDifAlertHandlerClassA, kConfigProfiles[0],
        /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleEnabled));

    // Initialize keymgr with otp contents
    CHECK_STATUS_OK(keymgr_testutils_advance_state(&keymgr, NULL));

    // DO NOT REMOVE, DV sync message
    LOG_INFO("Keymgr entered Init State");

    // Enable NMI
    CHECK_DIF_OK(dif_rv_core_ibex_enable_nmi(&rv_core_ibex,
                                             kDifRvCoreIbexNmiSourceAlert));

    // force trigger the alert
    CHECK_DIF_OK(dif_rv_core_ibex_alert_force(&rv_core_ibex,
                                              kDifRvCoreIbexAlertRecovSwErr));

    // Stop execution here and just wait for something to happen
    wait_for_interrupt();
    LOG_ERROR("Should have reset before this line");
    return false;

  } else if (rst_info & kDifRstmgrResetInfoEscalation) {
    // DO NOT REMOVE, DV sync message
    LOG_INFO("Reset due to alert escalation");
    return true;

  } else {
    LOG_ERROR("Unexpected reset info %d", rst_info);
  }

  return false;
}
