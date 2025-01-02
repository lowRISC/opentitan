// Copyright lowRISC contributors (OpenTitan project).
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

OTTF_DEFINE_TEST_CONFIG();

static dif_clkmgr_t clkmgr;
static dif_keymgr_t keymgr;
static dif_rstmgr_t rstmgr;
static dif_alert_handler_t alert_handler;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_uart_t uart;

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 *
 * @param exc_info Execution info.
 */
void ottf_external_nmi_handler(uint32_t *exc_info) {
  // DO NOT REMOVE, DV sync message
  LOG_INFO("You are experiencing an NMI");

  dif_rv_core_ibex_nmi_state_t nmi_state = (dif_rv_core_ibex_nmi_state_t){0};

  CHECK_DIF_OK(dif_rv_core_ibex_get_nmi_state(
      &rv_core_ibex, (dif_rv_core_ibex_nmi_state_t *)&nmi_state));

  CHECK(nmi_state.alert_enabled && nmi_state.alert_raised,
        "Alert handler NMI state not expected:\n\t"
        "alert_enable:%x\n\talert_raised:%x\n",
        nmi_state.alert_enabled, nmi_state.alert_raised);

  dif_alert_handler_class_state_t state;
  CHECK_DIF_OK(dif_alert_handler_get_class_state(
      &alert_handler, kDifAlertHandlerClassA, &state));

  // Now intentionally hang the device
  CHECK_DIF_OK(dif_clkmgr_gateable_clock_set_enabled(
      &clkmgr, kTopEarlgreyGateableClocksIoDiv4Peri, kDifToggleDisabled));

  // access uart after clocks have been disabled
  CHECK_DIF_OK(dif_uart_disable_rx_timeout(&uart));
  LOG_FATAL("This message should never be seen");
}

/**
 * Initialize the dif handles required for this test.
 */
static void init_peripheral_handles(void) {
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
}

/**
 * Configure the alert handler. The escalation phases (NMI interrupt, LC scrap
 * state, chip reset) are assigned to alert class A.
 */
static void config_alert_handler(void) {
  // Escalation phase 0 is the NMI interrupt whose timeout value before
  // progressing to phase 1 differs depending on the simulation device. For
  // example, on the ChipWhisperer 1000000 cycles are enough to prevent a
  // premature cancellation of the NMI interrupt handler (see
  // `ottf_external_nmi_handler`).
  uint32_t phase0DurationCycles = 1000000;
  if (kDeviceType == kDeviceSimVerilator) {
    phase0DurationCycles /= 10;
  } else if (kDeviceType == kDeviceSimDV) {
    phase0DurationCycles /= 100;
  }

  dif_alert_handler_escalation_phase_t escalationProfiles[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = phase0DurationCycles},
      {.phase = kDifAlertHandlerClassStatePhase1,
       .signal = 1,
       .duration_cycles = 10000},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 3,
       .duration_cycles = 10000},
  };
  dif_alert_handler_class_config_t configProfiles[] = {{
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = 0,
      .escalation_phases = escalationProfiles,
      .escalation_phases_len = 3,
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  }};

  // set the alert we care about to class A
  CHECK_DIF_OK(dif_alert_handler_configure_alert(
      &alert_handler, kTopEarlgreyAlertIdRvCoreIbexRecovSwErr,
      kDifAlertHandlerClassA, /*enabled=*/kDifToggleEnabled,
      /*locked=*/kDifToggleEnabled));

  // configure class A
  CHECK_DIF_OK(dif_alert_handler_configure_class(
      &alert_handler, kDifAlertHandlerClassA, configProfiles[0],
      /*enabled=*/kDifToggleEnabled,
      /*locked=*/kDifToggleEnabled));
}

/**
 * - Verify the first escalation results in NMI interrupt serviced by the CPU.
 * - Verify the second results in device being put in escalate state, via the LC
 *   JTAG TAP.
 * - Verify the third results in chip reset.
 * - Ensure that all escalation handshakes complete without errors.
 *
 * The first escalation is checked via the entry of the NMI handler and polling
 * by dv. The second escalation is directly checked by dv. The third escalation
 * is checked via reset reason.
 */
bool test_main(void) {
  init_peripheral_handles();

  // Check if there was a HW reset caused by the escalation.
  dif_rstmgr_reset_info_bitfield_t rst_info;
  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  if (rst_info & kDifRstmgrResetInfoPor) {
    config_alert_handler();

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
