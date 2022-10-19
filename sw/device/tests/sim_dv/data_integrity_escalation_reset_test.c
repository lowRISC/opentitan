// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test triggers a ram read uncorrectable error created from the SV side
// for a specific address. The alert handler is programmed to trigger a specific
// alert for the ibex.
//
// The test checks that the alert handler state indicates the correct alert
// prior to reset, which is checked in the alert triggered interrupt. The
// test also checks that the alert handler cleared that state after reset.  It
// also checks that the corresponding bit in the ibex fatal error CSR is set in
// the interrupt, and it is also cleared after reset.
//
// As a backup the aon timer is programmed to bark and bite, but these are
// expected not to happen since the escalation takes precedence.
//
// The alert_handler is programmed to escalate on the first interrupt, so the
// regular ISR is not necessarily run and the load integrity error handler may
// be beat by the NMI.

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

// This location will be update from SV to contain the address which will
// trigger the fault on a read.
static volatile const uint32_t kErrorRamAddress = 0;

static const uint32_t kExpectedAlertNumber = 63;

uint32_t reset_count;

enum {
  // Counter for resets.
  kCounterReset,
  // Counter for regular interrupts.
  kCounterInterrupt,
  // Counter for NMIs.
  kCounterNmi,
};

/**
 * Program the alert handler to escalate on alerts upto phase 2 (i.e. reset).
 * Also program the aon timer with:
 * - bark after escalation starts, so the interrupt is suppressed by escalation,
 * - bite after escalation reset, so we should not get timer reset.
 */
enum {
  kWdogBarkMicros = 600,          // 600 us
  kWdogBiteMicros = 800,          // 800 us
  kEscalationStartMicros = 200,   // 200 us
  kEscalationPhase0Micros = 200,  // 200 us
  kEscalationPhase1Micros = 200,  // 200 us
  kMaxResets = 2,
  kMaxInterrupts = 30,
};

static_assert(kWdogBarkMicros < kWdogBiteMicros &&
                  kWdogBarkMicros > kEscalationPhase0Micros,
              "The wdog bite shall happen only if escalation reset fails.");

/**
 * Objects to access the peripherals used in this test via dif API.
 */
static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static dif_alert_handler_t alert_handler;
static dif_aon_timer_t aon_timer;
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_rstmgr_t rstmgr;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_rv_plic_t plic;

static const char *we_check = "prim_reg_we_check";

static void rv_core_ibex_fault_checker(bool enable) {
  dif_rv_core_ibex_error_status_t codes;
  CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  CHECK(codes == (enable ? kDifRvCoreIbexErrorStatusFatalResponseIntegrity : 0),
        "Unexpected ibex error status");
}

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
void ottf_external_isr(void) {
  dif_rv_plic_irq_id_t irq_id;

  LOG_INFO("At regular external ISR");

  // There may be multiple interrupts due to the alert firing, so this keeps an
  // interrupt counter and errors-out if there are too many interrupts.

  // Increment the interrupt count and detect overflows.
  uint32_t interrupt_count =
      flash_ctrl_testutils_counter_get(kCounterInterrupt);
  if (interrupt_count > kMaxInterrupts) {
    CHECK(false, "Reset count %d got too many interrupts (%d)", reset_count,
          interrupt_count);
  }
  flash_ctrl_testutils_counter_set_at_least(
      &flash_ctrl_state, kCounterInterrupt, interrupt_count + 1);

  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  LOG_INFO("Got irq_id 0x%x (%d)", irq_id, irq_id);

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    uint32_t irq =
        (irq_id - (dif_rv_plic_irq_id_t)
                      kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);

    // We should not get aon timer interrupts since escalation suppresses them.
    CHECK(false, "Unexpected aon timer interrupt %d", irq);
  } else if (peripheral == kTopEarlgreyPlicPeripheralAlertHandler) {
    CHECK(irq_id == kTopEarlgreyPlicIrqIdAlertHandlerClassa,
          "Unexpected irq_id, expected %d, got %d",
          kTopEarlgreyPlicIrqIdAlertHandlerClassa, irq_id);
  }

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));
  LOG_INFO("Regular external ISR exiting");
}

void ottf_load_integrity_error_handler(void) {
  dif_rv_plic_irq_id_t irq_id;

  LOG_INFO("At load integrity error handler");

  uint32_t mtval = ibex_mtval_read();
  CHECK(mtval == kErrorRamAddress, "Unexpected mtval: expected 0x%x, got 0x%x",
        kErrorRamAddress, mtval);

  rv_core_ibex_fault_checker(true);

  // There may be multiple interrupts due to the alert firing, so this keeps an
  // interrupt counter and errors-out if there are too many interrupts.

  // Increment the interrupt count and detect overflows.
  uint32_t interrupt_count =
      flash_ctrl_testutils_counter_get(kCounterInterrupt);
  if (interrupt_count > kMaxInterrupts) {
    CHECK(false, "Reset count %d got too many interrupts (%d)", reset_count,
          interrupt_count);
  }
  flash_ctrl_testutils_counter_set_at_least(
      &flash_ctrl_state, kCounterInterrupt, interrupt_count + 1);

  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  LOG_INFO("Got irq_id 0x%x (%d)", irq_id, irq_id);

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    uint32_t irq =
        (irq_id - (dif_rv_plic_irq_id_t)
                      kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);

    // We should not get aon timer interrupts since escalation suppresses them.
    CHECK(false, "Unexpected aon timer interrupt %d", irq);
  } else if (peripheral == kTopEarlgreyPlicPeripheralAlertHandler) {
    LOG_INFO("Got expected alert handler interrupt %d", irq_id);

    // Disable these interrupts from alert_handler so they don't keep happening
    // until NMI.
    uint32_t irq =
        (irq_id -
         (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdAlertHandlerClassa);
    CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(&alert_handler, irq,
                                                   kDifToggleDisabled));

    // Disable this interrupt to prevent it from continuously firing. This
    // should not prevent escalation from continuing.
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&plic, irq_id, kPlicTarget,
                                             kDifToggleEnabled));
  }

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));
  LOG_INFO("Load integrity error handler exiting");
}

/**
 * External NMI ISR.
 *
 * Handles NMI interrupts on Ibex for either escalation or watchdog.
 */
void ottf_external_nmi_handler(void) {
  LOG_INFO("At NMI handler");

  // Increment the nmi interrupt count.
  uint32_t nmi_interrupt_count = flash_ctrl_testutils_counter_get(kCounterNmi);
  if (nmi_interrupt_count > kMaxInterrupts) {
    LOG_INFO("Saturating nmi interrupts at %d", nmi_interrupt_count);
  } else {
    flash_ctrl_testutils_counter_set_at_least(&flash_ctrl_state, kCounterNmi,
                                              nmi_interrupt_count + 1);
  }

  // Check the class.
  dif_alert_handler_class_state_t state;
  CHECK_DIF_OK(dif_alert_handler_get_class_state(
      &alert_handler, kDifAlertHandlerClassA, &state));
  CHECK(state == kDifAlertHandlerClassStatePhase0, "Wrong phase %d", state);

  // Check this gets the expected alert.
  bool is_cause = false;
  CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
      &alert_handler, kExpectedAlertNumber, &is_cause));
  CHECK(is_cause);

  // Acknowledge the cause, which doesn't affect escalation.
  CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(&alert_handler,
                                                   kExpectedAlertNumber));
}

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));

  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));
}

/**
 * Program the alert handler to escalate on alerts and reset on phase 2,
 * and to start escalation after timing out due to an unacknowledged
 * interrupt.
 */
static void alert_handler_config(void) {
  dif_alert_handler_alert_t alerts[] = {kExpectedAlertNumber};
  dif_alert_handler_class_t alert_classes[] = {kDifAlertHandlerClassA};

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles =
           alert_handler_testutils_get_cycles_from_us(kEscalationPhase0Micros)},
      {.phase = kDifAlertHandlerClassStatePhase1,
       .signal = 1,
       .duration_cycles =
           alert_handler_testutils_get_cycles_from_us(kEscalationPhase1Micros)},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 3,
       .duration_cycles = alert_handler_testutils_get_cycles_from_us(
           kEscalationPhase1Micros)}};

  uint32_t deadline_cycles =
      alert_handler_testutils_get_cycles_from_us(kEscalationStartMicros);
  uint32_t threshold = 0;
  LOG_INFO("Configuring class A with %d cycles and %d occurrences",
           deadline_cycles, threshold);
  dif_alert_handler_class_config_t class_config[] = {{
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = threshold,
      .irq_deadline_cycles = deadline_cycles,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase3,
  }};

  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassA};
  dif_alert_handler_config_t config = {
      .alerts = alerts,
      .alert_classes = alert_classes,
      .alerts_len = ARRAYSIZE(alerts),
      .classes = classes,
      .class_configs = class_config,
      .classes_len = ARRAYSIZE(class_config),
      .ping_timeout = 0,
  };

  alert_handler_testutils_configure_all(&alert_handler, config,
                                        kDifToggleEnabled);
  // Enables alert handler irq.
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));
}

static void set_aon_timers() {
  uint32_t bark_cycles =
      aon_timer_testutils_get_aon_cycles_from_us(kWdogBarkMicros);
  uint32_t bite_cycles =
      aon_timer_testutils_get_aon_cycles_from_us(kWdogBiteMicros);

  LOG_INFO(
      "Wdog will bark after %u us (%u cycles) and bite after %u us (%u cycles)",
      (uint32_t)kWdogBarkMicros, bark_cycles, (uint32_t)kWdogBiteMicros,
      bite_cycles);

  // Setup the wdog bark and bite timeouts.
  aon_timer_testutils_watchdog_config(&aon_timer, bark_cycles, bite_cycles,
                                      /*pause_in_sleep=*/false);
}

/**
 * Setup aon timer interrupts and trigger fault.
 *
 * The aon timers should never trigger actions because escalation should take
 * precedence.
 */
static void execute_test() {
  alert_handler_config();

  // Enable NMI
  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceAlert));

  set_aon_timers();

  LOG_INFO("Reading corrupted address 0x%x, expecting alert %d",
           kErrorRamAddress, kExpectedAlertNumber);

  // The SV side injects error when test starts.
  uint32_t data = *((uint32_t *)kErrorRamAddress);

  // This normally should not run.
  LOG_INFO("Read from address 0x%0x with expected error gets 0x%x",
           kErrorRamAddress, data);

  wait_for_interrupt();
  CHECK(false, "This should not be reached");
}

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  init_peripherals();

  // Enable all the interrupts used in this test.
  rv_plic_testutils_irq_range_enable(
      &plic, kPlicTarget, kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired,
      kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark);
  rv_plic_testutils_irq_range_enable(&plic, kPlicTarget,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassa,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassd);

  // Enable access to flash for storing info across resets.
  LOG_INFO("Setting default region accesses");
  flash_ctrl_testutils_default_region_access(&flash_ctrl_state,
                                             /*rd_en*/ true,
                                             /*prog_en*/ true,
                                             /*erase_en*/ true,
                                             /*scramble_en*/ false,
                                             /*ecc_en*/ false,
                                             /*he_en*/ false);

  // Get the flash maintained reset counter.
  reset_count = flash_ctrl_testutils_counter_get(kCounterReset);
  LOG_INFO("Reset counter value: %u", reset_count);
  if (reset_count > kMaxResets) {
    CHECK(false, "Got too many resets (%d)", reset_count);
  }

  // Increment reset counter to know where we are.
  flash_ctrl_testutils_counter_set_at_least(&flash_ctrl_state, kCounterReset,
                                            reset_count + 1);

  // Check if there was a HW reset caused by the escalation.
  dif_rstmgr_reset_info_bitfield_t rst_info;
  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  CHECK(rst_info == kDifRstmgrResetInfoPor ||
            rst_info == kDifRstmgrResetInfoEscalation,
        "Wrong reset reason %02X", rst_info);

  if (rst_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Booting for the first time, starting test");
    execute_test();
  } else if (rst_info == kDifRstmgrResetInfoEscalation) {
    LOG_INFO("Booting for the second time due to escalation reset");

    int interrupt_count = flash_ctrl_testutils_counter_get(kCounterInterrupt);
    // The interrupt count is informational only, since it is possible the NMI
    // ends up taking precedence given the accumulator threshold is zero.
    LOG_INFO("Interrupt count %d", interrupt_count);

    int nmi_interrupt_count = flash_ctrl_testutils_counter_get(kCounterNmi);
    CHECK(nmi_interrupt_count > 0, "Expected at least one nmi");

    // Check the alert handler cause is cleared.
    bool is_cause = true;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, kExpectedAlertNumber, &is_cause));
    CHECK(!is_cause);

    // Check the fault register is clear.
    rv_core_ibex_fault_checker(false);
    return true;
  } else {
    LOG_ERROR("Unexpected rst_info=0x%x", rst_info);
    return false;
  }

  return false;
}
