// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test triggers a catastrophic flash controller error
// (fault_status.host_gnt_err), and checks the alert escalation
// process and ibex core are not distubed by this flash_ctrl error.
#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
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

#include "alert_handler_regs.h"
#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kPlicTarget = kTopEarlgreyPlicTargetIbex0,
  kWdogBarkMicros = 200,  // 200 us
  kWdogBiteMicros = 600,  // 600 us
  // handlers have time to execute.
  kEscalationPhase0Micros = 100,
  // @200 us -> in this phase we will raise an NMI
  kEscalationPhase1Micros = 100,
  // @400 us -> in this phase we will assert lc_escalate_en
  kEscalationPhase2Micros = 100,
  // @600 us -> in this phase we will reset the chip
  kEscalationPhase3Micros = 100,

  kRegionBaseBank1Page0Addr = FLASH_CTRL_PARAM_BYTES_PER_BANK,
  kNumTestWords = 16,
  kNumTestBytes = kNumTestWords * sizeof(uint32_t),
  kExpectedAlertNumber = kTopEarlgreyAlertIdFlashCtrlFatalErr,
};

static_assert(kWdogBarkMicros < kWdogBiteMicros &&
                  kWdogBarkMicros > kEscalationPhase0Micros,
              "The wdog bite shall happen only if escalation reset fails.");

static dif_rv_plic_t plic;
static dif_alert_handler_t alert_handler;
static dif_aon_timer_t aon_timer;
static dif_rstmgr_t rstmgr;
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_rv_core_ibex_t rv_core_ibex;

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
void ottf_external_isr(void) {
  top_earlgrey_plic_peripheral_t peripheral;
  dif_rv_plic_irq_id_t irq_id;
  uint32_t irq = 0;

  LOG_INFO("At regular external ISR");
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  LOG_INFO("peripheral: %d  irq_id:%d", peripheral, irq_id);

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    irq =
        (dif_aon_timer_irq_t)(irq_id -
                              (dif_rv_plic_irq_id_t)
                                  kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);

    CHECK(false, "Unexpected aon timer interrupt %d", irq);
  } else if (peripheral == kTopEarlgreyPlicPeripheralAlertHandler) {
    irq = (irq_id -
           (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdAlertHandlerClassa);

    // Check if class A alert.
    CHECK(irq == 0, "ClassA('d0) was expected but got %d", irq);
  }

  // Disable these interrupts from alert_handler so they don't keep happening
  // until NMI.
  irq =
      (irq_id - (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdAlertHandlerClassa);
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(&alert_handler, irq,
                                                 kDifToggleDisabled));

  // Disable this interrupt to prevent it from continuously firing. This
  // should not prevent escalation from continuing.
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&plic, irq_id, kPlicTarget,
                                           kDifToggleDisabled));

  uint16_t accum_count;
  CHECK_DIF_OK(dif_alert_handler_get_accumulator(
      &alert_handler, kDifAlertHandlerClassA, &accum_count));
  LOG_INFO("Accumulator count %d", accum_count);

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));

  LOG_INFO("Regular external ISR exiting");
}

/**
 * External NMI ISR.
 *
 * Handles NMI interrupts on Ibex for either escalation or watchdog.
 */
void ottf_external_nmi_handler(void) {
  dif_rv_core_ibex_nmi_state_t nmi_state = (dif_rv_core_ibex_nmi_state_t){0};
  LOG_INFO("At NMI handler");

  // Check that this NMI was due to an alert handler escalation, and not due
  // to a watchdog bark, since escalation suppresses the watchdog.
  CHECK_DIF_OK(dif_rv_core_ibex_get_nmi_state(
      &rv_core_ibex, (dif_rv_core_ibex_nmi_state_t *)&nmi_state));
  CHECK(nmi_state.alert_enabled && nmi_state.alert_raised,
        "Alert handler NMI state not expected:\n\t"
        "alert_enable:%x\n\talert_raised:%x\n",
        nmi_state.alert_enabled, nmi_state.alert_raised);
  CHECK(nmi_state.wdog_enabled && !nmi_state.wdog_barked,
        "Watchdog NMI state not expected:\n\t"
        "wdog_enabled:%x\n\twdog_barked:%x\n",
        nmi_state.wdog_enabled, nmi_state.wdog_barked);

  // Check the class.
  dif_alert_handler_class_state_t state;
  CHECK_DIF_OK(dif_alert_handler_get_class_state(
      &alert_handler, kDifAlertHandlerClassA, &state));
  CHECK(state == kDifAlertHandlerClassStatePhase1, "Wrong phase %d", state);

  // Check this gets the expected alert.
  bool is_cause = false;
  CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
      &alert_handler, kExpectedAlertNumber, &is_cause));
  CHECK(is_cause);

  // Acknowledge the cause, which doesn't affect escalation.
  CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(&alert_handler,
                                                   kExpectedAlertNumber));
  LOG_INFO("NMI handler exiting");
}

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));

  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
}

/**
 * Program the alert handler to escalate on flash_ctrl fatal alerts and reset on
 * phase 2, and to start escalation after timing out due to an unacknowledged
 * interrupt.
 */
static void alert_handler_config(void) {
  dif_alert_handler_alert_t alerts[] = {kTopEarlgreyAlertIdFlashCtrlFatalErr};
  dif_alert_handler_class_t alert_classes[] = {kDifAlertHandlerClassA};

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = UINT32_MAX,  // do not trigger any signal, just wait.
       .duration_cycles =
           alert_handler_testutils_get_cycles_from_us(kEscalationPhase0Micros)},
      {.phase = kDifAlertHandlerClassStatePhase1,
       .signal = 0,  // NMI
       .duration_cycles =
           alert_handler_testutils_get_cycles_from_us(kEscalationPhase1Micros)},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 1,  // lc_escalate_en
       .duration_cycles =
           alert_handler_testutils_get_cycles_from_us(kEscalationPhase2Micros)},
      {.phase = kDifAlertHandlerClassStatePhase3,
       .signal = 3,  // reset
       .duration_cycles = alert_handler_testutils_get_cycles_from_us(
           kEscalationPhase3Micros)}};

  // This test does not leverage the IRQ timeout feature of the alert
  // handler, hence deadline_cycles is set to zero. Rather, it triggers
  // escalation right away if an alert event is seen, hence threshold = 0;
  uint32_t deadline_cycles = 0;
  uint32_t threshold = 0;

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

/**
 * Send flash read from the host interface.
 */
static void read_host_if(uint32_t addr) {
  uint32_t host_data[kNumTestWords];
  mmio_region_memcpy_from_mmio32(
      mmio_region_from_addr(TOP_EARLGREY_EFLASH_BASE_ADDR), addr, &host_data,
      kNumTestBytes);
}

static void set_aon_timers(const dif_aon_timer_t *aon_timer) {
  uint32_t bark_cycles =
      aon_timer_testutils_get_aon_cycles_from_us(kWdogBarkMicros);
  uint32_t bite_cycles =
      aon_timer_testutils_get_aon_cycles_from_us(kWdogBiteMicros);

  LOG_INFO(
      "Wdog will bark after %u us (%u cycles) and bite after %u us (%u cycles)",
      (uint32_t)kWdogBarkMicros, bark_cycles, (uint32_t)kWdogBiteMicros,
      bite_cycles);

  // Setup the wdog bark and bite timeouts.
  aon_timer_testutils_watchdog_config(aon_timer, bark_cycles, bite_cycles,
                                      /*pause_in_sleep=*/false);
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

  dif_rstmgr_reset_info_bitfield_t rst_info;
  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  LOG_INFO("reset reason %x", rst_info);

  if (rst_info == kDifRstmgrResetInfoPor) {
    alert_handler_config();
    // Make sure we can receive both the watchdog and alert NMIs.
    CHECK_DIF_OK(dif_rv_core_ibex_enable_nmi(&rv_core_ibex,
                                             kDifRvCoreIbexNmiSourceAlert));
    CHECK_DIF_OK(dif_rv_core_ibex_enable_nmi(&rv_core_ibex,
                                             kDifRvCoreIbexNmiSourceWdog));

    LOG_INFO("host read start from 0x%x",
             TOP_EARLGREY_EFLASH_BASE_ADDR + kRegionBaseBank1Page0Addr);
    read_host_if(kRegionBaseBank1Page0Addr);
    // Set the timer value longer than escalation timeout.
    // 'static_assert' is added to check it.
    set_aon_timers(&aon_timer);
    wait_for_interrupt();
  } else if (rst_info == kDifRstmgrResetInfoEscalation) {
    LOG_INFO("Booting for the second time due to escalation reset");
    return true;
  }

  return false;
}
