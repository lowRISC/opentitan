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
#include "sw/device/lib/dif/dif_rv_plic.h"
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
  kWdogBarkMicros = 200,          // 200 us
  kWdogBiteMicros = 600,          // 600 us
  kEscalationStartMicros = 100,   // 100 us
  kEscalationPhase0Micros = 100,  // 100 us
  kEscalationPhase1Micros = 100,  // 100 us
  kMaxInterrupts = 30,
  kRegionBaseBank1Page0Addr = FLASH_CTRL_PARAM_BYTES_PER_BANK,
  kNumTestWords = 16,
  kNumTestBytes = kNumTestWords * sizeof(uint32_t),
  kExpectedAlertNumber = 0,
};

static_assert(kWdogBarkMicros < kWdogBiteMicros &&
                  kWdogBarkMicros > kEscalationPhase0Micros,
              "The wdog bite shall happen only if escalation reset fails.");

static dif_rv_plic_t plic;
static dif_alert_handler_t alert_handler;
static dif_aon_timer_t aon_timer;
static dif_rstmgr_t rstmgr;
static dif_flash_ctrl_state_t flash_ctrl_state;

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

  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));

  LOG_INFO("Regular external ISR exiting");
}

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
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
       .signal = 0,
       .duration_cycles =
           alert_handler_testutils_get_cycles_from_us(kEscalationPhase0Micros) *
           alert_handler_testutils_cycle_rescaling_factor()},
      {.phase = kDifAlertHandlerClassStatePhase1,
       .signal = 3,
       .duration_cycles =
           alert_handler_testutils_get_cycles_from_us(kEscalationPhase1Micros) *
           alert_handler_testutils_cycle_rescaling_factor()}};

  uint32_t deadline_cycles =
      alert_handler_testutils_get_cycles_from_us(kEscalationStartMicros) *
      alert_handler_testutils_cycle_rescaling_factor();
  LOG_INFO("Configuring class A with %d cycles and %d occurrences",
           deadline_cycles, UINT16_MAX);
  dif_alert_handler_class_config_t class_config[] = {{
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = UINT16_MAX,
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
