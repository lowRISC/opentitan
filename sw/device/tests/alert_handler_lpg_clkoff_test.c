// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "alert_handler_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_rv_plic_t plic;
static dif_alert_handler_t alert_handler;
static dif_clkmgr_t clkmgr;
static dif_rv_core_ibex_t ibex;
static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

static plic_isr_ctx_t plic_ctx = {
    .rv_plic = &plic,
    .hart_id = kPlicTarget,
};

// Depends on the clock domain, sometimes alert handler will trigger a spurious
// alert after the alert timeout. (Issue #2321)
// So we allow class A interrupt to fire after the real timeout interrupt is
// triggered.
static alert_handler_isr_ctx_t alert_handler_ctx = {
    .alert_handler = &alert_handler,
    .plic_alert_handler_start_irq_id = kTopEarlgreyPlicIrqIdAlertHandlerClassa,
    .expected_irq = kDifAlertHandlerIrqClassb,
    .is_only_irq = false,
};

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, &alert_handler));

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  mmio_region_t ibex_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_core_ibex_init(ibex_addr, &ibex));

  // Enable all the alert_handler interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&plic, kPlicTarget,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassa,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassd);
}

/**
 * Program the alert handler to escalate on alerts upto phase 1 (i.e. wipe
 * secret) but not trigger reset. Then CPU can check if the correct interrupt
 * fires and check the local alert cause register.
 */
static void alert_handler_config(void) {
  dif_alert_handler_alert_t alerts[1];
  dif_alert_handler_class_t alert_classes[1];

  // Enable all incoming alerts and configure them to classa.
  // This alert should never fire because we do not expect any incoming alerts.
  //for (int i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
  for (int i = 0; i < 1; ++i) {
    alerts[i] = i+19;
    alert_classes[i] = kDifAlertHandlerClassA;
  }

  // Enable alert ping fail local alert and configure that to classb.
  dif_alert_handler_local_alert_t loc_alerts[] = {
      kDifAlertHandlerLocalAlertAlertPingFail,
      kDifAlertHandlerLocalAlertEscalationPingFail,
      kDifAlertHandlerLocalAlertAlertIntegrityFail,
      kDifAlertHandlerLocalAlertEscalationIntegrityFail,
      kDifAlertHandlerLocalAlertBusIntegrityFail,
      kDifAlertHandlerLocalAlertShadowedUpdateError,
      kDifAlertHandlerLocalAlertShadowedStorageError
      };
  dif_alert_handler_class_t loc_alert_classes[] = {kDifAlertHandlerClassB,
                                                   kDifAlertHandlerClassB,
                                                   kDifAlertHandlerClassB,
                                                   kDifAlertHandlerClassB,
                                                   kDifAlertHandlerClassB,
                                                   kDifAlertHandlerClassB,
                                                   kDifAlertHandlerClassB,
                                                  };

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = 2000}};

  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 1,
      .irq_deadline_cycles = 10000,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  dif_alert_handler_class_config_t class_configs[] = {class_config,
                                                      class_config};

  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassA,
                                         kDifAlertHandlerClassB};
  dif_alert_handler_config_t config = {
      .alerts = alerts,
      .alert_classes = alert_classes,
      .alerts_len = ARRAYSIZE(alerts),
      .local_alerts = loc_alerts,
      .local_alert_classes = loc_alert_classes,
      .local_alerts_len = ARRAYSIZE(loc_alerts),
      .classes = classes,
      .class_configs = class_configs,
      .classes_len = ARRAYSIZE(class_configs),
      .ping_timeout = 2,
  };

  alert_handler_testutils_configure_all(&alert_handler, config,
                                        kDifToggleEnabled);  
  // Enables alert handler irq.
 /*  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));

  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassb, kDifToggleEnabled));  */     
}

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
void ottf_external_isr(void) {
  top_earlgrey_plic_peripheral_t peripheral_serviced;
  dif_alert_handler_irq_t irq_serviced;
  isr_testutils_alert_handler_isr(plic_ctx, alert_handler_ctx,
                                  &peripheral_serviced, &irq_serviced);
  CHECK(peripheral_serviced == kTopEarlgreyPlicPeripheralAlertHandler,
        "Interurpt from unexpected peripheral: %d", peripheral_serviced);
}

bool test_main(void) {
  init_peripherals();

  //alert_handler_config();

  // Enable the external IRQ at Ibex.
  //irq_global_ctrl(true);
  //irq_external_ctrl(true);

  int aa;
  bool is_sth;

//---------------------- INITIAL ALERT_HANDLER CONFIG ---------------
  LOG_INFO("STEP #1: ALERT_HANDLER BEFORE THE CONFIG");
  // Print if any of the alerts is locked
  // Expected behavior: no print
  for(aa=0; aa<63; aa++) {
    CHECK_DIF_OK(dif_alert_handler_is_alert_locked( &alert_handler, aa, &is_sth));
    if (is_sth)
    {
      LOG_INFO("is_locked_alert_%d = %d", aa, is_sth);
    }
  }
  
  // Print if any of the local_alerts is locked
  // Expected behavior: no print
  for(aa=0; aa<7; aa++) {
    CHECK_DIF_OK(dif_alert_handler_is_local_alert_locked( &alert_handler, aa, &is_sth));
    if (is_sth)
    {
      LOG_INFO("is_locked_local_alert_%d = %d", aa, is_sth);
    }
  }

  // Print if any of the alert classess is locked
  // Expected behavior: no print
  for(aa=0; aa<4; aa++) {
    CHECK_DIF_OK(dif_alert_handler_is_class_locked( &alert_handler, aa, &is_sth));
    if (is_sth)
    {
      LOG_INFO("is_locked_class_%d = %d", aa, is_sth);
    }
  }

  // Print if ping timer is locked
  // Expected behavior: no print
  CHECK_DIF_OK(dif_alert_handler_is_ping_timer_locked( &alert_handler, &is_sth));
  if (is_sth)
  {
    LOG_INFO("is_locked_ping_timer", is_sth);
  }
  LOG_INFO("\n");
  //-----------------------------------------------------------------------
  
  dif_toggle_t clock_state;

// TRANSACTIONAL CLOCK ENABLE/DISABLE
  
  // Enable/disable AES clocks => alert #42 (recov), alert #43(fatal) (somehow worked)
/* 
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(&clkmgr, kTopEarlgreyHintableClocksMainAes,kDifToggleDisabled));
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_enabled(&clkmgr, kTopEarlgreyHintableClocksMainAes, &clock_state));
  LOG_INFO("Clock enabled state hintable (%d).", clock_state); 
*/

// Enable/disable HMAC clocks => alert #43 (did not work)
/* 
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(&clkmgr, kTopEarlgreyHintableClocksMainHmac,kDifToggleDisabled));
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_enabled(&clkmgr, kTopEarlgreyHintableClocksMainHmac, &clock_state));
  LOG_INFO("Clock enabled state hintable (%d).", clock_state); 
*/

// Enable/disable HMAC clocks => #44 (recov), alert #45(fatal) (did not work)
/* 
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(&clkmgr, kTopEarlgreyHintableClocksMainKmac,kDifToggleDisabled));
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_enabled(&clkmgr, kTopEarlgreyHintableClocksMainKmac, &clock_state));
  LOG_INFO("Clock enabled state hintable (%d).", clock_state); 
*/

// Enable/disable OTBN clocks => #46 (recov), alert #47(fatal) (did not work)
/* 
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(&clkmgr, kTopEarlgreyHintableClocksMainOtbn,kDifToggleDisabled));
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_enabled(&clkmgr, kTopEarlgreyHintableClocksMainOtbn, &clock_state));
  LOG_INFO("Clock enabled state hintable (%d).", clock_state); 
*/


// PERIPHERAL/GATEABLE CLOCKS
/*  
  // disable usbdev clock (usb_peri) -> alert #21 (worked, ping_timeout=2)
  
  CHECK_DIF_OK(dif_clkmgr_gateable_clock_set_enabled(&clkmgr, kTopEarlgreyGateableClocksUsbPeri, kDifToggleDisabled));
  CHECK_DIF_OK(dif_clkmgr_gateable_clock_get_enabled(&clkmgr, kTopEarlgreyGateableClocksUsbPeri, &clock_state));
  LOG_INFO("Clock enabled state gateable (%d).", clock_state);
*/

  // disable spi1 clock (div2_peri) -> alert #20 (worked, ping_timeout=2)
/*
  LOG_INFO("STEP #2: DISABLE IO_PERI CLOCK ");  
  CHECK_DIF_OK(dif_clkmgr_gateable_clock_set_enabled(&clkmgr, kTopEarlgreyGateableClocksIoDiv2Peri, kDifToggleDisabled));
  CHECK_DIF_OK(dif_clkmgr_gateable_clock_get_enabled(&clkmgr, kTopEarlgreyGateableClocksIoDiv2Peri, &clock_state));
  LOG_INFO("is_ClocksIoPeri_enabled = %d.", clock_state);
*/

// disable spi0 clock (io_peri) -> alert #19 (worked, ping_timeout=2)
///*
  LOG_INFO("STEP #2: DISABLE IO_PERI CLOCK ");  
  CHECK_DIF_OK(dif_clkmgr_gateable_clock_set_enabled(&clkmgr, kTopEarlgreyGateableClocksIoPeri, kDifToggleDisabled));
  CHECK_DIF_OK(dif_clkmgr_gateable_clock_get_enabled(&clkmgr, kTopEarlgreyGateableClocksIoPeri, &clock_state));
  LOG_INFO("is_ClocksIoPeri_enabled = %d.", clock_state);
//*/

  int jj = 0;
  LOG_INFO("STEP #3: CONFIGURE THE ALERT HANDLER");
  alert_handler_config();

  LOG_INFO("STEP #4: ALERT_HANDLER AFTER CONFIG");
  // Print if any of the alerts is locked
  // Expected behavior: no print
  for(aa=0; aa<63; aa++) {
    CHECK_DIF_OK(dif_alert_handler_is_alert_locked( &alert_handler, aa, &is_sth));
    if (is_sth)
    {
      LOG_INFO("is_locked_alert_%d = %d", aa, is_sth);
    }
  }
  
  // Print if any of the local_alerts is locked
  // Expected behavior: no print
  for(aa=0; aa<7; aa++) {
    CHECK_DIF_OK(dif_alert_handler_is_local_alert_locked( &alert_handler, aa, &is_sth));
    if (is_sth)
    {
      LOG_INFO("is_locked_local_alert_%d = %d", aa, is_sth);
    }
  }

  // Print if any of the alert classess is locked
  // Expected behavior: no print
  for(aa=0; aa<4; aa++) {
    CHECK_DIF_OK(dif_alert_handler_is_class_locked( &alert_handler, aa, &is_sth));
    if (is_sth)
    {
      LOG_INFO("is_locked_class_%d = %d", aa, is_sth);
    }
  }

  // Print if ping timer is locked
  // Expected behavior: no print
  CHECK_DIF_OK(dif_alert_handler_is_ping_timer_locked( &alert_handler, &is_sth));
  if (is_sth)
  {
    LOG_INFO("is_locked_ping_timer = %d", is_sth);
  }
  LOG_INFO("\n");

  
  LOG_INFO("STEP #5: WAIT....");
  //wait_for_interrupt();
  busy_spin_micros(1000*10000);

 
  int ii;
  bool is_cause;

  LOG_INFO("STEP #6: PRINT THE STATE AFTER WAITING");
  dif_alert_handler_class_state_t state;
  for (ii=0;ii<7;ii++){ 
    CHECK_DIF_OK(dif_alert_handler_local_alert_is_cause(
      &alert_handler, ii, &is_cause));
    LOG_INFO ("is_cause_local_alert_%d = %d", ii, is_cause);
  }

  for (ii=0;ii<4;ii++){
     CHECK_DIF_OK(dif_alert_handler_get_class_state(&alert_handler, ii, &state));
      LOG_INFO ("state_alert_class_%d = %d", ii, state);
  }

  dif_alert_handler_irq_state_snapshot_t snapshot;
  CHECK_DIF_OK(dif_alert_handler_irq_get_state(&alert_handler, &snapshot));
  LOG_INFO ("irq snapshot = %d", snapshot);


  LOG_INFO("STEP #7: PRINT THE CLOCKS AFTER WAITING");
  for (ii=kTopEarlgreyHintableClocksMainAes; ii <= kTopEarlgreyHintableClocksLast; ii++){
    CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_enabled(&clkmgr, ii, &clock_state));
    LOG_INFO("is_enabled_hinteable_clock_%d = %d", ii, clock_state);
  }

  for (ii=kTopEarlgreyGateableClocksIoDiv4Peri; ii <= kTopEarlgreyGateableClocksLast; ii++){
    CHECK_DIF_OK(dif_clkmgr_gateable_clock_get_enabled(&clkmgr, ii, &clock_state));
    LOG_INFO("is_enabled_gateable_clock_%d = %d", ii, clock_state);
  }

  // This part is from the original alert_handler_pinf_timeout_test.c
  // SUCCESS => We did get a ping_fail alert
  // FAIL ==> We did not get a ping_fail alert
  dif_alert_handler_local_alert_t exp_local_alert =
      kDifAlertHandlerLocalAlertAlertPingFail;
  CHECK_DIF_OK(dif_alert_handler_local_alert_is_cause(
      &alert_handler, exp_local_alert, &is_cause));
  LOG_INFO ("FINAL is_cause = %d", is_cause);
  CHECK(is_cause, "Expect local alert cause: alert_ping_fail!");

  return true;
}
