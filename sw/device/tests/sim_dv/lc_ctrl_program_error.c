// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/nv_counter_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "alert_handler_regs.h"
#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/*
 TO BE FILLED IN
 */

OTTF_DEFINE_TEST_CONFIG();

static dif_alert_handler_t alert_handler;
static dif_lc_ctrl_t lc_ctrl;
static dif_rstmgr_t rstmgr;
static dif_flash_ctrl_state_t flash_ctrl_state;

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static dif_rv_plic_t plic;
static dif_rv_core_ibex_t rv_core_ibex;

// Used for checking whether a regular alert interrupt has been seen.
static volatile bool alert_irq_seen = false;

static const dif_alert_handler_escalation_phase_t kEscProfiles[] = {
    // TODO:
    // this duration must be long enough to
    // accommodate a few jtag transactions
    // how can this be done in a non-hardcoded way?
    {.phase = kDifAlertHandlerClassStatePhase0,
     .signal = 1,
     .duration_cycles = 10000},
    {.phase = kDifAlertHandlerClassStatePhase1,
     .signal = 3,
     .duration_cycles = 10000}};

static const dif_alert_handler_class_config_t kConfigProfiles[] = {{
    .auto_lock_accumulation_counter = kDifToggleDisabled,
    .accumulator_threshold = 0,
    .irq_deadline_cycles = 0,
    .escalation_phases = kEscProfiles,
    .escalation_phases_len = 2,
    .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase0,
}};

// The function to check the fault status.
typedef void (*FaultCheckerFunction)(bool, const char *inst);

typedef struct fault_checker {
  FaultCheckerFunction function;
  const char *ip_inst;
} fault_checker_t;

// This preserves the fault checker across multiple resets in NV flash memory.
OT_SECTION(".non_volatile_scratch") uint64_t nv_fault_checker[2];

// This is the fault checker to be used. It is saved and retrieved from flash
// to preserve it across resets.
fault_checker_t fault_checker;

static void save_fault_checker(fault_checker_t *fault_checker) {
  uint32_t function_addr = (uint32_t)(fault_checker->function);
  uint32_t ip_inst_addr = (uint32_t)(fault_checker->ip_inst);
  CHECK_STATUS_OK(flash_ctrl_testutils_write(
      &flash_ctrl_state,
      (uint32_t)(&nv_fault_checker[0]) - TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
      0, &function_addr, kDifFlashCtrlPartitionTypeData, 1));
  CHECK_STATUS_OK(flash_ctrl_testutils_write(
      &flash_ctrl_state,
      (uint32_t)(&nv_fault_checker[1]) - TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
      0, &ip_inst_addr, kDifFlashCtrlPartitionTypeData, 1));
}

static void restore_fault_checker(fault_checker_t *fault_checker) {
  fault_checker->function = (FaultCheckerFunction)nv_fault_checker[0];
  fault_checker->ip_inst = (char *)nv_fault_checker[1];
}

static const char *lc_ctrl_inst_name = "lc_ctrl";

enum {
  // Counter for resets.
  kCounterReset,
  // Counter for regular interrupts.
  kCounterInterrupt,
  // Counter for NMIs.
  kCounterNmi,
};

static volatile uint32_t reset_count;

// This checks the lc_ctrl integrity fatal error code against expected.
static void lc_ctrl_fault_checker(bool enable, const char *ip_inst) {
  dif_lc_ctrl_status_t status;
  CHECK_DIF_OK(dif_lc_ctrl_get_status(&lc_ctrl, &status));
  bitfield_field32_t relevant_field = {
      .mask = UINT32_MAX, .index = kDifLcCtrlStatusCodeTooManyTransitions};
  uint32_t mask = bitfield_field32_write(0, relevant_field, UINT32_MAX);
  uint32_t relevant_status = status & mask;
  uint32_t fatal_prog_error =
      bitfield_bit32_write(0, kTopEarlgreyAlertIdLcCtrlFatalProgError, true);
  uint32_t expected_status = enable ? fatal_prog_error : 0;
  CHECK(relevant_status == expected_status,
        "For %s got codes 0x%x, expected 0x%x", ip_inst, relevant_status,
        expected_status);
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

  // Read the NV interrupt counter from flash and increment it.
  uint32_t interrupt_count = 0;
  CHECK_STATUS_OK(
      flash_ctrl_testutils_counter_get(kCounterInterrupt, &interrupt_count));
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_set_at_least(
      &flash_ctrl_state, kCounterInterrupt, interrupt_count + 1));

  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    uint32_t irq =
        (irq_id - (dif_rv_plic_irq_id_t)
                      kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);

    // We should not get aon timer interrupts since escalation suppresses them.
    CHECK(false, "Unexpected aon timer interrupt %d", irq);
  } else if (peripheral == kTopEarlgreyPlicPeripheralAlertHandler) {
    // Don't acknowledge the interrupt to alert_handler so it escalates.
    CHECK(fault_checker.function);
    CHECK(fault_checker.ip_inst);

    // Fatal alerts are only cleared by reset.
    fault_checker.function(/*enable=*/true, fault_checker.ip_inst);
  }

  // Disable these interrupts from alert_handler so they don't keep happening
  // until NMI.
  uint32_t irq =
      (irq_id - (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdAlertHandlerClassa);
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(&alert_handler, irq,
                                                 kDifToggleDisabled));

  // Disable this interrupt to prevent it from continuously firing. This
  // should not prevent escalation from continuing.
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&plic, irq_id, kPlicTarget,
                                           kDifToggleDisabled));

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));

  // Notify test function that the alert IRQ has been seen
  alert_irq_seen = true;

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

  // Read the NV NMI counter from flash and increment it.
  uint32_t nmi_count = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(kCounterNmi, &nmi_count));
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_set_at_least(
      &flash_ctrl_state, kCounterNmi, nmi_count + 1));

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
      &alert_handler, kTopEarlgreyAlertIdLcCtrlFatalProgError, &is_cause));
  CHECK(is_cause);

  // Acknowledge the cause, which doesn't affect escalation.
  CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
      &alert_handler, kTopEarlgreyAlertIdLcCtrlFatalProgError));
  LOG_INFO("NMI handler exiting");
}

void check_alert_dump(void) {
  dif_rstmgr_alert_info_dump_segment_t dump[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];
  size_t seg_size;
  alert_handler_testutils_info_t actual_info;

  // Reads the alert crash dump retained after reset (except POR)
  CHECK_DIF_OK(dif_rstmgr_alert_info_dump_read(
      &rstmgr, dump, DIF_RSTMGR_ALERT_INFO_MAX_SIZE, &seg_size));

  LOG_INFO("DUMP SIZE %d", seg_size);
  for (int i = 0; i < seg_size; i++) {
    LOG_INFO("DUMP:%d: 0x%x", i, dump[i]);
  }

  CHECK(seg_size <= INT_MAX, "seg_size must fit in int");
  CHECK_STATUS_OK(
      alert_handler_testutils_info_parse(dump, (int)seg_size, &actual_info));
  LOG_INFO("The alert info crash dump:");
  alert_handler_testutils_info_dump(&actual_info);
  // Check alert cause.
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    if (i == kTopEarlgreyAlertIdLcCtrlFatalProgError) {
      CHECK(actual_info.alert_cause[i], "Expected alert cause %d to be set", i);
    } else {
      // It is possible some alerts can trigger others; for example, some
      // lc_ctrl faults lead to otp_ctrl faults.
      if (actual_info.alert_cause[i]) {
        LOG_INFO("Unexpected alert cause %d, may be triggered by %d", i,
                 kTopEarlgreyAlertIdLcCtrlFatalProgError);
      }
    }
  }
}

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Initialize core and peripherals.
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR), &lc_ctrl));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // Enable access to flash for storing info across resets.
  LOG_INFO("Setting default region accesses");
  CHECK_STATUS_OK(
      flash_ctrl_testutils_default_region_access(&flash_ctrl_state,
                                                 /*rd_en*/ true,
                                                 /*prog_en*/ true,
                                                 /*erase_en*/ true,
                                                 /*scramble_en*/ false,
                                                 /*ecc_en*/ false,
                                                 /*he_en*/ false));

  // Get the flash maintained reset counter.
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(kCounterReset,
                                                   (uint32_t *)&reset_count));
  LOG_INFO("Reset counter value: %u", reset_count);

  // Increment reset counter.
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_set_at_least(
      &flash_ctrl_state, kCounterReset, reset_count + 1));

  // Check if there was a HW reset caused by the escalation.
  dif_rstmgr_reset_info_bitfield_t rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  CHECK(rst_info == kDifRstmgrResetInfoPor ||
            rst_info == kDifRstmgrResetInfoEscalation,
        "Wrong reset reason %02X", rst_info);

  if (rst_info & kDifRstmgrResetInfoPor) {
    LOG_INFO("Booting for the first time: starting test");

    LOG_INFO("Enabling rstmgr alert info capture");
    // Enable rstmgr alert crash dump capture.
    CHECK_DIF_OK(dif_rstmgr_alert_info_set_enabled(&rstmgr, kDifToggleEnabled));

    LOG_INFO("Configuring alert handlers");
    // Configure the alert handler, LC controller fault checker and start
    // executing the test. Set the alert we care about to class A.
    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        &alert_handler, kTopEarlgreyAlertIdLcCtrlFatalProgError,
        kDifAlertHandlerClassA, /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleEnabled));

    // Configure class A alerts.
    CHECK_DIF_OK(dif_alert_handler_configure_class(
        &alert_handler, kDifAlertHandlerClassA, kConfigProfiles[0],
        /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleEnabled));

    LOG_INFO("Configuring fault checker");
    // Configure the LC fault_checker function.
    fault_checker_t fc = {lc_ctrl_fault_checker, lc_ctrl_inst_name};
    fault_checker = fc;

    LOG_INFO("Saving fault checker to Flash");
    // Save the fault_checker to flash.
    save_fault_checker(&fault_checker);

    LOG_INFO("Enabling watchdog and alert NMIs");
    // Enable both the watchdog and alert NMIs.
    CHECK_DIF_OK(dif_rv_core_ibex_enable_nmi(&rv_core_ibex,
                                             kDifRvCoreIbexNmiSourceAlert));
    CHECK_DIF_OK(dif_rv_core_ibex_enable_nmi(&rv_core_ibex,
                                             kDifRvCoreIbexNmiSourceWdog));

    // Initiate transition into scrap
    dif_lc_ctrl_token_t zero_token = {0, 0, 0, 0, 0, 0, 0, 0,
                                      0, 0, 0, 0, 0, 0, 0, 0};

    // DV sync message
    LOG_INFO("Begin life cycle transition");

    // Mutex acquire should always succeed, there are no competing agents
    CHECK_DIF_OK(dif_lc_ctrl_mutex_try_acquire(&lc_ctrl));
    CHECK_DIF_OK(dif_lc_ctrl_configure(&lc_ctrl, kDifLcCtrlStateScrap, false,
                                       &zero_token));
    CHECK_DIF_OK(dif_lc_ctrl_transition(&lc_ctrl));

    // halt execution
    wait_for_interrupt();

  } else if (rst_info & kDifRstmgrResetInfoEscalation) {
    LOG_INFO("Booting for the second time due to escalation reset");
    restore_fault_checker(&fault_checker);

    uint32_t interrupt_count = 0;
    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_get(kCounterInterrupt, &interrupt_count));
    uint32_t nmi_count = 0;
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(kCounterNmi, &nmi_count));

    LOG_INFO("Interrupt count %d", interrupt_count);
    LOG_INFO("NMI count %d", nmi_count);

    CHECK(interrupt_count == 0,
          "Regular ISR should not run for "
          "kTopEarlgreyAlertIdLcCtrlFatalProgError");
    CHECK(nmi_count == 0,
          "NMI should not run for kTopEarlgreyAlertIdLcCtrlFatalProgError");

    // Check that the alert handler cause is cleared after reset.
    bool is_cause = true;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, kTopEarlgreyAlertIdLcCtrlFatalProgError, &is_cause));
    CHECK(!is_cause);

    // Check that the fault register is cleared after reset.
    fault_checker.function(/*enable=*/false, fault_checker.ip_inst);

    // Check the escalation alert cause from alert dump is as expected.
    check_alert_dump();

    return true;
  } else {
    LOG_FATAL("unexpected reset info %d", rst_info);
  }

  return false;
}
