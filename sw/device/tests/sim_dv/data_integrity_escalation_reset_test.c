// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test triggers a ram read uncorrectable error created from the SV side
// for a specific address. The alert handler is programmed to trigger a specific
// alert for the ibex. The injection address is randomly selected by the SV
// sequence and can either be in the main SRAM or in the retention SRAM. For the
// main SRAM the SV sequence also randomly selects whether it injects a data
// error, or an instruction error in a test function residing in the main SRAM.
//
// The test checks that the alert handler state indicates the correct alert
// prior to reset, which is checked in the alert triggered interrupt. The
// test also checks that the alert handler cleared that state after reset.  It
// also checks that the corresponding bit in the ibex fatal error CSR is set in
// the interrupt, and it is also cleared after reset.
//
// As a backup the aon timer is programmed to bark and bite, but these are
// expected not to happen since the escalation takes precedence. In particular,
// the timeouts are set so that bark and bite happen during the escalation phase
// where lc_escalate_en is asserted, which halts the watchdog timers.
//
// The alert_handler is programmed to escalate on the first alert event it
// registers. It is also programmed to do nothing in its first escalation phase
// so that the exception handlers and regular ISRs can execute before the NMI is
// triggered in the subsequent escalation phase.
//
// In summary, the test comprises the following steps:
//
// 0) SV sequence waits until test is running and the test function has been
// loaded to SRAM. It then randomly decides where to inject a fault, and
// communicates this to the program via symbol overwrites.
//
// 1) Test sets up peripherals. Randomly choose the alert class to use for the
// test.
//
// 2) Either read a corrupted memory location in main or retention SRAM, or
// jump to a corrupted test function in SRAM.
//
// 3) Alert handler escalates right away when seeing the first alert
// event. It enters phase 0 where it just waits for 200us without triggering any
// actions so that regular exception handlers can execute (these would
// otherwise be masked by the NMI).
//
// 4a) Regular ISR acknowledges alert handler has indeed escalated.
//
// 4b) Exception handler acknowledges either load integrity fault or instruction
// access fault.
//
// 5) Alert handler moves on to the next escalation phase and triggers an NMI.
//
// 6) NMI handler executes and checks that NMI is not due to Wdog, due to alert
// handler escalation. Since we do not clear the escalation, the NMI handler may
// execute several times, which will be reflected by a > 1 NMI count in the
// flash counters.
//
// 7) Alert handler moves on to the next escalation phase and asserts
// lc_escalate_en, which renders the chip inert. The Wdog should stop running,
// which is checked implicitly, since both bite and bark have been programmed to
// trigger within this escalation phase.
//
// 8) Alert handler moves on to the last excalation phase and resets the chip.
//
// 9) The chip reboots, and the test checks the alert handler state and the
// various interrupt counts maintained in flash.
//
// Throughout the entire test, we do not expect any Wdog bark or bite events.

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
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/nv_counter_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
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

// This location will be update from SV to indicate the fault target for this
// test. The SV side randomly selects between data errors on main and retention
// SRAM, and instruction errors in a program that is loaded in the main SRAM.
static volatile const uint32_t kFaultTarget = 0;

static const uint32_t kExpectedAlertNumber =
    kTopEarlgreyAlertIdRvCoreIbexFatalHwErr;

// Alert class to use for the test. Will be chosen randomly by the test SW.
static volatile dif_alert_handler_class_t alert_class_to_use;

static volatile uint32_t reset_count;

enum {
  // Counter for resets.
  kCounterReset,
  // Counter for regular interrupts.
  kCounterInterrupt,
  // Counter for NMIs.
  kCounterNmi,
  // Counter for exceptions
  kCounterException
};

/**
 * Enums for identifying the fault injection target.
 */
enum {
  kFaultTargetMainSramData,
  kFaultTargetRetSramData,
  kFaultTargetMainSramInstr
};

/**
 * Program the alert handler to escalate on alerts upto phase 2 (i.e. reset).
 * Also program the aon timer with:
 * - bark after escalation starts, so the interrupt is suppressed by escalation,
 * - bite after escalation reset, so we should not get timer reset.
 */
enum {
  // Note that the escalation phase times below define the length of each phase,
  // not when they start.
  // The starting time is given by the aggregate of previous phase lengths, and
  // is noted with @ below.
  // @0 us -> in this phase we will not do anything so that the exception
  // handlers have time to execute.
  kEscalationPhase0Micros = 200,
  // @200 us -> in this phase we will raise an NMI
  kEscalationPhase1Micros = 200,
  // @400 us -> in this phase we will assert lc_escalate_en
  kEscalationPhase2Micros = 200,
  // @600 us -> in this phase we will reset the chip
  kEscalationPhase3Micros = 200,
  // These are set so that both events happen in Phase2 of the escalation
  // protocol, which asserts lc_escalate_en. That should prevent the Wdog
  // from running and sending out an NMI on its own (we check in the NMI
  // handler below that this does not happen).
  kWdogBarkMicros = 450,
  kWdogBiteMicros = 500,
  // We expect exactly one reset
  kMaxResets = 1,
  kMaxInterrupts = 30,
};

static_assert(
    kWdogBarkMicros < kWdogBiteMicros &&
        kWdogBarkMicros > (kEscalationPhase0Micros + kEscalationPhase1Micros),
    "The wdog bite shall after the NMI phase when lc_escalate_en is asserted.");
/**
 * Main SRAM addresses used in the sram_function_test.
 */
enum {
  kSramStart = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR,
  kSramEnd = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR +
             TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES,
  kSramRetStart = TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR,
};

/**
 * Program in main SRAM to jump to for testing corruption of instruction
 * integrity.
 *
 * Using this program is convenient, since the sram_program.ld script ensures
 * that the entry point will be mapped to the start of the main SRAM.
 */
OT_SECTION(".data.sram_function_test")
OT_NOINLINE
static void sram_function_test(void) {
  uint32_t pc = 0;
  asm("auipc %[pc], 0;" : [pc] "=r"(pc));
  LOG_INFO("PC: %p, SRAM: [%p, %p)", pc, kSramStart, kSramEnd);
  CHECK(pc >= kSramStart && pc < kSramEnd, "PC is outside the main SRAM");
}
// Make the address of this function available via a global constant that SV can
// read.
volatile static const uint32_t kSramFunctionTestAddress =
    (uint32_t)sram_function_test;

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
  uint32_t interrupt_count = 0;
  CHECK_STATUS_OK(
      flash_ctrl_testutils_counter_get(kCounterInterrupt, &interrupt_count));
  if (interrupt_count > kMaxInterrupts) {
    CHECK(false, "Reset count %d got too many interrupts (%d)", reset_count,
          interrupt_count);
  }
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_set_at_least(
      &flash_ctrl_state, kCounterInterrupt, interrupt_count + 1));

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
    CHECK(
        irq_id == kTopEarlgreyPlicIrqIdAlertHandlerClassa + alert_class_to_use,
        "Unexpected irq_id, expected %d, got %d",
        kTopEarlgreyPlicIrqIdAlertHandlerClassa + alert_class_to_use, irq_id);
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
                                             kDifToggleDisabled));
  }

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));
  LOG_INFO("Regular external ISR exiting");
}

/**
 * Load integrity error exception handler.
 *
 * Handles load integrity error exceptions on Ibex.
 */
void ottf_load_integrity_error_handler(void) {
  LOG_INFO("At load integrity error handler");

  CHECK(kFaultTarget != kFaultTargetMainSramInstr,
        "Expected fault target 0 or 1, got %d", kFaultTarget);

  uint32_t mtval = ibex_mtval_read();
  CHECK(mtval == kErrorRamAddress, "Unexpected mtval: expected 0x%x, got 0x%x",
        kErrorRamAddress, mtval);

  // Increment the exception count.
  uint32_t exception_count = 0;
  CHECK_STATUS_OK(
      flash_ctrl_testutils_counter_get(kCounterException, &exception_count));
  if (exception_count > kMaxInterrupts) {
    LOG_INFO("Saturating exception counter at %d", exception_count);
  } else {
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_set_at_least(
        &flash_ctrl_state, kCounterException, exception_count + 1));
  }

  rv_core_ibex_fault_checker(true);

  LOG_INFO("Load integrity error handler exiting");
}

/**
 * Instruction access exception handler.
 *
 * Handles instruction access faults on Ibex.
 */
void ottf_instr_access_fault_handler(void) {
  LOG_INFO("At instr access fault handler");

  CHECK(kFaultTargetMainSramInstr == 2, "Expected fault target 2, got %d",
        kFaultTarget);

  // Increment the nmi interrupt count.
  uint32_t exception_count = 0;
  CHECK_STATUS_OK(
      flash_ctrl_testutils_counter_get(kCounterException, &exception_count));
  if (exception_count > kMaxInterrupts) {
    LOG_INFO("Saturating exception counter at %d", exception_count);
  } else if (exception_count == 0) {
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_set_at_least(
        &flash_ctrl_state, kCounterException, exception_count + 1));
  }

  rv_core_ibex_fault_checker(true);

  LOG_INFO("Instr access fault handler exiting");
}

/**
 * External NMI ISR.
 *
 * Handles NMI interrupts on Ibex for either escalation or watchdog.
 */
void ottf_external_nmi_handler(void) {
  dif_rv_core_ibex_nmi_state_t nmi_state = (dif_rv_core_ibex_nmi_state_t){0};
  LOG_INFO("At NMI handler");

  // Increment the nmi interrupt count.
  uint32_t nmi_count = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(kCounterNmi, &nmi_count));
  if (nmi_count > kMaxInterrupts) {
    LOG_INFO("Saturating nmi interrupts at %d", nmi_count);
  } else {
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_set_at_least(
        &flash_ctrl_state, kCounterNmi, nmi_count + 1));
  }

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
  CHECK_DIF_OK(dif_alert_handler_get_class_state(&alert_handler,
                                                 alert_class_to_use, &state));
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
 * Program the alert handler to escalate on alerts and reset on phase 3,
 * and to start escalation after observing 1 alert event.
 */
static void alert_handler_config(void) {
  alert_class_to_use = (dif_alert_handler_class_t)rand_testutils_gen32_range(
      kDifAlertHandlerClassA, kDifAlertHandlerClassD);
  dif_alert_handler_alert_t alerts[] = {kExpectedAlertNumber};
  dif_alert_handler_class_t alert_classes[] = {alert_class_to_use};

  uint32_t cycles[4] = {0};
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(
      kEscalationPhase0Micros, &cycles[0]));
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(
      kEscalationPhase1Micros, &cycles[1]));
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(
      kEscalationPhase2Micros, &cycles[2]));
  CHECK_STATUS_OK(alert_handler_testutils_get_cycles_from_us(
      kEscalationPhase3Micros, &cycles[3]));

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0xFFFFFFFF,  // do not trigger any signal, just wait.
       .duration_cycles = cycles[0]},
      {.phase = kDifAlertHandlerClassStatePhase1,
       .signal = 0,  // NMI
       .duration_cycles = cycles[1]},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 1,  // lc_escalate_en
       .duration_cycles = cycles[2]},
      {.phase = kDifAlertHandlerClassStatePhase3,
       .signal = 3,  // reset
       .duration_cycles = cycles[3]}};

  // This test does not leverage the IRQ timeout feature of the alert
  // handler, hence deadline_cycles is set to zero. Rather, it triggers
  // escalation right away if an alert event is seen, hence threshold = 0;
  uint32_t deadline_cycles = 0;
  uint16_t threshold = 0;
  LOG_INFO("Configuring class %d with %d cycles and %d occurrences",
           alert_class_to_use, deadline_cycles, threshold);
  dif_alert_handler_class_config_t class_config[] = {{
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = threshold,
      .irq_deadline_cycles = deadline_cycles,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase3,
  }};

  dif_alert_handler_class_t classes[] = {alert_class_to_use};
  dif_alert_handler_config_t config = {
      .alerts = alerts,
      .alert_classes = alert_classes,
      .alerts_len = ARRAYSIZE(alerts),
      .classes = classes,
      .class_configs = class_config,
      .classes_len = ARRAYSIZE(class_config),
      .ping_timeout = 0,
  };

  CHECK_STATUS_OK(alert_handler_testutils_configure_all(&alert_handler, config,
                                                        kDifToggleEnabled));

  // Enables all alert handler irqs. This allows us to implicitly check that
  // we do not get spurious IRQs from the classes that are unused.
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassb, kDifToggleEnabled));
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassc, kDifToggleEnabled));
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassd, kDifToggleEnabled));
}

static void set_aon_timers() {
  uint32_t bark_cycles = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_from_us(kWdogBarkMicros,
                                                             &bark_cycles));
  uint32_t bite_cycles = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_from_us(kWdogBiteMicros,
                                                             &bite_cycles));

  LOG_INFO(
      "Wdog will bark after %u us (%u cycles) and bite after %u us (%u cycles)",
      (uint32_t)kWdogBarkMicros, bark_cycles, (uint32_t)kWdogBiteMicros,
      bite_cycles);

  // Setup the wdog bark and bite timeouts.
  CHECK_STATUS_OK(
      aon_timer_testutils_watchdog_config(&aon_timer, bark_cycles, bite_cycles,
                                          /*pause_in_sleep=*/false));
}

/**
 * Setup aon timer interrupts and trigger fault.
 *
 * The aon timers should never trigger actions because escalation should take
 * precedence.
 */
static void execute_test() {
  alert_handler_config();

  // Make sure we can receive both the watchdog and alert NMIs.
  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceAlert));
  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceWdog));

  set_aon_timers();

  // 2 is an instruction fault on main SRAM.
  if (kFaultTarget == kFaultTargetMainSramInstr) {
    LOG_INFO("Jump to corrupted SRAM test function at %x",
             kSramFunctionTestAddress);
    sram_function_test();
    CHECK(false,
          "Since the SRAM test function is corrupted, this should not be "
          "reached");
    // 0/1 are data faults on ret/main SRAM.
  } else {
    // We run this to make sure the program is callable and working correctly
    // when no instruction faults are inserted.
    LOG_INFO("Jump to SRAM test function at %x", kSramFunctionTestAddress);
    sram_function_test();
    LOG_INFO("Returned from the SRAM test function");

    LOG_INFO("Reading corrupted address 0x%x, expecting alert %d",
             kErrorRamAddress, kExpectedAlertNumber);

    // The SV side injects error when test starts.
    uint32_t data = *((uint32_t *)kErrorRamAddress);

    // This normally should not run.
    LOG_INFO("Read from address 0x%0x with expected error gets 0x%x",
             kErrorRamAddress, data);
  }

  wait_for_interrupt();
  CHECK(false, "This should not be reached");
}

bool test_main(void) {
  LOG_INFO("Entered test_main");

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
  if (reset_count > kMaxResets) {
    CHECK(false, "Got too many resets (%d)", reset_count);
  }

  // Increment reset counter to know where we are.
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_set_at_least(
      &flash_ctrl_state, kCounterReset, reset_count + 1));

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

    // Get the counts from flash.
    uint32_t interrupt_count = 0;
    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_get(kCounterInterrupt, &interrupt_count));
    uint32_t nmi_count = 0;
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(kCounterNmi, &nmi_count));
    uint32_t exception_count = 0;
    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_get(kCounterException, &exception_count));

    LOG_INFO("Interrupt count %d", interrupt_count);
    LOG_INFO("NMI count %d", nmi_count);
    LOG_INFO("Exception count %d", exception_count);

    CHECK(interrupt_count == 1, "Expected exactly one regular interrupt");
    // The NMI handler may execute multiple times during the corresponding
    // escalation phase since we do not clear/stop the escalation.
    CHECK(nmi_count > 0, "Expected at least one nmi");
    CHECK(exception_count == 1, "Expected exactly one exception");

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
