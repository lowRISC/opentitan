// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test triggers a regfile integrity error from the SV side for any
// random IP instance. The alert handler is programmed to trigger a specific
// alert for the corresponding IP.
//
// The test checks that the alert handler state indicates the correct alert
// prior to the alert, which is checked in the alert triggered interrupt. The
// test also checks that the alert handler cleared that state after reset.
// It also checks that for some IPs the corresponding bit in the fatal error
// CSR is set in the interrupt, and it is also cleared after reset.
//
// As a backup the aon timer is programmed to bark and bite, but these are
// expected not to happen since the escalation takes precedence.

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rom_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
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

// This location will be update from SV to contain the expected alert.
static volatile const uint8_t kExpectedAlertNumber = 0;

// The function to check the fault status.
typedef void (*FaultCheckerFunction)(bool, const char *inst, const char *type);

typedef struct fault_checker {
  FaultCheckerFunction function;
  const char *ip_inst;
  const char *type;
} fault_checker_t;

// This preserves the fault checker across multiple resets.
OT_SECTION(".non_volatile_scratch") uint64_t nv_fault_checker[3];

// This is the fault checker to be used. It is saved and retrieved from flash
// to preserve it across resets.
fault_checker_t fault_checker;

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
  kWdogBarkMicros = 2000,          // 2 ms
  kWdogBiteMicros = 6000,          // 6 ms
  kEscalationStartMicros = 1000,   // 1 ms
  kEscalationPhase0Micros = 1000,  // 1 ms
  kEscalationPhase1Micros = 1000,  // 1 ms
  kEscalationPhase2Micros = 1000,  // 1 ms
  kEscalationPhase3Micros = 1000,  // 1 ms
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
static dif_aes_t aes;
static dif_alert_handler_t alert_handler;
static dif_aon_timer_t aon_timer;
static dif_clkmgr_t clkmgr;
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_kmac_t kmac;
static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;
static dif_pwrmgr_t pwrmgr;
static dif_rom_ctrl_t rom_ctrl;
static dif_rstmgr_t rstmgr;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_rv_plic_t plic;
static dif_sram_ctrl_t sram_ctrl_main;
static dif_sram_ctrl_t sram_ctrl_ret;

static const char *we_check = "prim_reg_we_check";

static void save_fault_checker(fault_checker_t *fault_checker) {
  uint32_t function_addr = (uint32_t)(fault_checker->function);
  uint32_t ip_inst_addr = (uint32_t)(fault_checker->ip_inst);
  uint32_t type_addr = (uint32_t)(fault_checker->type);
  CHECK(flash_ctrl_testutils_write(
      &flash_ctrl_state,
      (uint32_t)(&nv_fault_checker[0]) - TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
      0, &function_addr, kDifFlashCtrlPartitionTypeData, 1));
  CHECK(flash_ctrl_testutils_write(
      &flash_ctrl_state,
      (uint32_t)(&nv_fault_checker[1]) - TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
      0, &ip_inst_addr, kDifFlashCtrlPartitionTypeData, 1));
  CHECK(flash_ctrl_testutils_write(
      &flash_ctrl_state,
      (uint32_t)(&nv_fault_checker[2]) - TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
      0, &type_addr, kDifFlashCtrlPartitionTypeData, 1));
}

static void restore_fault_checker(fault_checker_t *fault_checker) {
  fault_checker->function = (FaultCheckerFunction)nv_fault_checker[0];
  fault_checker->ip_inst = (char *)nv_fault_checker[1];
  fault_checker->type = (char *)nv_fault_checker[2];
}

static const char *no_name = "unidentified";

// It would be handy to generate these.
static const char *adc_ctrl_inst_name = "adc_ctrl";
static const char *aes_inst_name = "aes";
static const char *aon_timer_inst_name = "aon_timer";
static const char *clkmgr_inst_name = "clkmgr";
static const char *csrng_inst_name = "csrng";
static const char *edn0_inst_name = "edn0";
static const char *edn1_inst_name = "edn1";
static const char *entropy_src_inst_name = "entropy_src";
// TODO test u_eflash.u_flash alert 35?
static const char *flash_ctrl_inst_name = "flash_ctrl";
static const char *gpio_inst_name = "gpio";
static const char *hmac_inst_name = "hmac";
static const char *i2c0_inst_name = "i2c0";
static const char *i2c1_inst_name = "i2c1";
static const char *i2c2_inst_name = "i2c2";
static const char *keymgr_inst_name = "keymgr";
static const char *kmac_inst_name = "kmac";
// TODO test fatal prog and fatal check, alerts 14 and 15. They don't have
// onehot_checkers. But we will probably need to cause both u_reg, and
// u_reg_tap checkers.
static const char *lc_ctrl_inst_name = "lc_ctrl";
static const char *otbn_inst_name = "otbn";
// TODO test fatal macro and fatal check, alerts 11 and 12.
static const char *otp_ctrl_inst_name = "otp_ctrl";
static const char *pattgen_inst_name = "pattgen";
static const char *pinmux_inst_name = "pinmux";
static const char *pwm_inst_name = "pwm";
static const char *pwrmgr_inst_name = "pwrmgr";
static const char *rom_ctrl_inst_name = "rom_ctrl";
static const char *rstmgr_inst_name = "rstmgr";
// TODO we don't yet test fatal SW error, alert 57.
static const char *rv_core_ibex_inst_name = "rv_core_ibex";
static const char *rv_dm_inst_name = "rv_dm";
static const char *rv_plic_inst_name = "rv_plic";
static const char *rv_timer_inst_name = "rv_timer";
static const char *sensor_ctrl_inst_name = "sensor_ctrl";
static const char *spi_host0_inst_name = "spi_host0";
static const char *spi_host1_inst_name = "spi_host1";
static const char *spi_device_inst_name = "spi_device";
static const char *sram_ctrl_main_inst_name = "sram_ctrl_main";
static const char *sram_ctrl_ret_inst_name = "sram_ctrl_ret";
static const char *sysrst_ctrl_inst_name = "sysrst_ctrl";
static const char *uart0_inst_name = "uart0";
static const char *uart1_inst_name = "uart1";
static const char *uart2_inst_name = "uart2";
static const char *uart3_inst_name = "uart3";
static const char *usbdev_inst_name = "usbdev";

static void trivial_fault_checker(bool enable, const char *ip_inst,
                                  const char *type) {
  CHECK(enable == enable);
}

static void aes_fault_checker(bool enable, const char *ip_inst,
                              const char *type) {
  // Check the aes integrity fatal error code.
  bool status;
  CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusAlertFatalFault, &status));
  CHECK(status == enable, "For %s got 0x%x, expected 0x%x", ip_inst, status,
        enable);
}

static void clkmgr_fault_checker(bool enable, const char *ip_inst,
                                 const char *type) {
  // Check the clkmgr integrity fatal error code.
  dif_clkmgr_fatal_err_codes_t codes;
  CHECK_DIF_OK(dif_clkmgr_fatal_err_code_get_codes(&clkmgr, &codes));
  uint32_t expected = enable ? kDifClkmgrFatalErrTypeRegfileIntegrity : 0;
  CHECK(codes == expected, "For %s got codes 0x%x, expected 0x%x", ip_inst,
        codes, expected);
}

static void flash_ctrl_fault_checker(bool enable, const char *ip_inst,
                                     const char *type) {
  dif_flash_ctrl_faults_t faults;
  CHECK_DIF_OK(dif_flash_ctrl_get_faults(&flash_ctrl_state, &faults));
  CHECK(faults.register_integrity_error == enable,
        "For %s got codes 0x%x, expected 0x%x", ip_inst,
        faults.register_integrity_error, enable);
}

/*
// TODO(#14518) hmac cannot read fault_status register.
static void hmac_fault_checker(bool enable) {
  // Check the hmac integrity fatal error code.
  dif_kmac_status_t status;
  CHECK_DIF_OK(dif_kmac_get_status(&keymgr, &codes));
  if (enable) {
    CHECK(status.faults == 1, "Got faults 0x%x", status.faults);
  } else {
    CHECK(status.faults == 0, "Got codes 0x%x", status.faults);
  }
}
*/

/*
// TODO(#14518) keymgr cannot read fault_status register.
static void keymgr_fault_checker(bool enable) {
  // Check the keymgr integrity fatal error code.
  dif_kmac_status_t status;
  CHECK_DIF_OK(dif_kmac_get_status(&keymgr, &codes));
  if (enable) {
    CHECK(status.faults == 1, "Got faults 0x%x", status.faults);
  } else {
    CHECK(status.faults == 0, "Got codes 0x%x", status.faults);
  }
}
*/

static void kmac_fault_checker(bool enable, const char *ip_inst,
                               const char *type) {
  // Check the kmac integrity fatal error code.
  dif_kmac_status_t status;
  uint32_t expected = enable ? 1 : 0;
  CHECK_DIF_OK(dif_kmac_get_status(&kmac, &status));
  CHECK(status.faults == expected, "For %s got codes 0x%x, expected 0x%x",
        ip_inst, status.faults, expected);
}

static void lc_ctrl_fault_checker(bool enable, const char *ip_inst,
                                  const char *type) {
  // Check the lc_ctrl integrity fatal error code.
  dif_lc_ctrl_status_t status;
  CHECK_DIF_OK(dif_lc_ctrl_get_status(&lc_ctrl, &status));
  bitfield_field32_t relevant_field = {
      .mask = UINT32_MAX, .index = kDifLcCtrlStatusCodeTooManyTransitions};
  uint32_t mask = bitfield_field32_write(0, relevant_field, UINT32_MAX);
  uint32_t relevant_status = status & mask;
  uint32_t expected_status =
      enable
          ? (bitfield_bit32_write(0, kDifLcCtrlStatusCodeBusIntegError, true) &
             mask)
          : 0;
  CHECK(relevant_status == expected_status,
        "For %s got codes 0x%x, expected 0x%x", ip_inst, relevant_status,
        expected_status);
}

/*
// TODO(#14518) otbn cannot read fault_status register.
static void otbn_ctrl_fault_checker(bool enable) {
  // Check the otbn integrity fatal error code.
  dif_otbn_err_bits_t codes;
  // TODO we seem to be missing a dif to read FATAL_ALERT_CAUSE.
  CHECK_DIF_OK(dif_otbn_get_err_bits(&otbn, &codes));
  if (enable) {
    CHECK(status.codes == kDifOtbn??, "Got codes 0x%x", codes);
  } else {
    CHECK(codes == 0, "Got codes 0x%x", codes);
  }
}
*/

static void otp_ctrl_fault_checker(bool enable, const char *ip_inst,
                                   const char *type) {
  // Check the otp_ctrl integrity fatal error code.
  dif_otp_ctrl_status_t status;
  uint32_t expected_codes;
  uint32_t relevant_codes;
  uint32_t relevant_mask =
      bitfield_bit32_write(UINT32_MAX, kDifOtpCtrlStatusCodeDaiIdle, false);
  relevant_mask = bitfield_bit32_write(
      relevant_mask, kDifOtpCtrlStatusCodeCheckPending, false);
  CHECK_DIF_OK(dif_otp_ctrl_get_status(&otp_ctrl, &status));
  relevant_codes = status.codes & relevant_mask;
  expected_codes = enable ? (1 << kDifOtpCtrlStatusCodeBusIntegError) : 0;
  CHECK(relevant_codes == expected_codes,
        "For %s got codes 0x%x, expected 0x%x", ip_inst, relevant_codes,
        expected_codes);
}

static void pwrmgr_fault_checker(bool enable, const char *ip_inst,
                                 const char *type) {
  // Check the pwrmgr integrity fatal error code.
  dif_pwrmgr_fatal_err_codes_t codes;
  CHECK_DIF_OK(dif_pwrmgr_fatal_err_code_get_codes(&pwrmgr, &codes));
  uint32_t expected_codes = enable ? kDifPwrmgrFatalErrTypeRegfileIntegrity : 0;
  CHECK(codes == expected_codes, "For %s got codes 0x%x, expected 0x%x",
        ip_inst, codes, expected_codes);
}

static void rom_ctrl_fault_checker(bool enable, const char *ip_inst,
                                   const char *type) {
  dif_rom_ctrl_fatal_alert_causes_t codes;
  CHECK_DIF_OK(dif_rom_ctrl_get_fatal_alert_cause(&rom_ctrl, &codes));
  uint32_t expected_codes =
      enable ? bitfield_bit32_write(0, kDifRomCtrlFatalAlertCauseIntegrityError,
                                    true)
             : 0;
  CHECK(codes == expected_codes, "For %s got codes 0x%x, expected 0x%x",
        ip_inst, codes, expected_codes);
}

static void rstmgr_fault_checker(bool enable, const char *ip_inst,
                                 const char *type) {
  // Check the rstmgr integrity fatal error code.
  dif_rstmgr_fatal_err_codes_t codes;
  CHECK_DIF_OK(dif_rstmgr_fatal_err_code_get_codes(&rstmgr, &codes));
  uint32_t expected_codes = enable ? kDifRstmgrFatalErrTypeRegfileIntegrity : 0;
  CHECK(codes == expected_codes, "For %s got codes 0x%x, expected 0x%x",
        ip_inst, codes, expected_codes);
}

static void rv_core_ibex_fault_checker(bool enable, const char *ip_inst,
                                       const char *type) {
  dif_rv_core_ibex_error_status_t codes;
  CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  // TODO determine which bit is set by onehot_checker:
  // kDifRvCoreIbexErrorStatusRegisterTransmissionIntegrity or
  // kDifRvCoreIbexErrorStatusFatalResponseIntegrity or
  // kDifRvCoreIbexErrorStatusFatalInternalError
  uint32_t expected_codes =
      enable ? kDifRvCoreIbexErrorStatusRegisterTransmissionIntegrity : 0;
  CHECK(codes == expected_codes, "For %s got codes 0x%x, expected 0x%x",
        ip_inst, codes, expected_codes);
}

static void generic_sram_ctrl_fault_checker(const dif_sram_ctrl_t *sram_ctrl,
                                            bool enable, const char *ip_inst,
                                            const char *type) {
  dif_sram_ctrl_status_bitfield_t codes;
  CHECK_DIF_OK(dif_sram_ctrl_get_status(sram_ctrl, &codes));
  uint32_t expected_codes = enable ? kDifSramCtrlStatusBusIntegErr : 0;
  CHECK(codes == expected_codes, "For %s got codes 0x%x, expected 0x%x",
        ip_inst, codes, expected_codes);
}

static void sram_ctrl_main_fault_checker(bool enable, const char *ip_inst,
                                         const char *type) {
  generic_sram_ctrl_fault_checker(&sram_ctrl_main, enable, ip_inst, type);
}

static void sram_ctrl_ret_fault_checker(bool enable, const char *ip_inst,
                                        const char *type) {
  generic_sram_ctrl_fault_checker(&sram_ctrl_ret, enable, ip_inst, type);
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
    restore_fault_checker(&fault_checker);
    CHECK(false, "For %s, reset count %d got too many interrupts (%d)",
          fault_checker.ip_inst, reset_count, interrupt_count);
  }
  flash_ctrl_testutils_counter_set_at_least(
      &flash_ctrl_state, kCounterInterrupt, interrupt_count + 1);

  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    uint32_t irq =
        (irq_id - (dif_rv_plic_irq_id_t)
                      kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);

    // We should not get aon timer interrupts since escalation suppresses them.
    CHECK(false, "Unexpected aon timer interrupt %0d", irq);
  } else if (peripheral == kTopEarlgreyPlicPeripheralAlertHandler) {
    // Don't acknowledge the interrupt to alert_handler so it escalates.
    CHECK(fault_checker.function);
    CHECK(fault_checker.ip_inst);
    CHECK(fault_checker.type);
    // Fatal alerts are only cleared by reset.
    fault_checker.function(/*enable=*/true, fault_checker.ip_inst,
                           fault_checker.type);
  }

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
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));

  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));

  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR), &lc_ctrl));

  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));

  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));

  CHECK_DIF_OK(dif_rom_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR), &rom_ctrl));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR),
      &sram_ctrl_main));

  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR),
      &sram_ctrl_ret));
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
       .duration_cycles = udiv64_slow(
           kEscalationPhase0Micros * kClockFreqPeripheralHz, 1000000,
           /*rem_out=*/NULL)},
      {.phase = kDifAlertHandlerClassStatePhase1,
       .signal = 1,
       .duration_cycles = udiv64_slow(
           kEscalationPhase1Micros * kClockFreqPeripheralHz, 1000000,
           /*rem_out=*/NULL)},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 3,
       .duration_cycles = udiv64_slow(
           kEscalationPhase2Micros * kClockFreqPeripheralHz, 1000000,
           /*rem_out=*/NULL)}};

  uint32_t deadline_cycles =
      udiv64_slow(kEscalationStartMicros * kClockFreqPeripheralHz, 1000000,
                  /*rem_out=*/NULL);
  LOG_INFO("Configuring class A with %0d cycles and %0d occurrences",
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

/**
 * Execute the aon timer interrupt test.
 */
static void execute_test(const dif_aon_timer_t *aon_timer) {
  alert_handler_config();

  // Select the fault_checker function, depending on kExpectedAlertNumber.
  switch (kExpectedAlertNumber) {
    case kTopEarlgreyAlertIdAdcCtrlAonFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, adc_ctrl_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdAesFatalFault: {
      fault_checker_t fc = {aes_fault_checker, aes_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdAonTimerAonFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, aon_timer_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdClkmgrAonFatalFault: {
      fault_checker_t fc = {clkmgr_fault_checker, clkmgr_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdCsrngFatalAlert: {
      fault_checker_t fc = {trivial_fault_checker, csrng_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdEdn0FatalAlert: {
      fault_checker_t fc = {trivial_fault_checker, edn0_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdEdn1FatalAlert: {
      fault_checker_t fc = {trivial_fault_checker, edn1_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdEntropySrcFatalAlert: {
      fault_checker_t fc = {trivial_fault_checker, entropy_src_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    // TODO, add mechanism to inject kTopEarlgreyAlertIdFlashCtrlFatalErr
    // alerts, and corresponding CSR bit to check. See flash_ctrl.sv around
    // line 1033.
    // TODO for new fatals do as in otp, forcing submodule outputs.
    case kTopEarlgreyAlertIdFlashCtrlFatalStdErr: {
      fault_checker_t fc = {flash_ctrl_fault_checker, flash_ctrl_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdGpioFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, gpio_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdHmacFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, hmac_inst_name, we_check};
      // TODO(#14518)
      LOG_INFO("Expected alert %d hmac fault check is yet unimplemented",
               kExpectedAlertNumber);
      /*
        fault_checker = {hmac_fault_checker, hmac_inst, we_check};
      */
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdI2c0FatalFault: {
      fault_checker_t fc = {trivial_fault_checker, i2c0_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdI2c1FatalFault: {
      fault_checker_t fc = {trivial_fault_checker, i2c1_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdI2c2FatalFault: {
      fault_checker_t fc = {trivial_fault_checker, i2c2_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdKeymgrFatalFaultErr: {
      fault_checker_t fc = {trivial_fault_checker, keymgr_inst_name, we_check};
      // TODO(#14518)
      LOG_INFO("Expected alert %d keymgr fault check is yet unimplemented",
               kExpectedAlertNumber);
      /*
        fault_checker = keymgr_fault_checker;
      */
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdKmacFatalFaultErr: {
      fault_checker_t fc = {kmac_fault_checker, kmac_inst_name, we_check};
      fault_checker = fc;
    } break;
    // TODO add mechanism to inject kTopEarlgreyAlertIdLcCtrlFatalProgError by
    // forcing otp_prog_err_o from lc_ctrl_fsm and
    // kTopEarlgreyAlertIdLcCtrlFatalStateError using sparse fsm.
    // alerts, and corresponding CSR bit to check.
    case kTopEarlgreyAlertIdLcCtrlFatalBusIntegError: {
      fault_checker_t fc = {lc_ctrl_fault_checker, lc_ctrl_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdOtbnFatal: {
      fault_checker_t fc = {trivial_fault_checker, otbn_inst_name, we_check};
      // TODO(#14518)
      LOG_INFO("Expected alert %d otbn fault check is yet unimplemented",
               kExpectedAlertNumber);
      /*
        fault_checker = otbn_fault_checker;
      */
      fault_checker = fc;
    } break;
      // TODO add mechanism to inject:
      // kTopEarlgreyAlertIdOtpCtrlFatalCheckError sparse fsm
      // kTopEarlgreyAlertIdOtpCtrlFatalMacroError uncorrectable ecc from macro
      // In any partition otp_ctrl_part_unbuf error_q = MacroEccUncorrError
      // kTopEarlgreyAlertIdOtpCtrlFatalPrimOtpAlert force at prim_otp interface
      // u_otp output fatal_alert_o.
      // forcing otp_prog_err_o from lc_ctrl_fsm and
      // kTopEarlgreyAlertIdLcCtrlFatalStateError using sparse fsm.
      // alerts, and corresponding CSR bit to check.
    case kTopEarlgreyAlertIdOtpCtrlFatalBusIntegError: {
      fault_checker_t fc = {otp_ctrl_fault_checker, otp_ctrl_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdPattgenFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, pattgen_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdPinmuxAonFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, pinmux_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdPwmAonFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, pwm_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdPwrmgrAonFatalFault: {
      fault_checker_t fc = {pwrmgr_fault_checker, pwrmgr_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdRomCtrlFatal: {
      fault_checker_t fc = {rom_ctrl_fault_checker, rom_ctrl_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    // TODO kTopEarlgreyAlertIdRstmgrAonFatalCnstyFault using sparse fsm or
    // idle counter.
    case kTopEarlgreyAlertIdRstmgrAonFatalFault: {
      fault_checker_t fc = {rstmgr_fault_checker, rstmgr_inst_name, we_check};
      fault_checker = fc;
    } break;
    // TODO kTopEarlgreyAlertIdRvCoreIbexFatalSwErr write to fatal_sw_err
    case kTopEarlgreyAlertIdRvCoreIbexFatalHwErr: {
      fault_checker_t fc = {rv_core_ibex_fault_checker, rv_core_ibex_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdRvDmFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, rv_dm_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdRvPlicFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, rv_plic_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdRvTimerFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, rv_timer_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdSensorCtrlFatalAlert: {
      fault_checker_t fc = {trivial_fault_checker, sensor_ctrl_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdSpiDeviceFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, spi_device_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdSpiHost0FatalFault: {
      fault_checker_t fc = {trivial_fault_checker, spi_host0_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdSpiHost1FatalFault: {
      fault_checker_t fc = {trivial_fault_checker, spi_host1_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdSramCtrlMainFatalError: {
      fault_checker_t fc = {sram_ctrl_main_fault_checker,
                            sram_ctrl_main_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdSramCtrlRetAonFatalError: {
      fault_checker_t fc = {sram_ctrl_ret_fault_checker,
                            sram_ctrl_ret_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdSysrstCtrlAonFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, sysrst_ctrl_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdUart0FatalFault: {
      fault_checker_t fc = {trivial_fault_checker, uart0_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdUart1FatalFault: {
      fault_checker_t fc = {trivial_fault_checker, uart1_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdUart2FatalFault: {
      fault_checker_t fc = {trivial_fault_checker, uart2_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdUart3FatalFault: {
      fault_checker_t fc = {trivial_fault_checker, uart3_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdUsbdevFatalFault: {
      fault_checker_t fc = {trivial_fault_checker, usbdev_inst_name, we_check};
      fault_checker = fc;
    } break;
    default: {
      LOG_ERROR("Unexpected fault");
    }
  }
  // Save the fault_checker to flash.
  save_fault_checker(&fault_checker);

  // Enable NMI
  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceAlert));

  set_aon_timers(aon_timer);

  LOG_INFO("Expected alert is %d for %s", kExpectedAlertNumber,
           fault_checker.ip_inst);

  // Trigger the SV side to inject fault.
  // DO NOT CHANGE THIS: it is used to notify the SV side.
  LOG_INFO("Ready for fault injection");

  wait_for_interrupt();
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
    restore_fault_checker(&fault_checker);
    CHECK(false, "Ip %d Got too many resets (%d)", fault_checker.ip_inst,
          reset_count);
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
    execute_test(&aon_timer);
  } else if (rst_info == kDifRstmgrResetInfoEscalation) {
    restore_fault_checker(&fault_checker);

    LOG_INFO("Booting for the second time due to escalation reset");

    int interrupt_count = flash_ctrl_testutils_counter_get(kCounterInterrupt);
    CHECK(interrupt_count > 0, "Expected at least one regular interrupt");

    int nmi_interrupt_count = flash_ctrl_testutils_counter_get(kCounterNmi);
    CHECK(nmi_interrupt_count > 0, "Expected at least one nmi");

    // Check the alert handler cause is cleared.
    bool is_cause = true;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, kExpectedAlertNumber, &is_cause));
    CHECK(!is_cause);

    // Check the fault register is clear.
    fault_checker.function(/*enable=*/false, fault_checker.ip_inst,
                           fault_checker.type);
  } else {
    LOG_ERROR("Unexpected rst_info=0x%x", rst_info);
    return false;
  }

  return true;
}
