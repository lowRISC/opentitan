// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test triggers a regfile integrity error from the SV side for any
// random IP instance. The alert handler is programmed to trigger a specific
// alert for the corresponding IP.
//
// The test checks that the alert handler state indicates the correct alert
// prior to the alert, which is checked in the alert triggered NMI. The
// test also checks that the alert handler cleared that state after reset.
// It also checks that for some IPs the corresponding bit in the fatal error
// CSR is set in the interrupt, and it is also cleared after reset.
//
// For extra checking, the rstmgr is  configured to capture the alert info
// on reset, which is also used to check the alert cause is as expected.
//
// If the fault is injected in the retention SRAM, we perform an additional
// access check to make sure that local escalation blocks any SRAM accesses
// correctly.
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

#include "alert_handler_regs.h"
#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

// This location will be update from SV to contain the expected alert.
static volatile const uint8_t kExpectedAlertNumber = 0;

// Used for checking whether a load access exception has occurred.
static volatile bool load_access_exception_seen = false;

// Used for checking whether a regular alert interrupt has been seen.
static volatile bool alert_irq_seen = false;

// The function to check the fault status.
typedef void (*FaultCheckerFunction)(bool, const char *inst, const char *type);

typedef struct fault_checker {
  FaultCheckerFunction function;
  const char *ip_inst;
  const char *type;
} fault_checker_t;

// This preserves the fault checker across multiple resets.
OT_SET_BSS_SECTION(".non_volatile_scratch", uint64_t nv_fault_checker[3];)

// This is the fault checker to be used. It is saved and retrieved from flash
// to preserve it across resets.
fault_checker_t fault_checker;

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
};

/**
 * Program the alert handler to escalate on alerts through NMI and then reset.
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
  kTestTimeout = 1000,  // 1000 us
  kMaxResets = 2,
  kMaxInterrupts = 30,
};

static_assert(
    kWdogBarkMicros < kWdogBiteMicros &&
        kWdogBarkMicros > (kEscalationPhase0Micros + kEscalationPhase1Micros),
    "The wdog bite shall after the NMI phase when lc_escalate_en is asserted");

/**
 * SRAM addresses used in the test below.
 */
enum {
  kSramMainStart = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR,
  kSramRetStart = TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR,
};

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

static const char *sparse_fsm_check = "prim_sparse_fsm_flop";
static const char *we_check = "prim_reg_we_check";
static const char *rst_cnsty_check = "rst_cnsty_check";
static const char *flash_fatal_check = "flash_fatal_check";
static const char *sw_alert_check = "sw_fatal_alert_check";

static void save_fault_checker(fault_checker_t *fault_checker) {
  uint32_t function_addr = (uint32_t)(fault_checker->function);
  uint32_t ip_inst_addr = (uint32_t)(fault_checker->ip_inst);
  uint32_t type_addr = (uint32_t)(fault_checker->type);
  CHECK_STATUS_OK(flash_ctrl_testutils_write(
      &flash_ctrl_state,
      (uint32_t)(&nv_fault_checker[0]) - TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
      0, &function_addr, kDifFlashCtrlPartitionTypeData, 1));
  CHECK_STATUS_OK(flash_ctrl_testutils_write(
      &flash_ctrl_state,
      (uint32_t)(&nv_fault_checker[1]) - TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
      0, &ip_inst_addr, kDifFlashCtrlPartitionTypeData, 1));
  CHECK_STATUS_OK(flash_ctrl_testutils_write(
      &flash_ctrl_state,
      (uint32_t)(&nv_fault_checker[2]) - TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR,
      0, &type_addr, kDifFlashCtrlPartitionTypeData, 1));
}

static void restore_fault_checker(fault_checker_t *fault_checker) {
  fault_checker->function = (FaultCheckerFunction)nv_fault_checker[0];
  fault_checker->ip_inst = (char *)nv_fault_checker[1];
  fault_checker->type = (char *)nv_fault_checker[2];
}

// It would be handy to generate these.
static const char *adc_ctrl_inst_name = "adc_ctrl";
static const char *aes_inst_name = "aes";
static const char *aon_timer_inst_name = "aon_timer";
static const char *clkmgr_inst_name = "clkmgr";
static const char *csrng_inst_name = "csrng";
static const char *edn0_inst_name = "edn0";
static const char *edn1_inst_name = "edn1";
static const char *entropy_src_inst_name = "entropy_src";
static const char *flash_ctrl_inst_name = "flash_ctrl";
static const char *gpio_inst_name = "gpio";
static const char *hmac_inst_name = "hmac";
static const char *i2c0_inst_name = "i2c0";
static const char *i2c1_inst_name = "i2c1";
static const char *i2c2_inst_name = "i2c2";
static const char *keymgr_inst_name = "keymgr";
static const char *kmac_inst_name = "kmac";
// TODO: test lc_ctrl fatal_state, alert 17.
static const char *lc_ctrl_inst_name = "lc_ctrl";
static const char *otbn_inst_name = "otbn";
static const char *otp_ctrl_inst_name = "otp_ctrl";
static const char *pattgen_inst_name = "pattgen";
static const char *pinmux_inst_name = "pinmux";
static const char *pwm_inst_name = "pwm";
static const char *pwrmgr_inst_name = "pwrmgr";
static const char *rom_ctrl_inst_name = "rom_ctrl";
static const char *rstmgr_inst_name = "rstmgr";
// TODO: test rv_core_ibex fatal SW error, alert 57.
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
  uint32_t fault_code = (type == we_check) ? faults.register_integrity_error
                                           : faults.host_gnt_error;

  CHECK(fault_code == enable, "For %s got codes 0x%x, expected 0x%x", ip_inst,
        fault_code, enable);
}

static void flash_ctrl_prim_fault_checker(bool enable, const char *ip_inst,
                                          const char *type) {
  dif_flash_ctrl_faults_t faults;
  CHECK_DIF_OK(dif_flash_ctrl_get_faults(&flash_ctrl_state, &faults));

  CHECK(faults.memory_properties_error == 0,
        "For flash memory_properties err exp 1 get 0");
  CHECK(faults.read_error == 0, "For flash read err exp 1 get 0");
  CHECK(faults.prog_window_error == 0, "For flash prog_window err exp 1 get 0");
  CHECK(faults.prog_type_error == 0, "For flash prog_type err exp 1 get 0");
  CHECK(faults.host_gnt_error == 0, "For flash host_gnt err exp 1 get 0");
  CHECK(faults.host_gnt_error == 0, "For flash host_gnt err exp 1 get 0");
  CHECK(faults.register_integrity_error == 0,
        "For flash register_integrity err exp 1 get 0");
  CHECK(faults.phy_integrity_error == 0,
        "For flash phy_integrity err exp 1 get 0");
  CHECK(faults.lifecycle_manager_error == 0,
        "For flash lifecycle_manager err exp 1 get 0");
  CHECK(faults.shadow_storage_error == 0,
        "For flash shadow_storage err exp 1 get 0");
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

// This discriminates between the two faults based on type.
static void lc_ctrl_fault_checker(bool enable, const char *ip_inst,
                                  const char *type) {
  // Check the lc_ctrl integrity fatal error code.
  dif_lc_ctrl_status_t status;
  CHECK_DIF_OK(dif_lc_ctrl_get_status(&lc_ctrl, &status));
  bitfield_field32_t relevant_field = {
      .mask = UINT32_MAX, .index = kDifLcCtrlStatusCodeTooManyTransitions};
  uint32_t mask = bitfield_field32_write(0, relevant_field, UINT32_MAX);
  uint32_t relevant_status = status & mask;
  uint32_t bus_integ_error =
      bitfield_bit32_write(0, kDifLcCtrlStatusCodeBusIntegError, true);
  uint32_t state_error =
      bitfield_bit32_write(0, kDifLcCtrlStatusCodeCorrupt, true);
  uint32_t expected_status =
      enable ? (type == we_check ? bus_integ_error : state_error) : 0;
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
  dif_otp_ctrl_status_code_t exp_err = (type == we_check)
                                           ? kDifOtpCtrlStatusCodeBusIntegError
                                           : kDifOtpCtrlStatusCodeDaiError;
  expected_codes = enable ? (1 << exp_err) : 0;
  CHECK(relevant_codes == expected_codes,
        "For %s got codes 0x%x, expected 0x%x", ip_inst, relevant_codes,
        expected_codes);
}

// OTP_prim_fault does not affect open source otp_ctrl's status register.
static void otp_ctrl_prim_fault_checker(bool enable, const char *ip_inst,
                                        const char *type) {
  // Check the otp_ctrl integrity fatal error code.
  dif_otp_ctrl_status_t status;
  uint32_t expected_codes;
  CHECK_DIF_OK(dif_otp_ctrl_get_status(&otp_ctrl, &status));
  expected_codes = 1 << kDifOtpCtrlStatusCodeDaiIdle;
  CHECK(status.codes == expected_codes, "For %s got codes 0x%x, expected 0x%x",
        ip_inst, status.codes, expected_codes);
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
  uint32_t fault_code = (type == we_check)
                            ? kDifRstmgrFatalErrTypeRegfileIntegrity
                            : kDifRstmgrFatalErrTypeResetConsistency;
  uint32_t expected_codes = enable ? fault_code : 0;
  CHECK(codes == expected_codes, "For %s got codes 0x%x, expected 0x%x",
        ip_inst, codes, expected_codes);
}

static void rv_core_ibex_fault_checker(bool enable, const char *ip_inst,
                                       const char *type) {
  dif_rv_core_ibex_error_status_t codes;
  CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  // For a we_check an error code
  // (kDifRvCoreIbexErrorStatusRegisterTransmissionIntegrity) is reported. If
  // triggering a software fatal alert no error code should be seen.
  uint32_t expected_codes =
      (type == we_check) && enable
          ? kDifRvCoreIbexErrorStatusRegisterTransmissionIntegrity
          : 0;

  CHECK(codes == expected_codes, "For %s got codes 0x%x, expected 0x%x",
        ip_inst, codes, expected_codes);
}

/**
 * Load access error exception handler.
 *
 * Handles load access error exceptions on Ibex.
 * This is needed for the SRAM fault check that tries to access
 * the retention SRAM after escalation to make sure the access
 * is correctly blocked.
 *
 */
void ottf_load_store_fault_handler(void) {
  LOG_INFO("At load access error handler");

  uint32_t mtval = ibex_mtval_read();
  CHECK(mtval == kSramRetStart, "Unexpected mtval: expected 0x%x, got 0x%x",
        kSramRetStart, mtval);

  load_access_exception_seen = true;

  LOG_INFO("Load access error handler exiting");
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
  uint32_t interrupt_count = 0;
  CHECK_STATUS_OK(
      flash_ctrl_testutils_counter_get(kCounterInterrupt, &interrupt_count));
  if (interrupt_count > kMaxInterrupts) {
    restore_fault_checker(&fault_checker);
    CHECK(false, "For %s, reset count %d got too many interrupts (%d)",
          fault_checker.ip_inst, reset_count, interrupt_count);
  }
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
    CHECK(fault_checker.type);
    // Fatal alerts are only cleared by reset.
    fault_checker.function(/*enable=*/true, fault_checker.ip_inst,
                           fault_checker.type);
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

  uint16_t accum_count;
  CHECK_DIF_OK(dif_alert_handler_get_accumulator(
      &alert_handler, alert_class_to_use, &accum_count));
  LOG_INFO("Accumulator count %d", accum_count);

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
      .ping_timeout = 256,
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

static void set_aon_timers(const dif_aon_timer_t *aon_timer) {
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
      aon_timer_testutils_watchdog_config(aon_timer, bark_cycles, bite_cycles,
                                          /*pause_in_sleep=*/false));
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
    case kTopEarlgreyAlertIdFlashCtrlFatalErr: {
      fault_checker_t fc = {flash_ctrl_fault_checker, flash_ctrl_inst_name,
                            flash_fatal_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdFlashCtrlFatalStdErr: {
      fault_checker_t fc = {flash_ctrl_fault_checker, flash_ctrl_inst_name,
                            we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdFlashCtrlFatalPrimFlashAlert: {
      fault_checker_t fc = {flash_ctrl_prim_fault_checker, flash_ctrl_inst_name,
                            flash_fatal_check};
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
    // forcing otp_prog_err_o from lc_ctrl_fsm
    case kTopEarlgreyAlertIdLcCtrlFatalStateError: {
      fault_checker_t fc = {lc_ctrl_fault_checker, lc_ctrl_inst_name,
                            sparse_fsm_check};
      fault_checker = fc;
    } break;
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
      // forcing otp_prog_err_o from lc_ctrl_fsm and
      // kTopEarlgreyAlertIdLcCtrlFatalStateError using sparse fsm.
      // alerts, and corresponding CSR bit to check.
    case kTopEarlgreyAlertIdOtpCtrlFatalMacroError: {
      fault_checker_t fc = {otp_ctrl_fault_checker, otp_ctrl_inst_name,
                            sparse_fsm_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdOtpCtrlFatalPrimOtpAlert: {
      fault_checker_t fc = {otp_ctrl_prim_fault_checker, otp_ctrl_inst_name,
                            sparse_fsm_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdOtpCtrlFatalCheckError: {
      fault_checker_t fc = {otp_ctrl_fault_checker, otp_ctrl_inst_name,
                            sparse_fsm_check};
      fault_checker = fc;
    } break;
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
    case kTopEarlgreyAlertIdRstmgrAonFatalCnstyFault: {
      fault_checker_t fc = {rstmgr_fault_checker, rstmgr_inst_name,
                            rst_cnsty_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdRstmgrAonFatalFault: {
      fault_checker_t fc = {rstmgr_fault_checker, rstmgr_inst_name, we_check};
      fault_checker = fc;
    } break;
    case kTopEarlgreyAlertIdRvCoreIbexFatalSwErr: {
      fault_checker_t fc = {rv_core_ibex_fault_checker, rv_core_ibex_inst_name,
                            sw_alert_check};
      fault_checker = fc;
    } break;
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

  // Make sure we can receive both the watchdog and alert NMIs.
  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceAlert));
  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceWdog));

  set_aon_timers(aon_timer);

  LOG_INFO("Expected alert is %d for %s", kExpectedAlertNumber,
           fault_checker.ip_inst);

  // Trigger the SV side to inject fault.
  // DO NOT CHANGE THIS: it is used to notify the SV side.
  LOG_INFO("Ready for fault injection");

  if (kExpectedAlertNumber == kTopEarlgreyAlertIdRvCoreIbexFatalSwErr) {
    CHECK_DIF_OK(dif_rv_core_ibex_trigger_sw_fatal_err_alert(&rv_core_ibex));
    LOG_INFO("Software fatal alert triggered");
  }

  // OTP ecc macro error test requires otp to read backdoor injected error
  // macro.
  if (kExpectedAlertNumber == kTopEarlgreyAlertIdOtpCtrlFatalMacroError) {
    CHECK_DIF_OK(
        dif_otp_ctrl_dai_read_start(&otp_ctrl, kDifOtpCtrlPartitionHwCfg, 0));
    LOG_INFO("OTP_CTRL error inject done");
  }

  // FlashCtrlFatalErr test requires host read request.
  if (kExpectedAlertNumber == kTopEarlgreyAlertIdFlashCtrlFatalErr) {
    enum {
      kNumTestWords = 16,
      kNumTestBytes = kNumTestWords * sizeof(uint32_t),
    };
    uint32_t host_data[kNumTestWords];
    // Send host request to trigger host grant from flash_ctrl.
    mmio_region_memcpy_from_mmio32(
        mmio_region_from_addr(TOP_EARLGREY_EFLASH_BASE_ADDR),
        FLASH_CTRL_PARAM_BYTES_PER_BANK, &host_data, kNumTestBytes);
  }

  IBEX_SPIN_FOR(alert_irq_seen, kTestTimeout);
  LOG_INFO("Alert IRQ seen");

  if (kExpectedAlertNumber == kTopEarlgreyAlertIdSramCtrlRetAonFatalError) {
    LOG_INFO("Check that the retention SRAM blocks accesses");
    uint32_t data = *((uint32_t *)kSramRetStart);
    LOG_INFO("Read from address 0x%0x with expected error gets 0x%x",
             kSramRetStart, data);
    CHECK(load_access_exception_seen,
          "We expect this access to trigger a load access exception");
  }

  wait_for_interrupt();
  CHECK(false, "This should not be reached");
}

void check_alert_dump(void) {
  dif_rstmgr_alert_info_dump_segment_t dump[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];
  size_t seg_size;
  alert_handler_testutils_info_t actual_info;

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
    if (i == kExpectedAlertNumber) {
      CHECK(actual_info.alert_cause[i], "Expected alert cause %d to be set", i);
    } else {
      // It is possible some alerts can trigger others; for example, some
      // lc_ctrl faults lead to otp_ctrl faults.
      if (actual_info.alert_cause[i]) {
        LOG_INFO("Unexpected alert cause %d, may be triggered by %d", i,
                 kExpectedAlertNumber);
      }
    }
  }
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
    restore_fault_checker(&fault_checker);
    CHECK(false, "Ip %d Got too many resets (%d)", fault_checker.ip_inst,
          reset_count);
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
    // Enable rstmgr alert info capture.
    CHECK_DIF_OK(dif_rstmgr_alert_info_set_enabled(&rstmgr, kDifToggleEnabled));
    execute_test(&aon_timer);
  } else if (rst_info == kDifRstmgrResetInfoEscalation) {
    restore_fault_checker(&fault_checker);

    LOG_INFO("Booting for the second time due to escalation reset");

    uint32_t interrupt_count = 0;
    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_get(kCounterInterrupt, &interrupt_count));
    uint32_t nmi_count = 0;
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(kCounterNmi, &nmi_count));

    LOG_INFO("Interrupt count %d", interrupt_count);
    LOG_INFO("NMI count %d", nmi_count);

    // ISRs should not run if flash_ctrl or sram_ctrl_main get a fault because
    // flash or sram accesses are blocked in those cases. For lc_ctrl fatal
    // state, otp_fatal alerts tha will trigger LC to escalate, the lc_ctrl
    // blocks the CPU.
    if (kExpectedAlertNumber == kTopEarlgreyAlertIdFlashCtrlFatalStdErr ||
        kExpectedAlertNumber == kTopEarlgreyAlertIdSramCtrlMainFatalError ||
        kExpectedAlertNumber == kTopEarlgreyAlertIdLcCtrlFatalStateError ||
        kExpectedAlertNumber == kTopEarlgreyAlertIdOtpCtrlFatalMacroError ||
        kExpectedAlertNumber == kTopEarlgreyAlertIdOtpCtrlFatalCheckError) {
      CHECK(interrupt_count == 0,
            "Expected regular ISR should not run for flash_ctrl, lc_ctrl fatal "
            "state, or sram_ctrl_main faults");
      CHECK(nmi_count == 0,
            "Expected nmi should not run for flash_ctrl, lc_ctrl fatal state, "
            "or sram_ctrl_main faults");
    } else {
      CHECK(interrupt_count == 1, "Expected exactly one regular interrupt");
      CHECK(nmi_count > 0, "Expected at least one nmi");
    }

    // Check the alert handler cause is cleared.
    bool is_cause = true;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, kExpectedAlertNumber, &is_cause));
    CHECK(!is_cause);

    // Check the fault register is clear.
    fault_checker.function(/*enable=*/false, fault_checker.ip_inst,
                           fault_checker.type);
    check_alert_dump();
    return true;
  } else {
    LOG_ERROR("Unexpected rst_info=0x%x", rst_info);
    return false;
  }

  return false;
}
