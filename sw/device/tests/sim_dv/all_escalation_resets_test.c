// Copyright lowRISC contributors (OpenTitan project).
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

#if defined(OPENTITAN_IS_EARLGREY)
#include "dt/dt_adc_ctrl.h"     // Generated
#include "dt/dt_entropy_src.h"  // Generated
#include "dt/dt_flash_ctrl.h"   // Generated
#include "dt/dt_keymgr.h"       // Generated
#include "dt/dt_pattgen.h"      // Generated
#include "dt/dt_pwm.h"          // Generated
#include "dt/dt_sensor_ctrl.h"  // Generated
#include "dt/dt_sysrst_ctrl.h"  // Generated
#include "dt/dt_usbdev.h"       // Generated
#include "sw/device/lib/dif/dif_flash_ctrl.h"

#include "flash_ctrl_regs.h"  // Generated
#elif defined(OPENTITAN_IS_DARJEELING)
#include "dt/dt_keymgr_dpe.h"  // Generated
#else
#error "all_escalation_resets_test does not support this top"
#endif

#include "dt/dt_aes.h"            // Generated
#include "dt/dt_alert_handler.h"  // Generated
#include "dt/dt_aon_timer.h"      // Generated
#include "dt/dt_api.h"            // Generated
#include "dt/dt_clkmgr.h"         // Generated
#include "dt/dt_csrng.h"          // Generated
#include "dt/dt_edn.h"            // Generated
#include "dt/dt_gpio.h"           // Generated
#include "dt/dt_hmac.h"           // Generated
#include "dt/dt_i2c.h"            // Generated
#include "dt/dt_kmac.h"           // Generated
#include "dt/dt_lc_ctrl.h"        // Generated
#include "dt/dt_otbn.h"           // Generated
#include "dt/dt_otp_ctrl.h"       // Generated
#include "dt/dt_pinmux.h"         // Generated
#include "dt/dt_pwrmgr.h"         // Generated
#include "dt/dt_rom_ctrl.h"       // Generated
#include "dt/dt_rstmgr.h"         // Generated
#include "dt/dt_rv_core_ibex.h"   // Generated
#include "dt/dt_rv_dm.h"          // Generated
#include "dt/dt_rv_plic.h"        // Generated
#include "dt/dt_rv_timer.h"       // Generated
#include "dt/dt_spi_device.h"     // Generated
#include "dt/dt_spi_host.h"       // Generated
#include "dt/dt_sram_ctrl.h"      // Generated
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
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
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/ret_sram_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "alert_handler_regs.h"  // Generated

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

// This is the fault checker to be used. It is saved and retrieved from
// Retention SRAM to preserve it across resets.
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
 * SRAM address used in the test below.
 */
static uint32_t kSramRetStart;

/**
 * Objects to access the peripherals used in this test via dif/dt APIs.
 */
// Top-specific objects
#if defined(OPENTITAN_IS_EARLGREY)
static dif_flash_ctrl_state_t flash_ctrl_state;
dt_flash_ctrl_t kFlashCtrlDt = (dt_flash_ctrl_t)0;
static_assert(kDtFlashCtrlCount >= 1, "This test requires a Flash Ctrl");
static dif_rom_ctrl_t rom_ctrl;
static dt_rom_ctrl_t kRomCtrlDt = (dt_rom_ctrl_t)0;
static_assert(kDtRomCtrlCount >= 1, "This test requires a ROM CTRL");

static const char *flash_fatal_check = "flash_fatal_check";
#elif defined(OPENTITAN_IS_DARJEELING)
static dif_sram_ctrl_t sram_ctrl_mbox;
static dt_sram_ctrl_t kSramCtrlMboxDt = kDtSramCtrlMbox;
static dif_rom_ctrl_t rom_ctrl0;
static dif_rom_ctrl_t rom_ctrl1;
static dt_rom_ctrl_t kRomCtrl0Dt = kDtRomCtrl0;
static dt_rom_ctrl_t kRomCtrl1Dt = kDtRomCtrl1;
#else
#error "all_escalation_resets_test does not support this top"
#endif

// Top-agnostic objects
static const uint32_t kPlicTarget = 0;

static dif_aes_t aes;
static dif_alert_handler_t alert_handler;
static dif_aon_timer_t aon_timer;
static dif_clkmgr_t clkmgr;
static dif_kmac_t kmac;
static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;
static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_rv_plic_t plic;
static dif_sram_ctrl_t sram_ctrl_main;
static dif_sram_ctrl_t sram_ctrl_ret;

static dt_aes_t kAesDt = (dt_aes_t)0;
static_assert(kDtAesCount >= 1, "This test requires an AES");
static dt_alert_handler_t kAlertHandlerDt = (dt_alert_handler_t)0;
static_assert(kDtAlertHandlerCount >= 1, "This test needs an Alert Handler");
static dt_aon_timer_t kAonTimerDt = kDtAonTimerAon;
static dt_clkmgr_t kClkmgrDt = kDtClkmgrAon;
static dt_kmac_t kKmacDt = (dt_kmac_t)0;
static_assert(kDtKmacCount >= 1, "This test requires a KMAC instance");
static dt_lc_ctrl_t kLcCtrlDt = (dt_lc_ctrl_t)0;
static_assert(kDtLcCtrlCount >= 1, "This test requries a LC CTRL");
static dt_otp_ctrl_t kOtpCtrlDt = (dt_otp_ctrl_t)0;
static_assert(kDtOtpCtrlCount >= 1, "This test requires an OTP CTRL");
static dt_pwrmgr_t kPwrmgrDt = kDtPwrmgrAon;
static dt_rstmgr_t kRstmgrDt = kDtRstmgrAon;
static dt_rv_core_ibex_t kRvCoreIbexDt = (dt_rv_core_ibex_t)0;
static_assert(kDtRvCoreIbexCount >= 1, "This test requires an Ibex core");
static dt_rv_plic_t kRvPlicDt = (dt_rv_plic_t)0;
static_assert(kDtRvPlicCount >= 1, "This test requries an RV PLIC instance");
static dt_sram_ctrl_t kSramCtrlMainDt = kDtSramCtrlMain;
static dt_sram_ctrl_t kSramCtrlRetAonDt = kDtSramCtrlRetAon;

static const char *sparse_fsm_check = "prim_sparse_fsm_flop";
static const char *we_check = "prim_reg_we_check";
static const char *rst_cnsty_check = "rst_cnsty_check";
static const char *sw_alert_check = "sw_fatal_alert_check";

/**
 * Utilities for saving & restoring the fault checker to/from non-volatile SRAM
 * so it persists across resets.
 */
static void save_fault_checker(fault_checker_t *fault_checker) {
  uint32_t function_addr = (uint32_t)(fault_checker->function);
  uint32_t ip_inst_addr = (uint32_t)(fault_checker->ip_inst);
  uint32_t type_addr = (uint32_t)(fault_checker->type);
  CHECK_STATUS_OK(ret_sram_testutils_scratch_write(0, 1, &function_addr));
  CHECK_STATUS_OK(ret_sram_testutils_scratch_write(1, 1, &ip_inst_addr));
  CHECK_STATUS_OK(ret_sram_testutils_scratch_write(2, 1, &type_addr));
}

static void restore_fault_checker(fault_checker_t *fault_checker) {
  CHECK_STATUS_OK(ret_sram_testutils_scratch_read(
      0, 1, (uint32_t *)&(fault_checker->function)));
  CHECK_STATUS_OK(ret_sram_testutils_scratch_read(
      1, 1, (uint32_t *)&(fault_checker->ip_inst)));
  CHECK_STATUS_OK(ret_sram_testutils_scratch_read(
      2, 1, (uint32_t *)&(fault_checker->type)));
}

// Instance name definitions. TODO: It would be handy to generate these.
#if defined(OPENTITAN_IS_EARLGREY)
static const char *adc_ctrl_inst_name = "adc_ctrl";
static const char *entropy_src_inst_name = "entropy_src";
static const char *flash_ctrl_inst_name = "flash_ctrl";
static const char *i2c1_inst_name = "i2c1";
static const char *i2c2_inst_name = "i2c2";
static const char *keymgr_inst_name = "keymgr";
static const char *pattgen_inst_name = "pattgen";
static const char *pwm_inst_name = "pwm";
static const char *rom_ctrl_inst_name = "rom_ctrl";
static const char *sensor_ctrl_inst_name = "sensor_ctrl";
static const char *spi_host1_inst_name = "spi_host1";
static const char *sysrst_ctrl_inst_name = "sysrst_ctrl";
static const char *uart1_inst_name = "uart1";
static const char *uart2_inst_name = "uart2";
static const char *uart3_inst_name = "uart3";
static const char *usbdev_inst_name = "usbdev";
#elif defined(OPENTITAN_IS_DARJEELING)
static const char *keymgr_dpe_inst_name = "keymgr_dpe";
static const char *sram_ctrl_mbox_inst_name = "sram_ctrl_mbox";
static const char *rom_ctrl0_inst_name = "rom_ctrl0";
static const char *rom_ctrl1_inst_name = "rom_ctrl1";
#else
#error "all_escalation_resets_test does not support this top"
#endif

static const char *aes_inst_name = "aes";
static const char *aon_timer_inst_name = "aon_timer";
static const char *clkmgr_inst_name = "clkmgr";
static const char *csrng_inst_name = "csrng";
static const char *edn0_inst_name = "edn0";
static const char *edn1_inst_name = "edn1";
static const char *gpio_inst_name = "gpio";
static const char *hmac_inst_name = "hmac";
static const char *i2c0_inst_name = "i2c0";
static const char *kmac_inst_name = "kmac";
// TODO: test lc_ctrl fatal_state, alert 17.
static const char *lc_ctrl_inst_name = "lc_ctrl";
static const char *otbn_inst_name = "otbn";
static const char *otp_ctrl_inst_name = "otp_ctrl";
static const char *pinmux_inst_name = "pinmux";
static const char *pwrmgr_inst_name = "pwrmgr";
static const char *rstmgr_inst_name = "rstmgr";
// TODO: test rv_core_ibex fatal SW error, alert 57.
static const char *rv_core_ibex_inst_name = "rv_core_ibex";
static const char *rv_dm_inst_name = "rv_dm";
static const char *rv_plic_inst_name = "rv_plic";
static const char *rv_timer_inst_name = "rv_timer";
static const char *spi_host0_inst_name = "spi_host0";
static const char *spi_device_inst_name = "spi_device";
static const char *sram_ctrl_main_inst_name = "sram_ctrl_main";
static const char *sram_ctrl_ret_inst_name = "sram_ctrl_ret";
static const char *uart0_inst_name = "uart0";

/**
 * Define fault checkers used for checking faults in different IPs
 * during the test.
 */
static void trivial_fault_checker(bool enable, const char *ip_inst,
                                  const char *type) {
  CHECK(enable == enable);
}

static void generic_rom_ctrl_fault_checker(bool enable, const char *ip_inst,
                                           const char *type,
                                           dif_rom_ctrl_t *dif) {
  dif_rom_ctrl_fatal_alert_causes_t codes;
  CHECK_DIF_OK(dif_rom_ctrl_get_fatal_alert_cause(dif, &codes));
  uint32_t expected_codes =
      enable ? bitfield_bit32_write(0, kDifRomCtrlFatalAlertCauseIntegrityError,
                                    true)
             : 0;
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

// Fault checkers for Top-specific IP
#if defined(OPENTITAN_IS_EARLGREY)
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

static void keymgr_fault_checker(bool enable, const char *ip_inst,
                                 const char *type) {
  // TODO(#14518)
  LOG_INFO("Expected alert %d keymgr fault check is yet unimplemented",
           kDtKeymgrAlertFatalFaultErr);
  trivial_fault_checker(enable, ip_inst, type);
}

static void rom_ctrl_fault_checker(bool enable, const char *ip_inst,
                                   const char *type) {
  return generic_rom_ctrl_fault_checker(enable, ip_inst, type, &rom_ctrl);
}
#elif defined(OPENTITAN_IS_DARJEELING)
static void keymgr_dpe_fault_checker(bool enable, const char *ip_inst,
                                     const char *type) {
  // TODO(#14518)
  LOG_INFO("Expected alert %d keymgr_dpe fault check is yet unimplemented",
           kDtKeymgrDpeAlertFatalFaultErr);
  trivial_fault_checker(enable, ip_inst, type);
}

static void rom_ctrl0_fault_checker(bool enable, const char *ip_inst,
                                    const char *type) {
  return generic_rom_ctrl_fault_checker(enable, ip_inst, type, &rom_ctrl0);
}

static void rom_ctrl1_fault_checker(bool enable, const char *ip_inst,
                                    const char *type) {
  return generic_rom_ctrl_fault_checker(enable, ip_inst, type, &rom_ctrl1);
}

static void sram_ctrl_mbox_fault_checker(bool enable, const char *ip_inst,
                                         const char *type) {
  generic_sram_ctrl_fault_checker(&sram_ctrl_mbox, enable, ip_inst, type);
}
#else
#error "all_escalation_resets_test does not support this top"
#endif

// Fault checkers for the remaining top-agnostic IP
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

static void hmac_fault_checker(bool enable, const char *ip_inst,
                               const char *type) {
  // TODO(#14518)
  LOG_INFO("Expected alert %d hmac fault check is yet unimplemented",
           kDtHmacAlertFatalFault);
  trivial_fault_checker(enable, ip_inst, type);
}

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

static void otbn_fault_checker(bool enable, const char *ip_inst,
                               const char *type) {
  // TODO(#14518)
  LOG_INFO("Expected alert %d otbn fault check is yet unimplemented",
           kDtOtbnAlertFatal);
  trivial_fault_checker(enable, ip_inst, type);
}

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
void ottf_load_store_fault_handler(uint32_t *exc_info) {
  LOG_INFO("At load access error handler");

  uint32_t mtval = ibex_mtval_read();
  CHECK(mtval == kSramRetStart, "Unexpected mtval: expected 0x%x, got 0x%x",
        kSramRetStart, mtval);

  load_access_exception_seen = true;

  LOG_INFO("Load access error handler exiting");
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
void ottf_external_isr(uint32_t *exc_info) {
  dif_rv_plic_irq_id_t irq_id;

  // There may be multiple interrupts due to the alert firing, so this keeps an
  // interrupt counter and errors-out if there are too many interrupts.

  // Increment the interrupt count and detect overflows.
  uint32_t interrupt_count = 0;
  CHECK_STATUS_OK(
      ret_sram_testutils_counter_get(kCounterInterrupt, &interrupt_count));
  if (interrupt_count > kMaxInterrupts) {
    restore_fault_checker(&fault_checker);
    CHECK(false, "For %s, reset count %d got too many interrupts (%d)",
          fault_checker.ip_inst, reset_count, interrupt_count);
  }
  CHECK_STATUS_OK(ret_sram_testutils_counter_increment(kCounterInterrupt));

  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  dt_instance_id_t peripheral_id = dt_plic_id_to_instance_id(irq_id);

  if (peripheral_id == dt_aon_timer_instance_id(kDtAonTimerAon)) {
    dt_aon_timer_irq_t irq =
        dt_aon_timer_irq_from_plic_id(kDtAonTimerAon, irq_id);

    // We should not get aon timer interrupts since escalation suppresses them.
    CHECK(false, "Unexpected aon timer interrupt %d", irq);
  } else if (peripheral_id == dt_alert_handler_instance_id(kAlertHandlerDt)) {
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
  dt_alert_handler_irq_t irq =
      dt_alert_handler_irq_from_plic_id(kAlertHandlerDt, irq_id);
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
}

/**
 * External NMI ISR.
 *
 * Handles NMI interrupts on Ibex for either escalation or watchdog.
 */
void ottf_external_nmi_handler(uint32_t *exc_info) {
  dif_rv_core_ibex_nmi_state_t nmi_state = (dif_rv_core_ibex_nmi_state_t){0};
  // Increment the nmi interrupt count.
  uint32_t nmi_count = 0;
  CHECK_STATUS_OK(ret_sram_testutils_counter_get(kCounterNmi, &nmi_count));
  if (nmi_count <= kMaxInterrupts) {
    CHECK_STATUS_OK(ret_sram_testutils_counter_increment(kCounterNmi));
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
}

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
#if defined(OPENTITAN_IS_EARLGREY)
  CHECK_DIF_OK(
      dif_flash_ctrl_init_state_from_dt(&flash_ctrl_state, kFlashCtrlDt));
  CHECK_DIF_OK(dif_rom_ctrl_init_from_dt(kRomCtrlDt, &rom_ctrl));
#elif defined(OPENTITAN_IS_DARJEELING)
  CHECK_DIF_OK(dif_rom_ctrl_init_from_dt(kRomCtrl0Dt, &rom_ctrl0));
  CHECK_DIF_OK(dif_rom_ctrl_init_from_dt(kRomCtrl1Dt, &rom_ctrl1));
  CHECK_DIF_OK(dif_sram_ctrl_init_from_dt(kSramCtrlMboxDt, &sram_ctrl_mbox));
#else
#error "all_escalation_resets_test does not support this top"
#endif

  CHECK_DIF_OK(dif_aes_init_from_dt(kAesDt, &aes));
  CHECK_DIF_OK(dif_alert_handler_init_from_dt(kAlertHandlerDt, &alert_handler));
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kAonTimerDt, &aon_timer));
  CHECK_DIF_OK(dif_clkmgr_init_from_dt(kClkmgrDt, &clkmgr));
  CHECK_DIF_OK(dif_kmac_init_from_dt(kKmacDt, &kmac));
  CHECK_DIF_OK(dif_lc_ctrl_init_from_dt(kLcCtrlDt, &lc_ctrl));
  CHECK_DIF_OK(dif_otp_ctrl_init_from_dt(kOtpCtrlDt, &otp_ctrl));
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kRstmgrDt, &rstmgr));
  CHECK_DIF_OK(dif_rv_core_ibex_init_from_dt(kRvCoreIbexDt, &rv_core_ibex));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &plic));
  CHECK_DIF_OK(dif_sram_ctrl_init_from_dt(kSramCtrlMainDt, &sram_ctrl_main));
  CHECK_DIF_OK(dif_sram_ctrl_init_from_dt(kSramCtrlRetAonDt, &sram_ctrl_ret));
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
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_32_from_us(kWdogBarkMicros,
                                                                &bark_cycles));
  uint32_t bite_cycles = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_32_from_us(kWdogBiteMicros,
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
 * Initialise the map of fault checkers to use for different fault alerts.
 */
static void init_fault_checkers(fault_checker_t *checkers) {
#if defined(OPENTITAN_IS_EARLGREY)
  checkers[dt_adc_ctrl_alert_to_alert_id(kDtAdcCtrlAon,
                                         kDtAdcCtrlAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, adc_ctrl_inst_name, we_check};

  checkers[dt_entropy_src_alert_to_alert_id((dt_entropy_src_t)0,
                                            kDtEntropySrcAlertFatalAlert)] =
      (fault_checker_t){trivial_fault_checker, entropy_src_inst_name, we_check};
  static_assert(kDtEntropySrcCount >= 1, "This test needs an entropy src");

  checkers[dt_flash_ctrl_alert_to_alert_id(
      kFlashCtrlDt, kDtFlashCtrlAlertFatalErr)] = (fault_checker_t){
      flash_ctrl_fault_checker, flash_ctrl_inst_name, flash_fatal_check};
  checkers[dt_flash_ctrl_alert_to_alert_id(
      kFlashCtrlDt, kDtFlashCtrlAlertFatalStdErr)] = (fault_checker_t){
      flash_ctrl_fault_checker, flash_ctrl_inst_name, flash_fatal_check};
  checkers[dt_flash_ctrl_alert_to_alert_id(
      kFlashCtrlDt, kDtFlashCtrlAlertFatalPrimFlashAlert)] = (fault_checker_t){
      flash_ctrl_prim_fault_checker, flash_ctrl_inst_name, flash_fatal_check};

  checkers[dt_i2c_alert_to_alert_id((dt_i2c_t)1, kDtI2cAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, i2c1_inst_name, we_check};
  checkers[dt_i2c_alert_to_alert_id((dt_i2c_t)2, kDtI2cAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, i2c2_inst_name, we_check};
  static_assert(kDtI2cCount >= 3, "This test needs 3 I2C instances");

  checkers[dt_keymgr_alert_to_alert_id((dt_keymgr_t)0,
                                       kDtKeymgrAlertFatalFaultErr)] =
      (fault_checker_t){keymgr_fault_checker, keymgr_inst_name, we_check};
  static_assert(kDtKeymgrCount >= 1, "This test needs a keymgr");

  checkers[dt_pattgen_alert_to_alert_id((dt_pattgen_t)0,
                                        kDtPattgenAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, pattgen_inst_name, we_check};
  static_assert(kDtPattgenCount >= 1, "This test needs a pattgen instance");

  checkers[dt_pwm_alert_to_alert_id(kDtPwmAon, kDtPwmAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, pwm_inst_name, we_check};

  checkers[dt_rom_ctrl_alert_to_alert_id(kRomCtrlDt, kDtRomCtrlAlertFatal)] =
      (fault_checker_t){rom_ctrl_fault_checker, rom_ctrl_inst_name, we_check};

  checkers[dt_sensor_ctrl_alert_to_alert_id(kDtSensorCtrlAon,
                                            kDtSensorCtrlAlertFatalAlert)] =
      (fault_checker_t){trivial_fault_checker, sensor_ctrl_inst_name, we_check};

  checkers[dt_spi_host_alert_to_alert_id((dt_spi_host_t)1,
                                         kDtSpiHostAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, spi_host1_inst_name, we_check};
  static_assert(kDtSpiHostCount >= 2, "This test needs 2 SPI Host instances");

  checkers[dt_sysrst_ctrl_alert_to_alert_id(kDtSysrstCtrlAon,
                                            kDtSysrstCtrlAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, sysrst_ctrl_inst_name, we_check};

  checkers[dt_uart_alert_to_alert_id((dt_uart_t)1, kDtUartAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, uart1_inst_name, we_check};
  checkers[dt_uart_alert_to_alert_id((dt_uart_t)2, kDtUartAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, uart2_inst_name, we_check};
  checkers[dt_uart_alert_to_alert_id((dt_uart_t)3, kDtUartAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, uart3_inst_name, we_check};
  static_assert(kDtUartCount >= 4, "This test needs 4 UART instances");

  checkers[dt_usbdev_alert_to_alert_id((dt_usbdev_t)0,
                                       kDtUsbdevAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, usbdev_inst_name, we_check};
  static_assert(kDtUsbdevCount >= 1, "This test needs a USB Device");
#elif defined(OPENTITAN_IS_DARJEELING)
  checkers[dt_keymgr_dpe_alert_to_alert_id(
      (dt_keymgr_dpe_t)0, kDtKeymgrDpeAlertFatalFaultErr)] = (fault_checker_t){
      keymgr_dpe_fault_checker, keymgr_dpe_inst_name, we_check};
  static_assert(kDtKeymgrDpeCount >= 1, "This test needs a keymgr_dpe");

  checkers[dt_sram_ctrl_alert_to_alert_id(
      kDtSramCtrlMbox, kDtSramCtrlAlertFatalError)] = (fault_checker_t){
      sram_ctrl_mbox_fault_checker, sram_ctrl_mbox_inst_name, we_check};

  checkers[dt_rom_ctrl_alert_to_alert_id(kRomCtrl0Dt, kDtRomCtrlAlertFatal)] =
      (fault_checker_t){rom_ctrl0_fault_checker, rom_ctrl0_inst_name, we_check};
  checkers[dt_rom_ctrl_alert_to_alert_id(kRomCtrl1Dt, kDtRomCtrlAlertFatal)] =
      (fault_checker_t){rom_ctrl1_fault_checker, rom_ctrl1_inst_name, we_check};
#else
#error "all_escalation_resets_test does not support this top"
#endif

  checkers[dt_aes_alert_to_alert_id(kAesDt, kDtAesAlertFatalFault)] =
      (fault_checker_t){aes_fault_checker, aes_inst_name, we_check};

  checkers[dt_aon_timer_alert_to_alert_id(kAonTimerDt,
                                          kDtAonTimerAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, aon_timer_inst_name, we_check};

  checkers[dt_clkmgr_alert_to_alert_id(kClkmgrDt, kDtClkmgrAlertFatalFault)] =
      (fault_checker_t){clkmgr_fault_checker, clkmgr_inst_name, we_check};

  checkers[dt_csrng_alert_to_alert_id((dt_csrng_t)0, kDtCsrngAlertFatalAlert)] =
      (fault_checker_t){trivial_fault_checker, csrng_inst_name, we_check};
  static_assert(kDtCsrngCount >= 1, "This test needs a CSRNG instance");

  checkers[dt_edn_alert_to_alert_id((dt_edn_t)0, kDtEdnAlertFatalAlert)] =
      (fault_checker_t){trivial_fault_checker, edn0_inst_name, we_check};
  checkers[dt_edn_alert_to_alert_id((dt_edn_t)1, kDtEdnAlertFatalAlert)] =
      (fault_checker_t){trivial_fault_checker, edn1_inst_name, we_check};
  static_assert(kDtEdnCount >= 2, "This test needs 2 EDN instances");

  checkers[dt_gpio_alert_to_alert_id((dt_gpio_t)0, kDtGpioAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, gpio_inst_name, we_check};
  static_assert(kDtGpioCount >= 1, "This test needs 1 GPIO instance");

  checkers[dt_hmac_alert_to_alert_id((dt_hmac_t)0, kDtHmacAlertFatalFault)] =
      (fault_checker_t){hmac_fault_checker, hmac_inst_name, we_check};
  static_assert(kDtHmacCount >= 1, "This test needs 1 HMAC instance");

  checkers[dt_i2c_alert_to_alert_id((dt_i2c_t)0, kDtI2cAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, i2c0_inst_name, we_check};
  static_assert(kDtI2cCount >= 1, "This test needs at least 1 I2C instance");

  checkers[dt_kmac_alert_to_alert_id(kKmacDt, kDtKmacAlertFatalFaultErr)] =
      (fault_checker_t){kmac_fault_checker, kmac_inst_name, we_check};

  // TODO add mechanism to inject kDtLcCtrlAlertFatalProgError by
  // forcing otp_prog_err_o from lc_ctrl_fsm
  checkers[dt_lc_ctrl_alert_to_alert_id(
      kLcCtrlDt, kDtLcCtrlAlertFatalStateError)] = (fault_checker_t){
      lc_ctrl_fault_checker, lc_ctrl_inst_name, sparse_fsm_check};
  checkers[dt_lc_ctrl_alert_to_alert_id(kLcCtrlDt,
                                        kDtLcCtrlAlertFatalBusIntegError)] =
      (fault_checker_t){lc_ctrl_fault_checker, lc_ctrl_inst_name, we_check};

  checkers[dt_otbn_alert_to_alert_id((dt_otbn_t)0, kDtOtbnAlertFatal)] =
      (fault_checker_t){otbn_fault_checker, otbn_inst_name, we_check};
  static_assert(kDtOtbnCount >= 1, "This test needs at least 1 OTBN instance");

  // TODO add mechanism to inject:
  // forcing otp_prog_err_o from lc_ctrl_fsm and
  // kDtLcCtrlAlertFatalStateError using sparse fsm.
  // alerts, and corresponding CSR bit to check.
  checkers[dt_otp_ctrl_alert_to_alert_id(
      kOtpCtrlDt, kDtOtpCtrlAlertFatalMacroError)] = (fault_checker_t){
      otp_ctrl_fault_checker, otp_ctrl_inst_name, sparse_fsm_check};
  checkers[dt_otp_ctrl_alert_to_alert_id(
      kOtpCtrlDt, kDtOtpCtrlAlertFatalPrimOtpAlert)] = (fault_checker_t){
      otp_ctrl_prim_fault_checker, otp_ctrl_inst_name, sparse_fsm_check};
  checkers[dt_otp_ctrl_alert_to_alert_id(
      kOtpCtrlDt, kDtOtpCtrlAlertFatalCheckError)] = (fault_checker_t){
      otp_ctrl_fault_checker, otp_ctrl_inst_name, sparse_fsm_check};
  checkers[dt_otp_ctrl_alert_to_alert_id(kOtpCtrlDt,
                                         kDtOtpCtrlAlertFatalBusIntegError)] =
      (fault_checker_t){otp_ctrl_fault_checker, otp_ctrl_inst_name, we_check};

  checkers[dt_pinmux_alert_to_alert_id(kDtPinmuxAon,
                                       kDtPinmuxAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, pinmux_inst_name, we_check};

  checkers[dt_pwrmgr_alert_to_alert_id(kPwrmgrDt, kDtPwrmgrAlertFatalFault)] =
      (fault_checker_t){pwrmgr_fault_checker, pwrmgr_inst_name, we_check};

  checkers[dt_rstmgr_alert_to_alert_id(
      kRstmgrDt, kDtRstmgrAlertFatalCnstyFault)] = (fault_checker_t){
      rstmgr_fault_checker, rstmgr_inst_name, rst_cnsty_check};
  checkers[dt_rstmgr_alert_to_alert_id(kRstmgrDt, kDtRstmgrAlertFatalFault)] =
      (fault_checker_t){rstmgr_fault_checker, rstmgr_inst_name, we_check};

  checkers[dt_rv_core_ibex_alert_to_alert_id(
      kRvCoreIbexDt, kDtRvCoreIbexAlertFatalSwErr)] = (fault_checker_t){
      rv_core_ibex_fault_checker, rv_core_ibex_inst_name, sw_alert_check};
  checkers[dt_rv_core_ibex_alert_to_alert_id(
      kRvCoreIbexDt, kDtRvCoreIbexAlertFatalHwErr)] = (fault_checker_t){
      rv_core_ibex_fault_checker, rv_core_ibex_inst_name, we_check};

  checkers[dt_rv_dm_alert_to_alert_id((dt_rv_dm_t)0, kDtRvDmAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, rv_dm_inst_name, we_check};
  static_assert(kDtRvDmCount >= 1, "This test needs an RV DM");

  checkers[dt_rv_plic_alert_to_alert_id(kRvPlicDt, kDtRvPlicAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, rv_plic_inst_name, we_check};

  checkers[dt_rv_timer_alert_to_alert_id((dt_rv_timer_t)0,
                                         kDtRvTimerAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, rv_timer_inst_name, we_check};
  static_assert(kDtRvTimerCount >= 1, "This test needs a RV Timer");

  checkers[dt_spi_device_alert_to_alert_id((dt_spi_device_t)0,
                                           kDtSpiDeviceAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, spi_device_inst_name, we_check};
  static_assert(kDtSpiDeviceCount >= 1, "This test needs a SPI Device");

  checkers[dt_spi_host_alert_to_alert_id((dt_spi_host_t)0,
                                         kDtSpiHostAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, spi_host0_inst_name, we_check};
  static_assert(kDtSpiHostCount >= 1, "This test needs at leasst 1 SPI Host");

  checkers[dt_sram_ctrl_alert_to_alert_id(
      kSramCtrlMainDt, kDtSramCtrlAlertFatalError)] = (fault_checker_t){
      sram_ctrl_main_fault_checker, sram_ctrl_main_inst_name, we_check};
  checkers[dt_sram_ctrl_alert_to_alert_id(
      kSramCtrlRetAonDt, kDtSramCtrlAlertFatalError)] = (fault_checker_t){
      sram_ctrl_ret_fault_checker, sram_ctrl_ret_inst_name, we_check};

  checkers[dt_uart_alert_to_alert_id((dt_uart_t)0, kDtUartAlertFatalFault)] =
      (fault_checker_t){trivial_fault_checker, uart0_inst_name, we_check};
  static_assert(kDtUartCount >= 1, "This test needs at least 1 UART instance");
}

/**
 * Execute the all_escalations_reset_test.
 */
static void execute_test(const dif_aon_timer_t *aon_timer) {
  alert_handler_config();

  fault_checker_t fault_checkers[kDtAlertCount] = {{NULL, NULL, NULL}};
  init_fault_checkers((fault_checker_t *)fault_checkers);

  // Select the fault_checker function, depending on kExpectedAlertNumber.
  CHECK(kExpectedAlertNumber < kDtAlertCount,
        "Expected alert number larger than the number of alerts?");
  fault_checker_t fc = fault_checkers[kExpectedAlertNumber];
  if (fc.function == NULL || fc.ip_inst == NULL || fc.type == NULL) {
    LOG_ERROR("Unexpected fault");
  } else {
    fault_checker = fc;
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

  if (kExpectedAlertNumber ==
      dt_rv_core_ibex_alert_to_alert_id(kRvCoreIbexDt,
                                        kDtRvCoreIbexAlertFatalSwErr)) {
    CHECK_DIF_OK(dif_rv_core_ibex_trigger_sw_fatal_err_alert(&rv_core_ibex));
    LOG_INFO("Software fatal alert triggered");
  }

  // OTP ecc macro error test requires otp to read backdoor injected error
  // macro.
  if (kExpectedAlertNumber == dt_otp_ctrl_alert_to_alert_id(
                                  kOtpCtrlDt, kDtOtpCtrlAlertFatalMacroError)) {
    CHECK_DIF_OK(
        dif_otp_ctrl_dai_read_start(&otp_ctrl, kDifOtpCtrlPartitionHwCfg0, 0));
    LOG_INFO("OTP_CTRL error inject done");
  }

#if defined(OPENTITAN_IS_EARLGREY)
  // FlashCtrlFatalErr test requires host read request.
  if (kExpectedAlertNumber == dt_flash_ctrl_alert_to_alert_id(
                                  kFlashCtrlDt, kDtFlashCtrlAlertFatalErr)) {
    enum {
      kNumTestWords = 16,
      kNumTestBytes = kNumTestWords * sizeof(uint32_t),
    };
    uint32_t host_data[kNumTestWords];
    // Send host request to trigger host grant from flash_ctrl.
    mmio_region_memcpy_from_mmio32(
        mmio_region_from_addr(
            dt_flash_ctrl_reg_block(kFlashCtrlDt, kDtFlashCtrlRegBlockMem)),
        FLASH_CTRL_PARAM_BYTES_PER_BANK, &host_data, kNumTestBytes);
  }
#elif defined(OPENTITAN_IS_DARJEELING)
// Darjeeling does not have a Flash Controller
#else
#error "all_escalation_resets_test does not support this top"
#endif

  IBEX_SPIN_FOR(alert_irq_seen, kTestTimeout);
  LOG_INFO("Alert IRQ seen");

  if (kExpectedAlertNumber ==
      dt_sram_ctrl_alert_to_alert_id(kSramCtrlRetAonDt,
                                     kDtSramCtrlAlertFatalError)) {
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
  // Retrieve the SRAM Ret Start address from the DT
  kSramRetStart =
      dt_sram_ctrl_reg_block(kDtSramCtrlRetAon, kDtSramCtrlRegBlockRam);

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  init_peripherals();

  ret_sram_testutils_init();

  // Enable all the interrupts used in this test.
  rv_plic_testutils_irq_range_enable(
      &plic, kPlicTarget,
      dt_aon_timer_irq_to_plic_id(kAonTimerDt, kDtAonTimerIrqWkupTimerExpired),
      dt_aon_timer_irq_to_plic_id(kAonTimerDt, kDtAonTimerIrqWdogTimerBark));
  rv_plic_testutils_irq_range_enable(
      &plic, kPlicTarget,
      dt_alert_handler_irq_to_plic_id(kAlertHandlerDt,
                                      kDtAlertHandlerIrqClassa),
      dt_alert_handler_irq_to_plic_id(kAlertHandlerDt,
                                      kDtAlertHandlerIrqClassd));

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
    CHECK_STATUS_OK(ret_sram_testutils_counter_clear(kCounterReset));
    CHECK_STATUS_OK(ret_sram_testutils_counter_clear(kCounterInterrupt));
    CHECK_STATUS_OK(ret_sram_testutils_counter_clear(kCounterNmi));
    execute_test(&aon_timer);
  } else if (rst_info == kDifRstmgrResetInfoEscalation) {
    restore_fault_checker(&fault_checker);
    // Get the reset counter.
    CHECK_STATUS_OK(ret_sram_testutils_counter_get(kCounterReset,
                                                   (uint32_t *)&reset_count));
    LOG_INFO("Reset counter value: %u", reset_count);
    if (reset_count > kMaxResets) {
      CHECK(false, "Ip %d Got too many resets (%d)", fault_checker.ip_inst,
            reset_count);
    }

    // Increment reset counter to know where we are.
    CHECK_STATUS_OK(ret_sram_testutils_counter_increment(kCounterReset));

    restore_fault_checker(&fault_checker);

    LOG_INFO("Booting due to escalation reset");

    uint32_t interrupt_count = 0;
    CHECK_STATUS_OK(
        ret_sram_testutils_counter_get(kCounterInterrupt, &interrupt_count));
    uint32_t nmi_count = 0;
    CHECK_STATUS_OK(ret_sram_testutils_counter_get(kCounterNmi, &nmi_count));

    LOG_INFO("Interrupt count %d", interrupt_count);
    LOG_INFO("NMI count %d", nmi_count);

#if defined(OPENTITAN_IS_EARLGREY)
    // ISRs should not run if flash_ctrl or sram_ctrl_main get a fault because
    // flash or sram accesses are blocked in those cases. For lc_ctrl fatal
    // state, otp_fatal alerts tha will trigger LC to escalate, the lc_ctrl
    // blocks the CPU.
    if (kExpectedAlertNumber ==
            dt_flash_ctrl_alert_to_alert_id(kFlashCtrlDt,
                                            kDtFlashCtrlAlertFatalStdErr) ||
        kExpectedAlertNumber ==
            dt_sram_ctrl_alert_to_alert_id(kSramCtrlMainDt,
                                           kDtSramCtrlAlertFatalError) ||
        kExpectedAlertNumber == dt_lc_ctrl_alert_to_alert_id(
                                    kLcCtrlDt, kDtLcCtrlAlertFatalStateError) ||
        kExpectedAlertNumber ==
            dt_otp_ctrl_alert_to_alert_id(kOtpCtrlDt,
                                          kDtOtpCtrlAlertFatalMacroError) ||
        kExpectedAlertNumber ==
            dt_otp_ctrl_alert_to_alert_id(kOtpCtrlDt,
                                          kDtOtpCtrlAlertFatalCheckError)) {
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
#elif defined(OPENTITAN_IS_DARJEELING)
    // ISRs should not run if sram_ctrl_main gets a fault because sram accesses
    // are blocked in that cases. For lc_ctrl fatal state, otp_fatal alerts that
    // will trigger LC to escalate, the lc_ctrl blocks the CPU.
    if (kExpectedAlertNumber ==
            dt_sram_ctrl_alert_to_alert_id(kSramCtrlMainDt,
                                           kDtSramCtrlAlertFatalError) ||
        kExpectedAlertNumber == dt_lc_ctrl_alert_to_alert_id(
                                    kLcCtrlDt, kDtLcCtrlAlertFatalStateError) ||
        kExpectedAlertNumber ==
            dt_otp_ctrl_alert_to_alert_id(kOtpCtrlDt,
                                          kDtOtpCtrlAlertFatalMacroError) ||
        kExpectedAlertNumber ==
            dt_otp_ctrl_alert_to_alert_id(kOtpCtrlDt,
                                          kDtOtpCtrlAlertFatalCheckError)) {
      CHECK(interrupt_count == 0,
            "Expected regular ISR should not run for lc_ctrl fatal state, "
            "or sram_ctrl_main faults");
      CHECK(nmi_count == 0,
            "Expected nmi should not run for lc_ctrl fatal state, or "
            "sram_ctrl_main faults");
    } else {
      CHECK(interrupt_count == 1, "Expected exactly one regular interrupt");
      CHECK(nmi_count > 0, "Expected at least one nmi");
    }
#else
#error "all_escalation_resets_test does not support this top"
#endif

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
