// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "aes_regs.h"
#include "alert_handler_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

OTTF_DEFINE_TEST_CONFIG();

static status_t test_set_and_check_config(void) {
  LOG_INFO("Testing high security config");
  TRY(otcrypto_set_security_config(kOtcryptoKeySecurityLevelHigh));
  TRY(otcrypto_security_config_check(kOtcryptoKeySecurityLevelHigh));

  LOG_INFO("Testing low security config");
  TRY(otcrypto_set_security_config(kOtcryptoKeySecurityLevelLow));
  TRY(otcrypto_security_config_check(kOtcryptoKeySecurityLevelLow));

  return OK_STATUS();
}

static status_t test_init_and_exit(void) {
  otcrypto_key_security_level_t sec_level = kOtcryptoKeySecurityLevelHigh;

  TRY(otcrypto_init(sec_level));
  TRY(otcrypto_security_config_check(sec_level));
  TRY(otcrypto_eval_exit(OTCRYPTO_OK));

  return OK_STATUS();
}

static status_t test_multiple_inits(void) {
  otcrypto_key_security_level_t sec_level = kOtcryptoKeySecurityLevelHigh;

  TRY(otcrypto_set_security_config(sec_level));

  for (size_t i = 0; i < 50; i++) {
    TRY(otcrypto_init(sec_level));
  }

  return OK_STATUS();
}

static status_t test_security_config_check_negative(void) {
  LOG_INFO("Testing negative security config check on boot state");
  otcrypto_key_security_level_t sec_level = kOtcryptoKeySecurityLevelHigh;

  otcrypto_status_t tamper_status = otcrypto_security_config_check(sec_level);
  CHECK(tamper_status.value != OTCRYPTO_OK.value);

  TRY(otcrypto_set_security_config(sec_level));

  TRY(otcrypto_security_config_check(sec_level));

  return OK_STATUS();
}

static status_t test_icache_disable_restore(void) {
  LOG_INFO("Testing icache disable and restore");
  hardened_bool_t icache_state;

  TRY(otcrypto_disable_icache(&icache_state));

  TRY(otcrypto_restore_icache(icache_state));

  return OK_STATUS();
}

static status_t test_alert_caught_by_eval_exit(void) {
  LOG_INFO("Testing otcrypto_eval_exit with forced AES alert");

  // Initialize crypto (this also clears alert accumulators)
  TRY(otcrypto_init(kOtcryptoKeySecurityLevelHigh));

  // OTTF has its own alert management system, we have to bypass it.
  // Disable interrupts globally.
  // This prevents the OTTF ISR from preempting us and clearing the accumulator.
  irq_global_ctrl(false);

  // Force a recoverable alert of the AES
  uint32_t alert_test_reg =
      bitfield_bit32_write(0, AES_ALERT_TEST_RECOV_CTRL_UPDATE_ERR_BIT, true);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR),
                      (ptrdiff_t)AES_ALERT_TEST_REG_OFFSET, alert_test_reg);

  // Verify eval_exit catches the alert.
  // Because interrupts are off, the accumulator is preserved for this check.
  otcrypto_status_t exit_status = otcrypto_eval_exit(OTCRYPTO_OK);
  CHECK(exit_status.value == OTCRYPTO_FATAL_ERR.value,
        "otcrypto_eval_exit failed to catch the AES alert. Expected 0x%08x, "
        "got 0x%08x",
        OTCRYPTO_FATAL_ERR.value, exit_status.value);

  // Use the cryptolib's helper call to clear the alerts.
  TRY(otcrypto_clear_alerts());

  // Verify that the eval_exit passes again.
  TRY(otcrypto_eval_exit(OTCRYPTO_OK));

  // - Cleanup
  // The PLIC still has a pending interrupt latched from the alert. If we turn
  // IRQs back on right now, the ISR will run, find no cause, and abort(). To
  // exit safely, we tell the OTTF to expect an alert, and trigger a fresh one.

  // Feed the OTTF ISR.
  TRY(ottf_alerts_expect_alert_start(kTopEarlgreyAlertIdAesRecovCtrlUpdateErr));

  // Provide a new alert.
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR),
                      (ptrdiff_t)AES_ALERT_TEST_REG_OFFSET, alert_test_reg);

  // The CPU jumps to the ISR immediately. The ISR sees the second alert, marks
  // it as caught, clears the PLIC state, and returns.
  irq_global_ctrl(true);

  // Finish the OTTF's expectation.
  TRY(ottf_alerts_expect_alert_finish(
      kTopEarlgreyAlertIdAesRecovCtrlUpdateErr));

  return OK_STATUS();
}

static status_t test_lock(void) {
  LOG_INFO("Testing locking the regwen provides a bad status");
  // Locking the accumulators causes the alert to no longer be clearable.
  // The test is similar to test_alert_caught_by_eval_exit

  TRY(otcrypto_init(kOtcryptoKeySecurityLevelHigh));
  irq_global_ctrl(false);

  // Lock the accumulators
  abs_mmio_write32_shadowed(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                ALERT_HANDLER_CLASSA_CLR_REGWEN_REG_OFFSET,
                            0);
  abs_mmio_write32_shadowed(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                ALERT_HANDLER_CLASSB_CLR_REGWEN_REG_OFFSET,
                            0);
  abs_mmio_write32_shadowed(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                ALERT_HANDLER_CLASSC_CLR_REGWEN_REG_OFFSET,
                            0);
  abs_mmio_write32_shadowed(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                ALERT_HANDLER_CLASSD_CLR_REGWEN_REG_OFFSET,
                            0);

  // Recoverable alert
  uint32_t alert_test_reg =
      bitfield_bit32_write(0, AES_ALERT_TEST_RECOV_CTRL_UPDATE_ERR_BIT, true);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR),
                      (ptrdiff_t)AES_ALERT_TEST_REG_OFFSET, alert_test_reg);

  // eval_exit catches the alert.
  otcrypto_status_t exit_status = otcrypto_eval_exit(OTCRYPTO_OK);
  CHECK(exit_status.value == OTCRYPTO_FATAL_ERR.value,
        "otcrypto_eval_exit failed to catch the AES alert. Expected 0x%08x, "
        "got 0x%08x",
        OTCRYPTO_FATAL_ERR.value, exit_status.value);

  // Use the cryptolib's helper call to clear the alerts.
  // However, the function will return OTCRYPTO_FATAL_ERR as these accumulators
  // are locked.
  exit_status = otcrypto_clear_alerts();
  CHECK(exit_status.value == OTCRYPTO_FATAL_ERR.value,
        "otcrypto_clear_alerts failed to lock. Expected 0x%08x, "
        "got 0x%08x",
        OTCRYPTO_FATAL_ERR.value, exit_status.value);

  // Since the accumulators are locked, the cryptolib remains locked.
  exit_status = otcrypto_eval_exit(OTCRYPTO_OK);
  CHECK(exit_status.value == OTCRYPTO_FATAL_ERR.value,
        "otcrypto_eval_exit failed to lock. Expected 0x%08x, "
        "got 0x%08x",
        OTCRYPTO_FATAL_ERR.value, exit_status.value);

  // Cleanup
  TRY(ottf_alerts_expect_alert_start(kTopEarlgreyAlertIdAesRecovCtrlUpdateErr));
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR),
                      (ptrdiff_t)AES_ALERT_TEST_REG_OFFSET, alert_test_reg);
  irq_global_ctrl(true);
  TRY(ottf_alerts_expect_alert_finish(
      kTopEarlgreyAlertIdAesRecovCtrlUpdateErr));

  return OK_STATUS();
}

bool test_main(void) {
  status_t result = OK_STATUS();

  // We run the config check first as the chip comes out of boot, so the config
  // is not set yet.
  EXECUTE_TEST(result, test_security_config_check_negative);
  EXECUTE_TEST(result, test_set_and_check_config);
  EXECUTE_TEST(result, test_init_and_exit);
  EXECUTE_TEST(result, test_multiple_inits);
  EXECUTE_TEST(result, test_icache_disable_restore);
  EXECUTE_TEST(result, test_alert_caught_by_eval_exit);
  // Locks the accumulators making the cryptolib alerts no longer clearable
  // Hence this test should be the last
  EXECUTE_TEST(result, test_lock);

  return status_ok(result);
}
