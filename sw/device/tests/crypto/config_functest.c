// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

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

bool test_main(void) {
  status_t result = OK_STATUS();

  // We run the config check first as the chip comes out of boot, so the config
  // is not set yet.
  EXECUTE_TEST(result, test_security_config_check_negative);
  EXECUTE_TEST(result, test_set_and_check_config);
  EXECUTE_TEST(result, test_init_and_exit);
  EXECUTE_TEST(result, test_multiple_inits);
  EXECUTE_TEST(result, test_icache_disable_restore);

  return status_ok(result);
}
