// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

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

bool test_main(void) {
  status_t result = OK_STATUS();

  EXECUTE_TEST(result, test_set_and_check_config);
  EXECUTE_TEST(result, test_init_and_exit);
  EXECUTE_TEST(result, test_multiple_inits);

  return status_ok(result);
}
