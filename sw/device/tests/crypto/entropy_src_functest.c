// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#define MODULE_ID MAKE_MODULE_ID('e', 's', 'f')

OTTF_DEFINE_TEST_CONFIG();

static status_t test_entropy_lifecycle(void) {
  LOG_INFO("Testing entropy initialization");
  TRY(otcrypto_entropy_init());

  LOG_INFO("Testing entropy check");
  TRY(otcrypto_entropy_check());

  LOG_INFO("Testing entropy health test config check");
  TRY(otcrypto_entropy_health_test_config_check());

  return OK_STATUS();
}

static status_t test_multiple_entropy_checks(void) {
  LOG_INFO("Testing multiple consecutive entropy checks");

  for (size_t i = 0; i < 10; i++) {
    TRY(otcrypto_entropy_check());
  }

  return OK_STATUS();
}

bool test_main(void) {
  status_t result = OK_STATUS();

  EXECUTE_TEST(result, test_entropy_lifecycle);
  EXECUTE_TEST(result, test_multiple_entropy_checks);

  return status_ok(result);
}
