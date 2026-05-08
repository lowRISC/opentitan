// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

otcrypto_status_t reverse_status(otcrypto_status_t status) {
  otcrypto_status_t result;
  if (status_ok(status) == false) {
    result = OTCRYPTO_OK;
  } else {
    // We take an arbitrary bad status here.
    result = OTCRYPTO_BAD_ARGS;
  }
  return result;
}

otcrypto_status_t return_status(otcrypto_status_t status) { return status; }
otcrypto_status_t good_test(void) {
  HARDENED_TRY(return_status(OTCRYPTO_OK));
  return OTCRYPTO_OK;
}
otcrypto_status_t bad_test(otcrypto_status_t status) {
  HARDENED_TRY(return_status(status));
  return OTCRYPTO_OK;
}

// Reverse the status so we execute tests returning an ok status.
otcrypto_status_t bad_args_test(void) {
  otcrypto_status_t result = bad_test(OTCRYPTO_BAD_ARGS);
  return reverse_status(result);
}
otcrypto_status_t recov_err_test(void) {
  otcrypto_status_t result = bad_test(OTCRYPTO_RECOV_ERR);
  return reverse_status(result);
}
otcrypto_status_t fatal_err_test(void) {
  otcrypto_status_t result = bad_test(OTCRYPTO_FATAL_ERR);
  return reverse_status(result);
}
otcrypto_status_t async_incomplete_test(void) {
  otcrypto_status_t result = bad_test(OTCRYPTO_ASYNC_INCOMPLETE);
  return reverse_status(result);
}
otcrypto_status_t not_implemented_test(void) {
  otcrypto_status_t result = bad_test(OTCRYPTO_NOT_IMPLEMENTED);
  return reverse_status(result);
}

bool test_main(void) {
  status_t result = OTCRYPTO_OK;
  // Test hardened_try when the check is valid.
  EXECUTE_TEST(result, good_test);

  // Test hardened_try when the check is invalid.
  EXECUTE_TEST(result, bad_args_test);
  EXECUTE_TEST(result, recov_err_test);
  EXECUTE_TEST(result, fatal_err_test);
  EXECUTE_TEST(result, async_incomplete_test);
  EXECUTE_TEST(result, not_implemented_test);

  return status_ok(result);
}
