// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

status_t point_valid_invalid_check_test(void) {
  hardened_bool_t result;

  // Valid Ed25519 public key from RFC 8032 section 7.1, TEST 1.
  uint32_t point_valid_raw[8] = {
      0x01985ad7, 0xb70ab182, 0xd3fe4bd5, 0x3a0764c9,
      0xf372e10e, 0x2523a6da, 0x681a02af, 0x1a5107f7,
  };
  otcrypto_unblinded_key_t point_valid = {
      .key = point_valid_raw,
      .key_length = sizeof(point_valid_raw),
  };

  TRY(otcrypto_ed25519_point_on_curve(&point_valid, &result));
  TRY_CHECK(result == kHardenedBoolTrue);

  // Off-curve point (u / v is not a quadratic residue modulo p).
  uint32_t point_invalid_raw[8] = {
      0x01985ad6, 0xb70ab182, 0xd3fe4bd5, 0x3a0764c9,
      0xf372e10e, 0x2523a6da, 0x681a02af, 0x1a5107f7,
  };
  otcrypto_unblinded_key_t point_invalid = {
      .key = point_invalid_raw,
      .key_length = sizeof(point_invalid_raw),
  };

  TRY(otcrypto_ed25519_point_on_curve(&point_invalid, &result));
  TRY_CHECK(result == kHardenedBoolFalse);

  // Non-canonical point (y >= p = 2^255 - 19).
  uint32_t point_noncanonical_raw[8] = {
      0xffffffed, 0xffffffff, 0xffffffff, 0xffffffff,
      0xffffffff, 0xffffffff, 0xffffffff, 0x7fffffff,
  };
  otcrypto_unblinded_key_t point_noncanonical = {
      .key = point_noncanonical_raw,
      .key_length = sizeof(point_noncanonical_raw),
  };

  TRY(otcrypto_ed25519_point_on_curve(&point_noncanonical, &result));
  TRY_CHECK(result == kHardenedBoolFalse);

  // Negative tests: pass NULL arguments to verify error paths.
  hardened_bool_t null_res;
  CHECK(otcrypto_ed25519_point_on_curve(NULL, &null_res).value !=
        kOtcryptoStatusValueOk);
  CHECK(otcrypto_ed25519_point_on_curve(&point_valid, NULL).value !=
        kOtcryptoStatusValueOk);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t test_result = OK_STATUS();
  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));
  EXECUTE_TEST(test_result, point_valid_invalid_check_test);
  return status_ok(test_result);
}
