// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p384.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of 32-bit words in a P-384 point. */
  kP384PointWords = 24,
};

status_t point_valid_test(void) {
  // Create a valid point using the p384_point_t struct.
  p384_point_t point_valid_raw;
  point_valid_raw.x[0] = 0x4877f3d1;
  point_valid_raw.x[1] = 0x7b829460;
  point_valid_raw.x[2] = 0xb1cac609;
  point_valid_raw.x[3] = 0x5869de54;
  point_valid_raw.x[4] = 0xee0e2beb;
  point_valid_raw.x[5] = 0x6c30f2d8;
  point_valid_raw.x[6] = 0x47e80661;
  point_valid_raw.x[7] = 0x394d8b70;
  point_valid_raw.x[8] = 0xcf60d89e;
  point_valid_raw.x[9] = 0x1a9ea916;
  point_valid_raw.x[10] = 0xb439d701;
  point_valid_raw.x[11] = 0xca230836;

  point_valid_raw.y[0] = 0xc181f90f;
  point_valid_raw.y[1] = 0xc31ef079;
  point_valid_raw.y[2] = 0xbf3aff6e;
  point_valid_raw.y[3] = 0xc7e55880;
  point_valid_raw.y[4] = 0xec18818c;
  point_valid_raw.y[5] = 0xcea028a9;
  point_valid_raw.y[6] = 0x928c3e92;
  point_valid_raw.y[7] = 0x82b63bf3;
  point_valid_raw.y[8] = 0xd65e905d;
  point_valid_raw.y[9] = 0x68eef2d1;
  point_valid_raw.y[10] = 0x03afe2c2;
  point_valid_raw.y[11] = 0xaaafcad2;

  uint32_t pt_vld_buf[kP384PointWords];
  memcpy(pt_vld_buf, &point_valid_raw, sizeof(point_valid_raw));
  // Convert the p384_point_t struct into a otcrypto_unblinded_key_t struct.
  otcrypto_unblinded_key_t point_valid = {
      .key_length = sizeof(pt_vld_buf),
      .key = pt_vld_buf,
  };

  // Verify the valid point.
  hardened_bool_t result;
  TRY(otcrypto_ecc_p384_point_on_curve(&point_valid, &result));

  if (result != kHardenedBoolTrue) {
    LOG_ERROR("Valid point failed point check.");
    return OTCRYPTO_RECOV_ERR;
  }

  // Create an invalid point using the otcrypto_unblinded_key_t struct.
  uint32_t pt_invld_buf[kP384PointWords] = {0};
  otcrypto_unblinded_key_t point_invalid = {
      .key_length = sizeof(pt_invld_buf),
      .key = pt_invld_buf,
  };

  // Verify the invalid point.
  TRY(otcrypto_ecc_p384_point_on_curve(&point_invalid, &result));

  if (result != kHardenedBoolFalse) {
    LOG_ERROR("Invalid point passed point check.");
    return OTCRYPTO_RECOV_ERR;
  }

  // Null inputs
  hardened_bool_t null_res;
  CHECK(otcrypto_ecc_p384_point_on_curve(NULL, &null_res).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_point_on_curve(&point_valid, NULL).value !=
        OTCRYPTO_OK.value);

  return OTCRYPTO_OK;
}

status_t point_partial_collision_test(void) {
  // This constructs a point where (Y^2 % p) and (X^3 - 3X + b % p)
  // share the same lower 256 bits, but differ in the upper 128 bits.
  // x
  p384_point_t point_invalid_raw = {
      .x = {0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
            0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
            0x00000000, 0x00000000},
      .y = {0x8d32a89f, 0xf4b1cd74, 0x274c130d, 0xcf3a3e8a, 0x0116d5e6,
            0x64d700b3, 0x51d7182c, 0x5465e170, 0x080a67b2, 0x23b8ad4d,
            0x983109dc, 0x0de970b2}};

  uint32_t pt_invld_buf[kP384PointWords];
  memcpy(pt_invld_buf, &point_invalid_raw, sizeof(point_invalid_raw));

  otcrypto_unblinded_key_t point_invalid = {
      .key_length = sizeof(pt_invld_buf),
      .key = pt_invld_buf,
  };

  hardened_bool_t result;
  TRY(otcrypto_ecc_p384_point_on_curve(&point_invalid, &result));

  // The OTBN routine will pass the `bn.cmp w4, w6` check,
  // but fail the subsequent `bn.cmp w5, w7` check, trigger an ecall,
  // and safely return HARDENED_BOOL_FALSE to the host.
  if (result != kHardenedBoolFalse) {
    LOG_ERROR("Partial collision point bypassed point check.");
    return OTCRYPTO_RECOV_ERR;
  }

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  status_t err = point_valid_test();
  if (!status_ok(err)) {
    // If there was an error, print the OTBN error bits and instruction count.
    LOG_INFO("OTBN error bits: 0x%08x", otbn_err_bits_get());
    LOG_INFO("OTBN instruction count: 0x%08x", otbn_instruction_count_get());
    // Print the error.
    CHECK_STATUS_OK(err);
    return false;
  }

  err = point_partial_collision_test();
  if (!status_ok(err)) {
    LOG_INFO("OTBN error bits: 0x%08x", otbn_err_bits_get());
    LOG_INFO("OTBN instruction count: 0x%08x", otbn_instruction_count_get());
    CHECK_STATUS_OK(err);
    return false;
  }

  return true;
}
