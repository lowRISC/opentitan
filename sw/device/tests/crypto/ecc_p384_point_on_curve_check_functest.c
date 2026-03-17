// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p384.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
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
  TRY(otcrypto_p384_point_on_curve(&point_valid, &result));

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
  TRY(otcrypto_p384_point_on_curve(&point_invalid, &result));

  if (result != kHardenedBoolFalse) {
    LOG_ERROR("Invalid point passed point check.");
    return OTCRYPTO_RECOV_ERR;
  }

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  status_t err = point_valid_test();
  if (!status_ok(err)) {
    // If there was an error, print the OTBN error bits and instruction count.
    LOG_INFO("OTBN error bits: 0x%08x", otbn_err_bits_get());
    LOG_INFO("OTBN instruction count: 0x%08x", otbn_instruction_count_get());
    // Print the error.
    CHECK_STATUS_OK(err);
    return false;
  }

  return true;
}
