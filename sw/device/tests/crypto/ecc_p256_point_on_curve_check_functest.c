// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p256.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of 32-bit words in a P-256 point. */
  kP256PointWords = 16,
};

status_t point_valid_test(void) {
  // Create a valid point using the p256_point_t struct.
  p256_point_t point_valid_raw;
  point_valid_raw.x[0] = 0xbfa8c334;
  point_valid_raw.x[1] = 0x9773b7b3;
  point_valid_raw.x[2] = 0xf36b0689;
  point_valid_raw.x[3] = 0x6ec0c0b2;
  point_valid_raw.x[4] = 0xdb6c8bf3;
  point_valid_raw.x[5] = 0x1628ce58;
  point_valid_raw.x[6] = 0xfacdc546;
  point_valid_raw.x[7] = 0xb5511a6a;

  point_valid_raw.y[0] = 0x9e008c2e;
  point_valid_raw.y[1] = 0xa8707058;
  point_valid_raw.y[2] = 0xab9c6924;
  point_valid_raw.y[3] = 0x7f7a11d0;
  point_valid_raw.y[4] = 0xb53a17fa;
  point_valid_raw.y[5] = 0x43dd09ea;
  point_valid_raw.y[6] = 0x1f31c143;
  point_valid_raw.y[7] = 0x42a1c697;

  uint32_t pt_vld_buf[kP256PointWords];
  memcpy(pt_vld_buf, &point_valid_raw, sizeof(point_valid_raw));
  // Convert the p256_point_t struct into a otcrypto_unblinded_key_t struct.
  otcrypto_unblinded_key_t point_valid = {
      .key_length = sizeof(pt_vld_buf),
      .key = pt_vld_buf,
  };

  // Verify the valid point.
  hardened_bool_t result;
  TRY(otcrypto_ecc_p256_point_on_curve(&point_valid, &result));

  if (result != kHardenedBoolTrue) {
    LOG_ERROR("Valid point failed point check.");
    return OTCRYPTO_RECOV_ERR;
  }

  // Create an invalid point using the otcrypto_unblinded_key_t struct.
  uint32_t pt_invld_buf[kP256PointWords] = {0};
  otcrypto_unblinded_key_t point_invalid = {
      .key_length = sizeof(pt_invld_buf),
      .key = pt_invld_buf,
  };

  // Verify the invalid point.
  TRY(otcrypto_ecc_p256_point_on_curve(&point_invalid, &result));

  if (result != kHardenedBoolFalse) {
    LOG_ERROR("Invalid point passed point check.");
    return OTCRYPTO_RECOV_ERR;
  }

  // Null inputs
  hardened_bool_t null_res;
  CHECK(otcrypto_ecc_p256_point_on_curve(NULL, &null_res).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_point_on_curve(&point_valid, NULL).value !=
        OTCRYPTO_OK.value);

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

  return true;
}
