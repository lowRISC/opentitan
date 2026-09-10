// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/mldsa.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/mldsa87_sign_testvectors.h"

/**
 * Execute a ML-DSA-87 signature generation.
 */
static status_t run_mldsa87_sign(const mldsa87_sign_testvector_t *vector) {
  otcrypto_blinded_key_t sk = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMldsa87,
              .key_length = kOtcryptoMldsa87SkBytes,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kOtcryptoMldsa87SkBytes,
      .keyblob = (unsigned int *)vector->sk,
  };
  sk.checksum = otcrypto_integrity_blinded_checksum(&sk);

  otcrypto_const_byte_buf_t msg = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, vector->msg, vector->msg_len);
  otcrypto_const_byte_buf_t ctx = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, vector->ctx, vector->ctx_len);

  uint32_t sig_data[kOtcryptoMldsa87SigWords];
  otcrypto_word32_buf_t sig = OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig_data,
                                                kOtcryptoMldsa87SigWords);
  CHECK_STATUS_OK(otcrypto_mldsa87_sign(&sk, &msg, &ctx, vector->hash_mode,
                                        vector->sign_mode, &sig));

  CHECK_ARRAYS_EQ(vector->sig, sig_data, kOtcryptoMldsa87SigWords);

  return OTCRYPTO_OK;
}

/**
 * Pure hashing mode.
 */
static status_t mldsa87_sign_pure_test(void) {
  return run_mldsa87_sign(
      &mldsa87_sign_testvectors[kMldsa87SignNistAcvp61Pure]);
}

/**
 * Pre-hash mode.
 */
static status_t mldsa87_sign_pre_hash_test(void) {
  return run_mldsa87_sign(
      &mldsa87_sign_testvectors[kMldsa87SignNistAcvp76PreHashSha3_384]);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  CHECK_STATUS_OK(kmac_hwip_default_configure());

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  status_t result = OK_STATUS();
  EXECUTE_TEST(result, mldsa87_sign_pure_test);
  EXECUTE_TEST(result, mldsa87_sign_pre_hash_test);

  return status_ok(result);
}
