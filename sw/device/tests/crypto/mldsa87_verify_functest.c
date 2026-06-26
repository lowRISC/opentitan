// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/mldsa.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/mldsa87_verify_testvectors.h"

/**
 * Execute a ML-DSA-87 signature verification.
 */
static status_t run_mldsa87_verify(const mldsa87_verify_testvector_t *vector) {
  otcrypto_unblinded_key_t pk = {
      .key_length = kOtcryptoMldsa87PkBytes,
      .key = (unsigned int *)vector->pk,
  };
  pk.checksum = otcrypto_integrity_unblinded_checksum(&pk);

  otcrypto_const_word32_buf_t sig = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, vector->sig, kOtcryptoMldsa87SigWords);
  otcrypto_const_byte_buf_t msg = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, vector->msg, vector->msg_len);
  otcrypto_const_byte_buf_t ctx = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, vector->ctx, vector->ctx_len);

  hardened_bool_t verification_result;
  CHECK_STATUS_OK(otcrypto_mldsa87_verify(
      &pk, &msg, &ctx, &sig, vector->hash_mode, &verification_result));

  CHECK(verification_result == kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

/**
 * Pure hashing mode.
 */
static status_t mldsa87_verify_pure_test(void) {
  return run_mldsa87_verify(
      &mldsa87_verify_testvectors[kMldsa87VerifyNistAcvp63Pure]);
}

/**
 * Pre-hash mode.
 */
static status_t mldsa87_verify_pre_hash_test(void) {
  return run_mldsa87_verify(
      &mldsa87_verify_testvectors[kMldsa87VerifyNistAcvp79PreHashSha3_224]);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  CHECK_STATUS_OK(kmac_hwip_default_configure());

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  status_t result = OK_STATUS();
  EXECUTE_TEST(result, mldsa87_verify_pure_test);
  EXECUTE_TEST(result, mldsa87_verify_pre_hash_test);

  return status_ok(result);
}
