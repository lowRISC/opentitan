// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p256.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/drbg.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of 32-bit words in a P-256 public key. */
  kP256PublicKeyWords = 512 / 32,
  /* Number of bytes in a P-256 private key. */
  kP256PrivateKeyBytes = 256 / 8,
  /* Number of 32-bit words in a P-256 message digest. */
  kP256DigestWords = 256 / 32,
  /* Number of 32-bit words in a P-256 ECDSA signature. */
  kP256SignatureWords = 512 / 32,
};

static const otcrypto_key_config_t kPrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP256,
    .key_length = kP256PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const char kMessage[] = "test message";

// Generate a random plain private key in the interval [1, n - 1].
status_t generate_random_key(uint32_t *key) {
  otcrypto_word32_buf_t key_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, key, kP256ScalarWords);
  otcrypto_const_byte_buf_t kEmptyBuffer =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);

  // n - 1
  const uint32_t n1[kP256ScalarWords] = {0xfc632551, 0xf3b9cac2, 0xa7179e84,
                                         0xbce6faad, 0xffffffff, 0xffffffff,
                                         0x00000000, 0xffffffff};

  TRY(otcrypto_drbg_instantiate(/*perso_string=*/&kEmptyBuffer));
  // Attempt to generate a valid key until successful.
  // Each attempt has around a 1 - 2^-32 probability to succeed
  // To avoid infinite loops, we set to try  a total of 128 times
  // for a total failure probability of 2^-4096
  uint32_t try_count = 128;
  uint32_t idx = 0;
  while (idx < try_count) {
    idx++;
    // Generate a random scalar.
    TRY(otcrypto_drbg_generate(&kEmptyBuffer, &key_buf));

    // If the generated key is not in the range [1, n-1], restart.
    if (hardened_range_check(key, n1, kP256ScalarWords).value !=
        kOtcryptoStatusValueOk) {
      continue;
    }
    return OTCRYPTO_OK;
  }
  return OTCRYPTO_RECOV_ERR;
}

// Generate a random 320-bit Boolean-shared shared seed.
status_t generate_random_seed(uint32_t *share0, uint32_t *share1) {
  otcrypto_word32_buf_t key_buf0 = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, share0, kP256MaskedScalarShareWords);
  otcrypto_word32_buf_t key_buf1 = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, share1, kP256MaskedScalarShareWords);

  otcrypto_const_byte_buf_t kEmptyBuffer =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);

  TRY(otcrypto_drbg_instantiate(/*perso_string=*/&kEmptyBuffer));
  TRY(otcrypto_drbg_generate(&kEmptyBuffer, &key_buf0));
  TRY(otcrypto_drbg_generate(&kEmptyBuffer, &key_buf1));
  TRY(hardened_xor_in_place(share0, share1, kP256MaskedScalarShareWords));
  return OTCRYPTO_OK;
}

// Verify that we can correctly arithmetically share a Boolean-shared key.
status_t arith_share_private_key_test(bool seed) {
  // Part 1: Generate a random private key/seed and arithmetically share it.

  uint32_t key_share0[kP256MaskedScalarShareWords] = {0};
  uint32_t key_share1[kP256MaskedScalarShareWords] = {0};

  // Either generate a 320-bit Boolean-shared seed that is converted to an
  // 320-bit arithmetically shared key or generate a 256-bit unshared key in
  // the interval [1, n-1] according to FIPS 186-5 and expand it to 320-bit
  // Boolean shares before the conversion to arithmetic shares.
  if (seed) {
    TRY(generate_random_seed(key_share0, key_share1));
  } else {
    TRY(generate_random_key(key_share0));
    // Share the key
    TRY(hardened_memshred(key_share1, kP256MaskedScalarShareWords));
    TRY(hardened_xor_in_place(key_share0, key_share1,
                              kP256MaskedScalarShareWords));
  }

  otcrypto_const_word32_buf_t private_key_share0 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, key_share0, kP256MaskedScalarShareWords);
  otcrypto_const_word32_buf_t private_key_share1 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, key_share1, kP256MaskedScalarShareWords);

  uint32_t private_key_blob[kP256MaskedScalarTotalShareWords] = {0};
  otcrypto_blinded_key_t arith_shared_private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(private_key_blob),
      .keyblob = private_key_blob,
  };

  LOG_INFO("Sharing the private key...");
  CHECK_STATUS_OK(otcrypto_ecc_p256_arith_share_private_key(
      &private_key_share0, &private_key_share1, &arith_shared_private_key));

  // Part 2: Derive the public key with a base point multiplication.

  uint32_t public_key_blob[kP256PublicKeyWords] = {0};
  otcrypto_unblinded_key_t ppp = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(public_key_blob),
      .key = public_key_blob,
  };

  LOG_INFO("Calculating the public key...");
  CHECK_STATUS_OK(
      otcrypto_ecc_p256_base_point_mult(&arith_shared_private_key, &ppp));

  // Part 3: Sign a message with the arithmetically shared key.

  otcrypto_const_byte_buf_t msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, (unsigned char *)kMessage,
                        sizeof(kMessage) - 1);
  uint32_t msg_digest_data[kP256DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_256(&msg, &msg_digest));

  uint32_t sig[kP256SignatureWords] = {0};
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));

  LOG_INFO("Signing with shared private key...");
  TRY(otcrypto_ecdsa_p256_sign(&arith_shared_private_key, msg_digest,
                               &sig_buf));

  // Part 4: Verify the signature.

  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, ARRAYSIZE(sig));
  hardened_bool_t verification_result;

  LOG_INFO("Verifying signature with calculated public key...");
  TRY(otcrypto_ecdsa_p256_verify(&ppp, msg_digest, &const_sig_buf,
                                 &verification_result));
  TRY_CHECK(verification_result == kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  status_t err0 = arith_share_private_key_test(false);
  status_t err1 = arith_share_private_key_test(true);
  if (!status_ok(err0) || !status_ok(err1)) {
    // If there was an error, print the OTBN error bits and instruction count.
    LOG_INFO("OTBN error bits: 0x%08x", otbn_err_bits_get());
    LOG_INFO("OTBN instruction count: 0x%08x", otbn_instruction_count_get());
    // Print the error.
    CHECK_STATUS_OK(err0);
    CHECK_STATUS_OK(err1);
    return false;
  }

  return true;
}
