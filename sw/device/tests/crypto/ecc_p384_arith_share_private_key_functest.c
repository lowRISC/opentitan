// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p384.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of 32-bit words in a P-384 public key. */
  kP384PublicKeyWords = 2 * kP384CoordWords,
  /* Number of bytes in a P-384 private key. */
  kP384PrivateKeyBytes = 384 / 8,
  /* Number of 32-bit words in a P-384 message digest. */
  kP384DigestWords = 384 / 32,
  /* Number of 32-bit words in a P-384 ECDSA signature. */
  kP384SignatureWords = 768 / 32,
};

static const otcrypto_key_config_t kPrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP384,
    .key_length = kP384PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const char kMessage[] = "test message";

// Generate a random plain private key in the interval [1, n - 1].
void generate_random_key(uint32_t *key) {
  hardened_memshred(key, kP384ScalarWords);

  const uint32_t zero[kP384ScalarWords] = {0};

  // n - 1
  const uint32_t n1[kP384ScalarWords] = {
      0xccc52972, 0xecec196a, 0x48b0a77a, 0x581a0db2, 0xf4372ddf, 0xc7634d81,
      0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff};

  while (1) {
    // Generate a random scalar.
    size_t i = 0;
    for (; launder32(i) < kP384ScalarWords; i++) {
      key[i] = hardened_memshred_random_word();
    }
    HARDENED_CHECK_EQ(i, kP384ScalarWords);

    // If the generated key is 0, restart.
    if (hardened_memeq(key, zero, kP384ScalarWords) == kHardenedBoolTrue) {
      continue;
    }
    HARDENED_CHECK_EQ(hardened_memeq(key, zero, kP384ScalarWords),
                      kHardenedBoolFalse);

    // If the generated key is > n - 1, restart.
    uint32_t borrow = 0;
    i = 0;
    for (; launder32(i) < kP384ScalarWords; i++) {
      borrow = (n1[i] < borrow) + ((n1[i] - borrow) < key[i]);
    }
    HARDENED_CHECK_EQ(i, kP384ScalarWords);

    if (borrow) {
      continue;
    }
    HARDENED_CHECK_EQ(borrow, 0);

    return;
  }
}

// Verify that we can correctly arithmetically share a plain private key.
status_t arith_share_private_key_test(void) {
  // Part 1: Generate a random private key and arithmetically share it.

  uint32_t key_share0[kP384MaskedScalarShareWords] = {0};
  uint32_t key_share1[kP384MaskedScalarShareWords] = {0};
  generate_random_key(key_share0);

  otcrypto_const_word32_buf_t private_key_share0 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, key_share0, kP384MaskedScalarShareWords);
  otcrypto_const_word32_buf_t private_key_share1 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, key_share1, kP384MaskedScalarShareWords);

  uint32_t private_key_blob[kP384MaskedScalarTotalShareWords] = {0};
  otcrypto_blinded_key_t arith_shared_private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(private_key_blob),
      .keyblob = private_key_blob,
  };

  LOG_INFO("Sharing the private key...");
  CHECK_STATUS_OK(otcrypto_ecc_p384_arith_share_private_key(
      &private_key_share0, &private_key_share1, &arith_shared_private_key));

  // Part 2: Derive the public key with a base point multiplication.

  uint32_t public_key_blob[kP384PublicKeyWords] = {0};
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(public_key_blob),
      .key = public_key_blob,
  };

  LOG_INFO("Calculating the public key...");
  CHECK_STATUS_OK(otcrypto_ecc_p384_base_point_mult(&arith_shared_private_key,
                                                    &public_key));

  // Part 3: Sign a message with the arithmetically shared key.

  otcrypto_const_byte_buf_t msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, (unsigned char *)kMessage,
                        sizeof(kMessage) - 1);
  uint32_t msg_digest_data[kP384DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_384(&msg, &msg_digest));

  uint32_t sig[kP384SignatureWords] = {0};
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));

  LOG_INFO("Signing with shared private key...");
  TRY(otcrypto_ecdsa_p384_sign(&arith_shared_private_key, msg_digest,
                               &sig_buf));

  // Part 4: Verify the signature.

  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, ARRAYSIZE(sig));
  hardened_bool_t verification_result;

  LOG_INFO("Verifying signature with calculated public key...");
  TRY(otcrypto_ecdsa_p384_verify(&public_key, msg_digest, &const_sig_buf,
                                 &verification_result));
  TRY_CHECK(verification_result == kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  status_t err = arith_share_private_key_test();
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
