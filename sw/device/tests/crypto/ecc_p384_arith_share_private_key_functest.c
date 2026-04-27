// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p384.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/drbg.h"
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
status_t generate_random_key(uint32_t *key) {
  otcrypto_word32_buf_t key_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, key, kP384ScalarWords);
  otcrypto_const_byte_buf_t kEmptyBuffer =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);

  // n - 1
  const uint32_t n1[kP384ScalarWords] = {
      0xccc52972, 0xecec196a, 0x48b0a77a, 0x581a0db2, 0xf4372ddf, 0xc7634d81,
      0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff};

  TRY(otcrypto_drbg_instantiate(/*perso_string=*/&kEmptyBuffer));
  // Attempt to generate a valid key until successful.
  // Each attempt has an overwhelming probability to succeed
  // Still, to avoid infinite loops, we set to try a total of 128 times
  uint32_t try_count = 128;
  uint32_t idx = 0;
  while (idx < try_count) {
    idx++;
    // Generate a random scalar.
    TRY(otcrypto_drbg_generate(&kEmptyBuffer, &key_buf));

    // If the generated key is not in the range [1, n-1], restart.
    if (hardened_range_check(key, n1, kP384ScalarWords).value !=
        kOtcryptoStatusValueOk) {
      continue;
    }
    return OTCRYPTO_OK;
  }
  return OTCRYPTO_RECOV_ERR;
}

// Generate a random 448-bit Boolean-shared shared seed.
status_t generate_random_seed(uint32_t *share0, uint32_t *share1) {
  otcrypto_word32_buf_t key_buf0 = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, share0, kP384MaskedScalarShareWords);
  otcrypto_word32_buf_t key_buf1 = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, share1, kP384MaskedScalarShareWords);

  otcrypto_const_byte_buf_t kEmptyBuffer =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);

  TRY(otcrypto_drbg_instantiate(/*perso_string=*/&kEmptyBuffer));
  TRY(otcrypto_drbg_generate(&kEmptyBuffer, &key_buf0));
  TRY(otcrypto_drbg_generate(&kEmptyBuffer, &key_buf1));
  TRY(hardened_xor_in_place(share0, share1, kP384MaskedScalarShareWords));
  return OTCRYPTO_OK;
}

// Verify that we can correctly arithmetically share a Boolean-shared key.
status_t arith_share_private_key_test(bool seed) {
  // Part 1: Generate a random private key and arithmetically share it.

  uint32_t key_share0[kP384MaskedScalarShareWords] = {0};
  uint32_t key_share1[kP384MaskedScalarShareWords] = {0};

  // Either generate a 448-bit Boolean-shared seed that is converted to an
  // 448-bit arithmetically shared key or generate a 384-bit unshared key in
  // the interval [1, n-1] according to FIPS 186-5 and expand it to 448-bit
  // Boolean shares before the conversion to arithmetic shares.
  if (seed) {
    TRY(generate_random_seed(key_share0, key_share1));
  } else {
    TRY(generate_random_key(key_share0));
    // Share the key
    TRY(hardened_memshred(key_share1, kP384MaskedScalarShareWords));
    TRY(hardened_xor_in_place(key_share0, key_share1,
                              kP384MaskedScalarShareWords));
  }

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

static status_t run_arith_share_negative_tests(void) {
  LOG_INFO("Running arithmetic share negative tests.");

  // kP384MaskedScalarShareWords is 14
  uint32_t share_data[14] = {0};
  otcrypto_const_word32_buf_t share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share_data, 14);
  otcrypto_const_word32_buf_t share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share_data, 14);

  uint32_t keyblob[28] = {0};
  otcrypto_blinded_key_t priv_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  priv_key.checksum = integrity_blinded_checksum(&priv_key);

  // Null inputs
  CHECK(otcrypto_ecc_p384_arith_share_private_key(NULL, &share1, &priv_key)
            .value != OTCRYPTO_OK.value);
  CHECK(
      otcrypto_ecc_p384_arith_share_private_key(&share0, &share1, NULL).value !=
      OTCRYPTO_OK.value);

  // Bad length inputs
  otcrypto_const_word32_buf_t bad_len_share = {.data = share_data, .len = 13};
  CHECK(otcrypto_ecc_p384_arith_share_private_key(&bad_len_share, &share1,
                                                  &priv_key)
            .value != OTCRYPTO_OK.value);

  // Bad key mode
  otcrypto_key_config_t bad_mode_cfg = kPrivateKeyConfig;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeAesCtr;
  otcrypto_blinded_key_t bad_mode_key = {
      .config = bad_mode_cfg,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  bad_mode_key.checksum = integrity_blinded_checksum(&bad_mode_key);
  CHECK(
      otcrypto_ecc_p384_arith_share_private_key(&share0, &share1, &bad_mode_key)
          .value != OTCRYPTO_OK.value);

  // Bad hw backed
  otcrypto_key_config_t bad_hw_cfg = kPrivateKeyConfig;
  bad_hw_cfg.hw_backed = kHardenedBoolTrue;
  otcrypto_blinded_key_t bad_hw_key = {
      .config = bad_hw_cfg,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  bad_hw_key.checksum = integrity_blinded_checksum(&bad_hw_key);
  CHECK(otcrypto_ecc_p384_arith_share_private_key(&share0, &share1, &bad_hw_key)
            .value != OTCRYPTO_OK.value);

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

  status_t err = run_arith_share_negative_tests();
  if (!status_ok(err)) {
    CHECK_STATUS_OK(err);
    return false;
  }

  return true;
}
