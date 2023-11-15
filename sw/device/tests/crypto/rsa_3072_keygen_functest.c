// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module for status messages.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

enum {
  /* Number of words for a SHA-512 digest. */
  kSha512DigestWords = 512 / 32,
  /* Number of bytes for RSA-3072 modulus and private exponent. */
  kRsa3072NumBytes = 3072 / 8,
  /* Number of words for RSA-3072 modulus and private exponent. */
  kRsa3072NumWords = kRsa3072NumBytes / sizeof(uint32_t),
};

// Message data for testing.
static const unsigned char kTestMessage[] = "Test message.";
static const size_t kTestMessageLen = sizeof(kTestMessage) - 1;

// Configuration for the private exponent.
static const crypto_key_config_t kRsaPrivateKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeRsaSignPkcs,
    .key_length = kRsa3072NumBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kSecurityLevelLow,
};

status_t keygen_then_sign_test(void) {
  // Allocate buffers for the public key.
  uint32_t pub_n[kRsa3072NumWords] = {0};
  uint32_t pub_e = 0;
  rsa_public_key_t public_key = {
      .n =
          (crypto_unblinded_key_t){
              .key_mode = kRsaPrivateKeyConfig.key_mode,
              .key_length = kRsa3072NumBytes,
              .key = pub_n,
              .checksum = 0,
          },
      .e =
          (crypto_unblinded_key_t){
              .key_mode = kRsaPrivateKeyConfig.key_mode,
              .key_length = sizeof(uint32_t),
              .key = &pub_e,
              .checksum = 0,
          },
  };

  // Allocate buffers for the private key.
  uint32_t priv_n[kRsa3072NumWords] = {0};
  uint32_t priv_d[kRsa3072NumWords] = {0};
  rsa_private_key_t private_key = {
      .n =
          (crypto_unblinded_key_t){
              .key_mode = kRsaPrivateKeyConfig.key_mode,
              .key_length = kRsa3072NumBytes,
              .key = priv_n,
              .checksum = 0,
          },
      .d =
          (crypto_blinded_key_t){
              .config = kRsaPrivateKeyConfig,
              .keyblob_length = kRsa3072NumBytes,
              .keyblob = priv_d,
              .checksum = 0,
          },
  };

  // Generate the key pair.
  LOG_INFO("Starting keypair generation...");
  TRY(otcrypto_rsa_keygen(kRsaKeySize3072, &public_key, &private_key));
  LOG_INFO("Keypair generation complete.");
  LOG_INFO("OTBN instruction count: %u", otbn_instruction_count_get());

  // Check that the key uses the F4 exponent.
  TRY_CHECK(public_key.e.key_length == sizeof(uint32_t));
  TRY_CHECK(public_key.e.key[0] == 65537);

  // Check that d is at least 2^(len(n) / 2) (this is a FIPS requirement) by
  // ensuring that the most significant half is nonzero.
  bool d_large_enough = false;
  for (size_t i = kRsa3072NumWords / 2; i < kRsa3072NumWords; i++) {
    if (private_key.d.keyblob[i] != 0) {
      d_large_enough = true;
    }
  }
  TRY_CHECK(d_large_enough);

  // Hash the message.
  crypto_const_byte_buf_t msg_buf = {
      .len = kTestMessageLen,
      .data = kTestMessage,
  };
  uint32_t msg_digest_data[kSha512DigestWords];
  hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
      .mode = kHashModeSha512,
  };
  TRY(otcrypto_hash(msg_buf, &msg_digest));

  uint32_t sig[kRsa3072NumWords];
  crypto_word32_buf_t sig_buf = {
      .data = sig,
      .len = kRsa3072NumWords,
  };
  crypto_const_word32_buf_t const_sig_buf = {
      .data = sig,
      .len = kRsa3072NumWords,
  };

  // Generate a signature.
  LOG_INFO("Starting signature generation...");
  TRY(otcrypto_rsa_sign(&private_key, &msg_digest, kRsaPaddingPkcs, &sig_buf));
  LOG_INFO("Signature generation complete.");
  LOG_INFO("OTBN instruction count: %u", otbn_instruction_count_get());

  // Try to verify the signature. If something is wrong with the key (nonprime
  // p and q, incorrect d), then this is likely to fail.
  LOG_INFO("Starting signature verification...");
  hardened_bool_t verification_result;
  TRY(otcrypto_rsa_verify(&public_key, &msg_digest, kRsaPaddingPkcs,
                          const_sig_buf, &verification_result));
  LOG_INFO("Signature verification complete.");
  LOG_INFO("OTBN instruction count: %u", otbn_instruction_count_get());

  // Expect the signature to pass verification.
  TRY_CHECK(verification_result == kHardenedBoolTrue);
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  status_t test_result = OK_STATUS();
  EXECUTE_TEST(test_result, keygen_then_sign_test);
  return status_ok(test_result);
}
