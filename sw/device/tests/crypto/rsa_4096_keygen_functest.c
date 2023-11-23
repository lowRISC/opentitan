// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_datatypes.h"
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
};

// Message data for testing.
static const unsigned char kTestMessage[] = "Test message.";
static const size_t kTestMessageLen = sizeof(kTestMessage) - 1;

// RSA key mode for testing.
static const key_mode_t kTestKeyMode = kKeyModeRsaSignPkcs;

status_t keygen_then_sign_test(void) {
  // Get the key lengths from the size.
  size_t public_key_length;
  TRY(otcrypto_rsa_public_key_length(kRsaSize4096, &public_key_length));
  size_t private_key_length;
  size_t private_keyblob_length;
  TRY(otcrypto_rsa_private_key_length(kRsaSize4096, &private_key_length,
                                      &private_keyblob_length));

  // Allocate buffer for the public key.
  uint32_t public_key_data[ceil_div(public_key_length, sizeof(uint32_t))];
  memset(public_key_data, 0, sizeof(public_key_data));
  crypto_unblinded_key_t public_key = {
      .key_mode = kTestKeyMode,
      .key_length = public_key_length,
      .key = public_key_data,
  };

  // Allocate buffers for the private key.
  uint32_t keyblob[ceil_div(private_keyblob_length, sizeof(uint32_t))];
  memset(keyblob, 0, sizeof(keyblob));
  crypto_blinded_key_t private_key = {
      .config =
          {
              .version = kCryptoLibVersion1,
              .key_mode = kTestKeyMode,
              .key_length = private_key_length,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kSecurityLevelLow,
          },
      .keyblob_length = private_keyblob_length,
      .keyblob = keyblob,
  };

  // Generate the key pair.
  LOG_INFO("Starting keypair generation...");
  TRY(otcrypto_rsa_keygen(kRsaSize4096, &public_key, &private_key));
  LOG_INFO("Keypair generation complete.");
  LOG_INFO("OTBN instruction count: %u", otbn_instruction_count_get());

  // Interpret public key using internal RSA datatype.
  TRY_CHECK(public_key_length == sizeof(rsa_4096_public_key_t));
  rsa_4096_public_key_t *pk = (rsa_4096_public_key_t *)public_key.key;

  // Interpret private key using internal RSA datatype.
  TRY_CHECK(private_keyblob_length == sizeof(rsa_4096_private_key_t));
  rsa_4096_private_key_t *sk = (rsa_4096_private_key_t *)private_key.keyblob;

  // Check that the key uses the F4 exponent.
  TRY_CHECK(pk->e == 65537);

  // Check that the moduli match.
  TRY_CHECK(ARRAYSIZE(pk->n.data) == ARRAYSIZE(sk->n.data));
  TRY_CHECK_ARRAYS_EQ(pk->n.data, sk->n.data, ARRAYSIZE(pk->n.data));

  // Check that d is at least 2^(len(n) / 2) (this is a FIPS requirement) by
  // ensuring that the most significant half is nonzero.
  bool d_large_enough = false;
  for (size_t i = kRsa4096NumWords / 2; i < kRsa4096NumWords; i++) {
    if (sk->d.data[i] != 0) {
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

  uint32_t sig[kRsa4096NumWords];
  crypto_word32_buf_t sig_buf = {
      .data = sig,
      .len = kRsa4096NumWords,
  };
  crypto_const_word32_buf_t const_sig_buf = {
      .data = sig,
      .len = kRsa4096NumWords,
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
