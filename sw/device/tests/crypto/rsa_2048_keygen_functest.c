// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_datatypes.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module for status messages.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Message data for testing.
static const unsigned char kTestMessage[] = "Test message.";
static const size_t kTestMessageLen = sizeof(kTestMessage) - 1;

// RSA key mode for testing.
static const otcrypto_key_mode_t kTestKeyMode = kOtcryptoKeyModeRsaSignPkcs;

status_t keygen_then_sign_test(void) {
  // Allocate buffer for the public key.
  uint32_t public_key_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes,
                                    sizeof(uint32_t))];
  memset(public_key_data, 0, sizeof(public_key_data));
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kTestKeyMode,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = public_key_data,
  };

  // Allocate buffers for the private key.
  size_t keyblob_words =
      ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes, sizeof(uint32_t));
  uint32_t keyblob[keyblob_words];
  memset(keyblob, 0, sizeof(keyblob));
  otcrypto_blinded_key_t private_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kTestKeyMode,
              .key_length = kOtcryptoRsa2048PrivateKeyBytes,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = keyblob,
  };

  // Generate the key pair.
  LOG_INFO("Starting keypair generation...");
  TRY(otcrypto_rsa_keygen(kOtcryptoRsaSize2048, &public_key, &private_key));
  LOG_INFO("Keypair generation complete.");
  LOG_INFO("OTBN instruction count: %u", otbn_instruction_count_get());

  // Interpret public key using internal RSA datatype.
  TRY_CHECK(public_key.key_length == sizeof(rsa_2048_public_key_t));
  rsa_2048_public_key_t *pk = (rsa_2048_public_key_t *)public_key.key;

  // Interpret private key using internal RSA datatype.
  TRY_CHECK(private_key.keyblob_length == sizeof(rsa_2048_private_key_t));
  rsa_2048_private_key_t *sk = (rsa_2048_private_key_t *)private_key.keyblob;

  // Check that the key uses the F4 exponent.
  TRY_CHECK(pk->e == 65537);

  // Check that the moduli match.
  TRY_CHECK(ARRAYSIZE(pk->n.data) == ARRAYSIZE(sk->n.data));
  TRY_CHECK_ARRAYS_EQ(pk->n.data, sk->n.data, ARRAYSIZE(pk->n.data));

  // Check that d is at least 2^(len(n) / 2) (this is a FIPS requirement) by
  // ensuring that the most significant half is nonzero.
  bool d_large_enough = false;
  for (size_t i = kRsa2048NumWords / 2; i < kRsa2048NumWords; i++) {
    if (sk->d.data[i] != 0) {
      d_large_enough = true;
    }
  }
  TRY_CHECK(d_large_enough);

  // Hash the message.
  otcrypto_const_byte_buf_t msg_buf = {.data = kTestMessage,
                                       .len = kTestMessageLen};
  uint32_t msg_digest_data[256 / 32];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_256(msg_buf, &msg_digest));

  uint32_t sig[kRsa2048NumWords];
  otcrypto_word32_buf_t sig_buf = {
      .data = sig,
      .len = kRsa2048NumWords,
  };
  otcrypto_const_word32_buf_t const_sig_buf = {
      .data = sig,
      .len = kRsa2048NumWords,
  };

  // Generate a signature.
  LOG_INFO("Starting signature generation...");
  TRY(otcrypto_rsa_sign(&private_key, msg_digest, kOtcryptoRsaPaddingPkcs,
                        sig_buf));
  LOG_INFO("Signature generation complete.");
  LOG_INFO("OTBN instruction count: %u", otbn_instruction_count_get());

  // Try to verify the signature. If something is wrong with the key (nonprime
  // p and q, incorrect d), then this is likely to fail.
  LOG_INFO("Starting signature verification...");
  hardened_bool_t verification_result;
  TRY(otcrypto_rsa_verify(&public_key, msg_digest, kOtcryptoRsaPaddingPkcs,
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
