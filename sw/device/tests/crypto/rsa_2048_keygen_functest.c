// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_datatypes.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
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
              .version = otcrypto_lib_version(),
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

  // Check that the moduli match.
  TRY_CHECK(ARRAYSIZE(pk->n.data) == ARRAYSIZE(sk->n.data));
  TRY_CHECK_ARRAYS_EQ(pk->n.data, sk->n.data, ARRAYSIZE(pk->n.data));

  // Check that d is at least 2^(len(n) / 2) (this is a FIPS requirement) by
  // ensuring that the most significant half is nonzero.
  bool d_large_enough = false;
  for (size_t i = kRsa2048NumWords / 2; i < kRsa2048NumWords; i++) {
    if ((sk->d0.data[i] ^ sk->d1.data[i]) != 0) {
      d_large_enough = true;
    }
  }
  TRY_CHECK(d_large_enough);

  // Hash the message.
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kTestMessage, kTestMessageLen);
  uint32_t msg_digest_data[256 / 32];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_256(&msg_buf, &msg_digest));

  uint32_t sig[kRsa2048NumWords];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, kRsa2048NumWords);
  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, kRsa2048NumWords);

  // Generate a signature.
  LOG_INFO("Starting signature generation...");
  TRY(otcrypto_rsa_sign(&private_key, msg_digest, kOtcryptoRsaPaddingPkcs,
                        &sig_buf));
  LOG_INFO("Signature generation complete.");
  LOG_INFO("OTBN instruction count: %u", otbn_instruction_count_get());

  // Try to verify the signature. If something is wrong with the key (nonprime
  // p and q, incorrect d), then this is likely to fail.
  LOG_INFO("Starting signature verification...");
  hardened_bool_t verification_result;
  TRY(otcrypto_rsa_verify(&public_key, msg_digest, kOtcryptoRsaPaddingPkcs,
                          &const_sig_buf, &verification_result));
  LOG_INFO("Signature verification complete.");
  LOG_INFO("OTBN instruction count: %u", otbn_instruction_count_get());

  // Expect the signature to pass verification.
  TRY_CHECK(verification_result == kHardenedBoolTrue);
  return OK_STATUS();
}

static status_t deterministic_keygen_test(void) {
  LOG_INFO("Running deterministic RSA-2048 keygen test...");

  static const uint8_t kSeedA[48] = {
      0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b,
      0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
      0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f, 0x30, 0x31, 0x32, 0x33,
      0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
  };
  static const uint8_t kSeedB[48] = {
      0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b,
      0x9c, 0x9d, 0x9e, 0x9f, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
      0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf, 0xb0, 0xb1, 0xb2, 0xb3,
      0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xbb, 0xbc, 0xbd, 0xbe, 0xbf,
  };
  otcrypto_const_byte_buf_t entropy_a =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kSeedA, sizeof(kSeedA));
  otcrypto_const_byte_buf_t entropy_b =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kSeedB, sizeof(kSeedB));

  uint32_t pub_data_1[kOtcryptoRsa2048PublicKeyBytes / sizeof(uint32_t)] = {0};
  uint32_t pub_data_2[kOtcryptoRsa2048PublicKeyBytes / sizeof(uint32_t)] = {0};
  uint32_t pub_data_3[kOtcryptoRsa2048PublicKeyBytes / sizeof(uint32_t)] = {0};
  otcrypto_unblinded_key_t pub_1 = {
      .key_mode = kTestKeyMode,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_data_1,
  };
  otcrypto_unblinded_key_t pub_2 = {
      .key_mode = kTestKeyMode,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_data_2,
  };
  otcrypto_unblinded_key_t pub_3 = {
      .key_mode = kTestKeyMode,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_data_3,
  };

  size_t keyblob_words =
      ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes, sizeof(uint32_t));
  uint32_t keyblob_1[keyblob_words];
  uint32_t keyblob_2[keyblob_words];
  uint32_t keyblob_3[keyblob_words];
  otcrypto_key_config_t priv_cfg = {
      .version = otcrypto_lib_version(),
      .key_mode = kTestKeyMode,
      .key_length = kOtcryptoRsa2048PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  otcrypto_blinded_key_t priv_1 = {
      .config = priv_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = keyblob_1,
  };
  otcrypto_blinded_key_t priv_2 = {
      .config = priv_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = keyblob_2,
  };
  otcrypto_blinded_key_t priv_3 = {
      .config = priv_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = keyblob_3,
  };

  // First deterministic keygen with seed A.
  TRY(otcrypto_rsa_keygen_deterministic(kOtcryptoRsaSize2048, &entropy_a,
                                        &pub_1, &priv_1));
  // Second deterministic keygen with the same seed A must produce the exact
  // same public modulus n and private exponent d = d0 ^ d1.
  TRY(otcrypto_rsa_keygen_deterministic(kOtcryptoRsaSize2048, &entropy_a,
                                        &pub_2, &priv_2));
  TRY_CHECK_ARRAYS_EQ(pub_data_1, pub_data_2, ARRAYSIZE(pub_data_1));

  rsa_2048_private_key_t *sk_1 = (rsa_2048_private_key_t *)priv_1.keyblob;
  rsa_2048_private_key_t *sk_2 = (rsa_2048_private_key_t *)priv_2.keyblob;
  for (size_t i = 0; i < kRsa2048NumWords; i++) {
    TRY_CHECK((sk_1->d0.data[i] ^ sk_1->d1.data[i]) ==
              (sk_2->d0.data[i] ^ sk_2->d1.data[i]));
  }

  // Deterministic keygen with a different seed B must produce a different key.
  TRY(otcrypto_rsa_keygen_deterministic(kOtcryptoRsaSize2048, &entropy_b,
                                        &pub_3, &priv_3));
  TRY_CHECK_ARRAYS_NE(pub_data_1, pub_data_3, ARRAYSIZE(pub_data_1));

  // Sign with priv_1 and verify with pub_2.
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kTestMessage, kTestMessageLen);
  uint32_t msg_digest_data[256 / 32];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_256(&msg_buf, &msg_digest));

  uint32_t sig[kRsa2048NumWords];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, kRsa2048NumWords);
  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, kRsa2048NumWords);
  TRY(otcrypto_rsa_sign(&priv_1, msg_digest, kOtcryptoRsaPaddingPkcs,
                        &sig_buf));
  hardened_bool_t verification_result = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&pub_2, msg_digest, kOtcryptoRsaPaddingPkcs,
                          &const_sig_buf, &verification_result));
  TRY_CHECK(verification_result == kHardenedBoolTrue);

  return OK_STATUS();
}

static status_t run_keygen_negative_tests(void) {
  LOG_INFO("Running RSA keygen negative tests");

  uint32_t pub_data[kOtcryptoRsa2048PublicKeyBytes / 4] = {0};
  otcrypto_unblinded_key_t valid_pub = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_data,
  };

  otcrypto_key_config_t valid_priv_cfg = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa2048PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t priv_blob[kOtcryptoRsa2048PrivateKeyblobBytes / 4] = {0};
  otcrypto_blinded_key_t valid_priv = {
      .config = valid_priv_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };

  // Null checks
  CHECK(otcrypto_rsa_keygen(kOtcryptoRsaSize2048, NULL, &valid_priv).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keygen_async_finalize(NULL, &valid_priv).value !=
        OTCRYPTO_OK.value);

  CHECK(otcrypto_rsa_keygen(kOtcryptoRsaSize2048, &valid_pub, NULL).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keygen_async_finalize(&valid_pub, NULL).value !=
        OTCRYPTO_OK.value);

  // Bad modes
  otcrypto_key_config_t bad_mode_cfg = valid_priv_cfg;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeEcdsaP256;
  otcrypto_blinded_key_t bad_priv_mode = {
      .config = bad_mode_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };
  CHECK(otcrypto_rsa_keygen(kOtcryptoRsaSize2048, &valid_pub, &bad_priv_mode)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keygen_async_finalize(&valid_pub, &bad_priv_mode).value !=
        OTCRYPTO_OK.value);

  // HW backed restriction
  otcrypto_key_config_t bad_hw_cfg = valid_priv_cfg;
  bad_hw_cfg.hw_backed = kHardenedBoolTrue;
  otcrypto_blinded_key_t bad_priv_hw = {
      .config = bad_hw_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };
  CHECK(otcrypto_rsa_keygen(kOtcryptoRsaSize2048, &valid_pub, &bad_priv_hw)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keygen_async_finalize(&valid_pub, &bad_priv_hw).value !=
        OTCRYPTO_OK.value);

  // Bad size enum
  CHECK(otcrypto_rsa_keygen((otcrypto_rsa_size_t)999, &valid_pub, &valid_priv)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keygen_async_start((otcrypto_rsa_size_t)999).value !=
        OTCRYPTO_OK.value);

  // Bad length
  otcrypto_blinded_key_t bad_priv_blob_len = {
      .config = valid_priv_cfg,
      .keyblob_length = 999,  // Should be kOtcryptoRsa2048PrivateKeyblobBytes
      .keyblob = priv_blob,
  };
  CHECK(
      otcrypto_rsa_keygen(kOtcryptoRsaSize2048, &valid_pub, &bad_priv_blob_len)
          .value != OTCRYPTO_OK.value);

  return OTCRYPTO_OK;
}

static status_t run_async_wrong_finalize_tests(void) {
  LOG_INFO("Running RSA async wrong-finalize negative tests.");

  uint32_t pub_data_2048[kOtcryptoRsa2048PublicKeyBytes / 4] = {0};
  otcrypto_unblinded_key_t valid_pub_2048 = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_data_2048,
  };

  uint32_t priv_blob_2048[kOtcryptoRsa2048PrivateKeyblobBytes / 4] = {0};
  otcrypto_blinded_key_t valid_priv_2048 = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeRsaSignPkcs,
              .key_length = kOtcryptoRsa2048PrivateKeyBytes,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = priv_blob_2048,
  };

  uint32_t pub_data_3072[kOtcryptoRsa3072PublicKeyBytes / 4] = {0};
  otcrypto_unblinded_key_t valid_pub_3072 = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa3072PublicKeyBytes,
      .key = pub_data_3072,
  };

  uint32_t priv_blob_3072[kOtcryptoRsa3072PrivateKeyblobBytes / 4] = {0};
  otcrypto_blinded_key_t valid_priv_3072 = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeRsaSignPkcs,
              .key_length = kOtcryptoRsa3072PrivateKeyBytes,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kOtcryptoRsa3072PrivateKeyblobBytes,
      .keyblob = priv_blob_3072,
  };

  LOG_INFO("Starting 2048 standard keygen, attempting cofactor finalize...");
  CHECK_STATUS_OK(otcrypto_rsa_keygen_async_start(kOtcryptoRsaSize2048));

  CHECK(otcrypto_rsa_keypair_from_cofactor_async_finalize(&valid_pub_2048,
                                                          &valid_priv_2048)
            .value == OTCRYPTO_RECOV_ERR.value);

  LOG_INFO(
      "Starting 2048 standard keygen, attempting 3072 standard finalize...");
  CHECK_STATUS_OK(otcrypto_rsa_keygen_async_start(kOtcryptoRsaSize2048));

  CHECK(otcrypto_rsa_keygen_async_finalize(&valid_pub_3072, &valid_priv_3072)
            .value == OTCRYPTO_RECOV_ERR.value);

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));

  status_t test_result = OK_STATUS();
  EXECUTE_TEST(test_result, keygen_then_sign_test);
  EXECUTE_TEST(test_result, deterministic_keygen_test);
  EXECUTE_TEST(test_result, run_async_wrong_finalize_tests);
  // This test leaves the OTBN running, best call it at the end.
  EXECUTE_TEST(test_result, run_keygen_negative_tests);
  return status_ok(test_result);
}
