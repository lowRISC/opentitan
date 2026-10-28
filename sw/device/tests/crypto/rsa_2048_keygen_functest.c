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

static status_t find_next_prime_2048(uint32_t candidate[kRsa2048NumWords / 2],
                                     size_t *attempts) {
  *attempts = 0;
  for (size_t i = 0; i < 16; ++i) {
    otcrypto_const_word32_buf_t cand_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_word32_buf_t, candidate, kRsa2048NumWords / 2);
    hardened_bool_t prime_ok = kHardenedBoolFalse;
    TRY(otcrypto_rsa_prime_check(kOtcryptoRsaSize2048, &cand_buf, &prime_ok));
    *attempts += 1;
    if (prime_ok == kHardenedBoolTrue) {
      return OK_STATUS();
    }
    candidate[0] += 4;
  }
  return INTERNAL();
}

static status_t deterministic_keygen_test(void) {
  LOG_INFO("Running deterministic RSA-2048 prime check and keygen test...");

  // Starting candidate for p: candidate[0] = 0x7fa4d487 is composite, and
  // candidate[0] + 4 = 0x7fa4d48b is prime with p = 3 (mod 8), verifying that
  // otcrypto_rsa_prime_check tests 3 (mod 4) candidates as-is.
  uint32_t prime_p[kRsa2048NumWords / 2] = {
      0x7fa4d487u, 0xf1ff4004u, 0xa61a8263u, 0x1ce85b1du, 0x128d7b8eu,
      0x3072cec3u, 0xaea6e426u, 0x0616596au, 0x3c11797au, 0x320dfccbu,
      0xc97556ffu, 0xa68fb636u, 0xc5dd99b5u, 0x22a11a73u, 0xc16fcd1du,
      0xd9994a6cu, 0x7429616du, 0xe31534feu, 0xb572776du, 0xe9ec0158u,
      0x08e41f09u, 0x0ded3fa1u, 0xf654009bu, 0x3e1ae98eu, 0xdfc13527u,
      0x865983b3u, 0x006512feu, 0xb5c07dabu, 0x3064ae89u, 0xf3ee2ba1u,
      0x86f4e339u, 0xe14a1a00u,
  };
  // Starting candidate for q: candidate[0] = 0xaccd1283 is composite, and
  // candidate[0] + 4 = 0xaccd1287 is prime with q = 7 (mod 8).
  uint32_t prime_q[kRsa2048NumWords / 2] = {
      0xaccd1283u, 0xb8f02c5fu, 0x5a092627u, 0x2f0f1a4bu, 0xfd17457au,
      0x74848d63u, 0xf95018f6u, 0xa23de815u, 0xa002f551u, 0x3b1ccf90u,
      0xdb83c679u, 0xe574c6f7u, 0x56df0ed7u, 0xa42f1606u, 0xb34820d1u,
      0xce87067du, 0x7b878125u, 0xb504d87du, 0xe9a6954cu, 0xa9496837u,
      0xa9867857u, 0x1acbb155u, 0x618a6cb5u, 0x036a9a17u, 0x5a4a96abu,
      0x92802a56u, 0x1f30d599u, 0x0d47cd2bu, 0xcc060a39u, 0x6c30547bu,
      0x6b358d9du, 0xff490afeu,
  };

  // Reject invalid candidate (not 3 mod 4).
  uint32_t bad_cand[kRsa2048NumWords / 2];
  memcpy(bad_cand, prime_p, sizeof(bad_cand));
  bad_cand[0] &= ~2u;
  otcrypto_const_word32_buf_t bad_cand_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, bad_cand, ARRAYSIZE(bad_cand));
  hardened_bool_t prime_ok = kHardenedBoolFalse;
  TRY_CHECK(
      otcrypto_rsa_prime_check(kOtcryptoRsaSize2048, &bad_cand_buf, &prime_ok)
          .value == OTCRYPTO_BAD_ARGS.value);

  // Step through candidates to find p and q (each takes 2 checks: 1 composite
  // rejection followed by 1 prime acceptance).
  size_t attempts_p = 0;
  size_t attempts_q = 0;
  TRY(find_next_prime_2048(prime_p, &attempts_p));
  TRY_CHECK(attempts_p == 2);
  TRY_CHECK((prime_p[0] & 7u) == 3u);

  TRY(find_next_prime_2048(prime_q, &attempts_q));
  TRY_CHECK(attempts_q == 2);

  // Compute n = p * q using otcrypto_rsa_create_n_from_primes.
  uint32_t n_data[kRsa2048NumWords] = {0};
  otcrypto_const_word32_buf_t p_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, prime_p, ARRAYSIZE(prime_p));
  otcrypto_const_word32_buf_t q_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, prime_q, ARRAYSIZE(prime_q));
  otcrypto_word32_buf_t n_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, n_data, ARRAYSIZE(n_data));
  otcrypto_const_word32_buf_t const_n_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, n_data, ARRAYSIZE(n_data));
  TRY(otcrypto_rsa_create_n_from_primes(kOtcryptoRsaSize2048, &p_buf, &q_buf,
                                        &n_buf));

  uint32_t zero_share[kRsa2048NumWords / 2] = {0};
  otcrypto_const_word32_buf_t p_share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, zero_share, ARRAYSIZE(zero_share));

  uint32_t pub_data_1[kOtcryptoRsa2048PublicKeyBytes / sizeof(uint32_t)] = {0};
  uint32_t pub_data_2[kOtcryptoRsa2048PublicKeyBytes / sizeof(uint32_t)] = {0};
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

  size_t keyblob_words =
      ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes, sizeof(uint32_t));
  uint32_t keyblob_1[keyblob_words];
  uint32_t keyblob_2[keyblob_words];
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

  // Construct keypair twice from (n, p) and verify determinism of n and d.
  TRY(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize2048, &const_n_buf,
                                         &p_buf, &p_share1_buf, &pub_1,
                                         &priv_1));
  TRY(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize2048, &const_n_buf,
                                         &p_buf, &p_share1_buf, &pub_2,
                                         &priv_2));
  TRY_CHECK_ARRAYS_EQ(pub_data_1, n_data, ARRAYSIZE(n_data));
  TRY_CHECK_ARRAYS_EQ(pub_data_1, pub_data_2, ARRAYSIZE(pub_data_1));

  rsa_2048_private_key_t *sk_1 = (rsa_2048_private_key_t *)priv_1.keyblob;
  rsa_2048_private_key_t *sk_2 = (rsa_2048_private_key_t *)priv_2.keyblob;
  for (size_t i = 0; i < kRsa2048NumWords; i++) {
    TRY_CHECK((sk_1->d0.data[i] ^ sk_1->d1.data[i]) ==
              (sk_2->d0.data[i] ^ sk_2->d1.data[i]));
  }

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
