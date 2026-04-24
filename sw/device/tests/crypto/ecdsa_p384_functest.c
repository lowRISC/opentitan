// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of 32-bit words in a P-384 public key. */
  kP384PublicKeyWords = 768 / 32,
  /* Number of 32-bit words in a P-384 signature. */
  kP384SignatureWords = 768 / 32,
  /* Number of 32-bit words in a P-384 signature. */
  kP384DigestWords = 384 / 32,
  /* Number of bytes in a P-384 private key. */
  kP384PrivateKeyBytes = 384 / 8,
  /* Number of bytes in a P-384 secret scalar. */
  kP384SecretScalarBytes = 448 / 8,
  /* Number of words in a P-384 secret scalar. */
  kP384SecretScalarWords = kP384SecretScalarBytes / 4,
  /* Number of bytes in a P-384 scalar input. */
  kP384TestVectorScalarInpBytes = 384 / 8,
  /* Number of words in a P-384 scalar input. */
  kP384TestVectorScalarInpWords = kP384TestVectorScalarInpBytes / 4,
};

// Message
static const char kMessage[] = "test message";

// The KAT vectors are from:
// https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/P384_SHA384.pdf

// Known answer test message.
static const char kKATMessage[] = "Example of ECDSA with P-384";

// Known answer test secret scalar k.
static const uint32_t kKATSecretScalar[kP384TestVectorScalarInpWords] = {
    0xC2F43FEF, 0xEDCAE06C, 0x9FC43F85, 0x0878E074, 0x4F013768, 0x2ED95F05,
    0x4701749E, 0x2A459B53, 0x1EC6A784, 0x94E3DDA8, 0x8C0BEA83, 0x2E44EF1F,

};

// Known answer test key d.
static const uint32_t kKATKey[kP384TestVectorScalarInpWords] = {
    0xD83F8A08, 0xD1224B57, 0x5E6B9714, 0xE393A856, 0x392E6A0A, 0x55E73DFC,
    0xFC6ACB04, 0xB4FAAE4A, 0x6CE3A3E3, 0xC0584B1C, 0x629E4B48, 0xF92C02ED,
};

// Known answer test expected signature.
static const uint32_t kKATExpSignature[kP384SignatureWords] = {
    0x01A27088, 0xFCEF9FAF, 0x2CC7D507, 0x332795D0, 0xB57DD41A, 0x13D040D9,
    0xB40EA3B3, 0xDA9F66A3, 0x8113C7CA, 0x08756F06, 0xC0D38D82, 0x30EA514F,
    0x49683AD8, 0x821C46D5, 0xBE620BFB, 0xFD1F7D5D, 0xFBB7B94E, 0xC4476875,
    0xD6FCAA66, 0x67A43922, 0xBF78ADF0, 0x6C9027BC, 0x4BE414F4, 0xCC808E50,
};

static const otcrypto_key_config_t kPrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP384,
    .key_length = kP384PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static status_t sign_then_verify_test(void) {
  hardened_bool_t verificationResult;

  // Allocate space for a masked private key.
  uint32_t keyblob[keyblob_num_words(kPrivateKeyConfig)];
  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Allocate space for a public key.
  uint32_t pk[kP384PublicKeyWords] = {0};
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(pk),
      .key = pk,
  };

  // Generate a keypair.
  LOG_INFO("Generating keypair...");
  CHECK_STATUS_OK(otcrypto_ecdsa_p384_keygen(&private_key, &public_key));

  // Hash the message.
  otcrypto_const_byte_buf_t msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, (unsigned char *)&kMessage,
                        sizeof(kMessage) - 1);
  uint32_t msg_digest_data[kP384DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_384(&msg, &msg_digest));

  // Allocate space for the signature.
  uint32_t sig[kP384SignatureWords] = {0};

  // Generate a signature for the message.
  LOG_INFO("Signing...");
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  CHECK_STATUS_OK(otcrypto_ecdsa_p384_sign_verify(&private_key, &public_key,
                                                  msg_digest, &sig_buf));

  // Verify the signature.
  LOG_INFO("Verifying...");
  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, ARRAYSIZE(sig));
  CHECK_STATUS_OK(otcrypto_ecdsa_p384_verify(
      &public_key, msg_digest, &const_sig_buf, &verificationResult));
  TRY_CHECK(verificationResult == kHardenedBoolTrue);

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

/**
 * A test where a known input is signed and is compared to the expected output.
 * In addition, it draws randomness to share the known input using
 * hardened_memshred. The input is shared using the hardened_sub_mod function
 * using the P-384 curve order n.
 */
static status_t sign_kat(void) {
  uint32_t keyblob_len = 2 * kP384SecretScalarWords;

  // P-384 curve order n, padded to 448 bits (14 words) for our math operations.
  static const uint32_t kP384Order[kP384SecretScalarWords] = {
      0xCCC52973, 0xECEC196A, 0x48B0A77A, 0x581A0DB2, 0xF4372DDF,
      0xC7634D81, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF,
      0xFFFFFFFF, 0xFFFFFFFF, 0x00000000, 0x00000000};

  uint32_t unmasked_val[kP384SecretScalarWords];
  uint32_t share1_rand[kP384SecretScalarWords];
  uint32_t share0[kP384SecretScalarWords];
  uint32_t share1[kP384SecretScalarWords];

  memset(unmasked_val, 0, kP384SecretScalarBytes);
  memcpy(unmasked_val, kKATSecretScalar, kP384TestVectorScalarInpBytes);

  // Generate a random value and reduce it modulo n to get a valid share1
  TRY(hardened_memshred(share1_rand, kP384SecretScalarWords));
  TRY(hardened_mod_reduce(share1_rand, kP384Order, kP384SecretScalarWords,
                          share1));

  // Calculate share0 = (unmasked_val - share1) mod n
  TRY(hardened_sub_mod(unmasked_val, share1, kP384Order, kP384SecretScalarWords,
                       share0));

  // Allocate space for a masked secret scalar.
  uint32_t keyblob_scalar[keyblob_len];
  otcrypto_blinded_key_t secret_scalar = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob_scalar),
      .keyblob = keyblob_scalar,
  };
  memcpy(keyblob_scalar, share0, kP384SecretScalarBytes);
  // We copy over the full random bits
  memcpy(keyblob_scalar + kP384SecretScalarWords, share1,
         kP384SecretScalarBytes);
  secret_scalar.checksum = integrity_blinded_checksum(&secret_scalar);

  memset(unmasked_val, 0, kP384SecretScalarBytes);
  memcpy(unmasked_val, kKATKey, kP384TestVectorScalarInpBytes);

  // Generate new random noise and reduce it modulo n
  TRY(hardened_memshred(share1_rand, kP384SecretScalarWords));
  TRY(hardened_mod_reduce(share1_rand, kP384Order, kP384SecretScalarWords,
                          share1));

  // Calculate share0 = (unmasked_val - share1) mod n
  TRY(hardened_sub_mod(unmasked_val, share1, kP384Order, kP384SecretScalarWords,
                       share0));

  // Allocate space for a masked private key.
  uint32_t keyblob_sk[keyblob_len];
  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
  };
  memcpy(keyblob_sk, share0, kP384SecretScalarBytes);
  memcpy(keyblob_sk + kP384SecretScalarWords, share1, kP384SecretScalarBytes);
  private_key.checksum = integrity_blinded_checksum(&private_key);

  // Hash the message.
  otcrypto_const_byte_buf_t msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t,
                        (unsigned char *)&kKATMessage, sizeof(kKATMessage) - 1);
  uint32_t msg_digest_data[kP384DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_384(&msg, &msg_digest));

  // Allocate space for the signature.
  uint32_t sig[kP384SignatureWords] = {0};

  // Generate a signature for the message.
  LOG_INFO("Signing...");
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  CHECK_STATUS_OK(otcrypto_ecdsa_p384_sign_config_k(
      &private_key, &secret_scalar, msg_digest, &sig_buf));

  // Check if the signature matches the expected value.
  TRY_CHECK_ARRAYS_EQ(sig, kKATExpSignature, kP384SignatureWords);

  return OTCRYPTO_OK;
}

static status_t run_ecdsa_negative_tests(void) {
  LOG_INFO("Running ECDSA BAD_ARGS negative tests.");

  uint32_t priv_keyblob[112 / 4] = {0};
  otcrypto_blinded_key_t valid_priv = {
      .config = kPrivateKeyConfig,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  valid_priv.checksum = integrity_blinded_checksum(&valid_priv);

  uint32_t pub_key_data[96 / 4] = {0};
  otcrypto_unblinded_key_t valid_pub = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = 96,
      .key = pub_key_data,
  };
  valid_pub.checksum = integrity_unblinded_checksum(&valid_pub);

  uint32_t digest_data[48 / 4] = {0};
  otcrypto_hash_digest_t valid_digest = {
      .data = digest_data,
      .len = 12,
  };

  uint32_t sig_data[96 / 4] = {0};
  otcrypto_word32_buf_t valid_sig =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig_data, 24);
  otcrypto_const_word32_buf_t valid_const_sig =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig_data, 24);

  hardened_bool_t verify_res;

  // ECDSA keygen negative tests

  // Null pointers
  CHECK(otcrypto_ecdsa_p384_keygen(NULL, &valid_pub).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_keygen_async_start(NULL).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_keygen_async_finalize(NULL, &valid_pub).value !=
        OTCRYPTO_OK.value);

  CHECK(otcrypto_ecdsa_p384_keygen(&valid_priv, NULL).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_keygen_async_finalize(&valid_priv, NULL).value !=
        OTCRYPTO_OK.value);

  // Null pointer keyblob
  otcrypto_blinded_key_t bad_priv_null = {
      .config = kPrivateKeyConfig,
      .keyblob_length = 112,
      .keyblob = NULL,
  };
  CHECK(otcrypto_ecdsa_p384_keygen(&bad_priv_null, &valid_pub).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_keygen_async_start(&bad_priv_null).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_keygen_async_finalize(&bad_priv_null, &valid_pub)
            .value != OTCRYPTO_OK.value);

  // Bad mode
  otcrypto_key_config_t bad_mode_cfg = kPrivateKeyConfig;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeEcdhP384;
  otcrypto_blinded_key_t bad_priv_mode = {
      .config = bad_mode_cfg,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  bad_priv_mode.checksum = integrity_blinded_checksum(&bad_priv_mode);
  CHECK(otcrypto_ecdsa_p384_keygen(&bad_priv_mode, &valid_pub).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_keygen_async_start(&bad_priv_mode).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_keygen_async_finalize(&bad_priv_mode, &valid_pub)
            .value != OTCRYPTO_OK.value);

  // Bad public key length
  otcrypto_unblinded_key_t bad_pub_len = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = 95,
      .key = pub_key_data,
  };
  bad_pub_len.checksum = integrity_unblinded_checksum(&bad_pub_len);
  CHECK(otcrypto_ecdsa_p384_keygen(&valid_priv, &bad_pub_len).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_keygen_async_finalize(&valid_priv, &bad_pub_len)
            .value != OTCRYPTO_OK.value);

  // Bad keyblob length
  otcrypto_blinded_key_t bad_priv_blob_len = {
      .config = kPrivateKeyConfig,
      .keyblob_length = 111,  // Should be 112
      .keyblob = priv_keyblob,
  };
  bad_priv_blob_len.checksum = integrity_blinded_checksum(&bad_priv_blob_len);
  CHECK(otcrypto_ecdsa_p384_keygen(&bad_priv_blob_len, &valid_pub).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_keygen_async_start(&bad_priv_blob_len).value !=
        OTCRYPTO_OK.value);
  CHECK(
      otcrypto_ecdsa_p384_keygen_async_finalize(&bad_priv_blob_len, &valid_pub)
          .value != OTCRYPTO_OK.value);

  // Bad hardware backed configuration
  otcrypto_key_config_t bad_hw_cfg = kPrivateKeyConfig;
  bad_hw_cfg.hw_backed = (hardened_bool_t)0x12345678;  // Invalid boolean
  otcrypto_blinded_key_t bad_priv_hw = {
      .config = bad_hw_cfg,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  bad_priv_hw.checksum = integrity_blinded_checksum(&bad_priv_hw);
  CHECK(otcrypto_ecdsa_p384_keygen(&bad_priv_hw, &valid_pub).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_keygen_async_start(&bad_priv_hw).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_keygen_async_finalize(&bad_priv_hw, &valid_pub)
            .value != OTCRYPTO_OK.value);

  // ECDSA sign negative tests

  // Null pointers
  CHECK(otcrypto_ecdsa_p384_sign(NULL, valid_digest, &valid_sig).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_sign_async_start(NULL, valid_digest).value !=
        OTCRYPTO_OK.value);

  // Null digest data
  otcrypto_hash_digest_t bad_digest_null = {
      .data = NULL,
      .len = 12,
  };
  CHECK(otcrypto_ecdsa_p384_sign(&valid_priv, bad_digest_null, &valid_sig)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_sign_async_start(&valid_priv, bad_digest_null)
            .value != OTCRYPTO_OK.value);

  // Bad digest length
  otcrypto_hash_digest_t bad_digest_len = {
      .data = digest_data,
      .len = 11,
  };
  CHECK(
      otcrypto_ecdsa_p384_sign(&valid_priv, bad_digest_len, &valid_sig).value !=
      OTCRYPTO_OK.value);
  CHECK(
      otcrypto_ecdsa_p384_sign_async_start(&valid_priv, bad_digest_len).value !=
      OTCRYPTO_OK.value);

  // Null signature data
  otcrypto_word32_buf_t bad_sig_null =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, NULL, 24);
  CHECK(otcrypto_ecdsa_p384_sign(&valid_priv, valid_digest, &bad_sig_null)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_sign_async_finalize(&bad_sig_null).value !=
        OTCRYPTO_OK.value);

  // Corrupt private key checksum
  otcrypto_blinded_key_t bad_priv_chk = {
      .config = kPrivateKeyConfig,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  bad_priv_chk.checksum = valid_priv.checksum ^ 0xFFFFFFFF;
  CHECK(
      otcrypto_ecdsa_p384_sign(&bad_priv_chk, valid_digest, &valid_sig).value !=
      OTCRYPTO_OK.value);
  CHECK(
      otcrypto_ecdsa_p384_sign_async_start(&bad_priv_chk, valid_digest).value !=
      OTCRYPTO_OK.value);

  // Bad signature buffer length
  otcrypto_word32_buf_t bad_sig_len =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig_data, 23);  // Should be 24
  CHECK(
      otcrypto_ecdsa_p384_sign(&valid_priv, valid_digest, &bad_sig_len).value !=
      OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_sign_async_finalize(&bad_sig_len).value !=
        OTCRYPTO_OK.value);

  // ECDSA sign config k negative tests

  CHECK(otcrypto_ecdsa_p384_sign_config_k(NULL, &valid_priv, valid_digest,
                                          &valid_sig)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_sign_config_k_async_start(NULL, &valid_priv,
                                                      valid_digest)
            .value != OTCRYPTO_OK.value);

  // Passing a bad signature buffer length
  CHECK(otcrypto_ecdsa_p384_sign_config_k(&valid_priv, &valid_priv,
                                          valid_digest, &bad_sig_len)
            .value != OTCRYPTO_OK.value);

  // ECDSA verify negative tests

  // Null pointers
  CHECK(otcrypto_ecdsa_p384_verify(NULL, valid_digest, &valid_const_sig,
                                   &verify_res)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_verify_async_start(NULL, valid_digest,
                                               &valid_const_sig)
            .value != OTCRYPTO_OK.value);

  CHECK(otcrypto_ecdsa_p384_verify(&valid_pub, valid_digest, &valid_const_sig,
                                   NULL)
            .value != OTCRYPTO_OK.value);
  CHECK(
      otcrypto_ecdsa_p384_verify_async_finalize(&valid_const_sig, NULL).value !=
      OTCRYPTO_OK.value);

  // Corrupt public key checksum
  otcrypto_unblinded_key_t bad_pub_chk = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = 96,
      .key = pub_key_data,
  };
  bad_pub_chk.checksum = valid_pub.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_ecdsa_p384_verify(&bad_pub_chk, valid_digest, &valid_const_sig,
                                   &verify_res)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_verify_async_start(&bad_pub_chk, valid_digest,
                                               &valid_const_sig)
            .value != OTCRYPTO_OK.value);

  // Bad signature length
  otcrypto_const_word32_buf_t bad_const_sig_len = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, sig_data, 23);  // Should be 24
  CHECK(otcrypto_ecdsa_p384_verify(&valid_pub, valid_digest, &bad_const_sig_len,
                                   &verify_res)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdsa_p384_verify_async_start(&valid_pub, valid_digest,
                                               &bad_const_sig_len)
            .value != OTCRYPTO_OK.value);
  CHECK(
      otcrypto_ecdsa_p384_verify_async_finalize(&bad_const_sig_len, &verify_res)
          .value != OTCRYPTO_OK.value);

  return OTCRYPTO_OK;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));
  EXECUTE_TEST(result, sign_then_verify_test);
  EXECUTE_TEST(result, sign_kat);
  EXECUTE_TEST(result, run_ecdsa_negative_tests);

  return status_ok(result);
}
