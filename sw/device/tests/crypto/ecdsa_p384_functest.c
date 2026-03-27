// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/keyblob.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
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
  otcrypto_const_byte_buf_t msg = {
      .len = sizeof(kMessage) - 1,
      .data = (unsigned char *)&kMessage,
  };
  uint32_t msg_digest_data[kP384DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_384(msg, &msg_digest));

  // Allocate space for the signature.
  uint32_t sig[kP384SignatureWords] = {0};

  // Generate a signature for the message.
  LOG_INFO("Signing...");
  CHECK_STATUS_OK(otcrypto_ecdsa_p384_sign_verify(
      &private_key, &public_key, msg_digest,
      (otcrypto_word32_buf_t){.data = sig, .len = ARRAYSIZE(sig)}));

  // Verify the signature.
  LOG_INFO("Verifying...");
  CHECK_STATUS_OK(otcrypto_ecdsa_p384_verify(
      &public_key, msg_digest,
      (otcrypto_const_word32_buf_t){.data = sig, .len = ARRAYSIZE(sig)},
      &verificationResult));
  TRY_CHECK(verificationResult == kHardenedBoolTrue);

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

static status_t sign_kat(void) {
  uint32_t keyblob_len = 2 * kP384SecretScalarWords;

  // Allocate space for a masked secret scalar.
  uint32_t keyblob_scalar[keyblob_len];
  otcrypto_blinded_key_t secret_scalar = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob_scalar),
      .keyblob = keyblob_scalar,
  };
  memset(keyblob_scalar, 0, 2 * kP384SecretScalarBytes);
  memcpy(keyblob_scalar, kKATSecretScalar, kP384TestVectorScalarInpBytes);
  secret_scalar.checksum = integrity_blinded_checksum(&secret_scalar);

  // Allocate space for a masked private key.
  uint32_t keyblob_sk[keyblob_len];
  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
  };
  memset(keyblob_sk, 0, 2 * kP384SecretScalarBytes);
  memcpy(keyblob_sk, kKATKey, kP384TestVectorScalarInpBytes);
  private_key.checksum = integrity_blinded_checksum(&private_key);

  // Hash the message.
  otcrypto_const_byte_buf_t msg = {
      .len = sizeof(kKATMessage) - 1,
      .data = (unsigned char *)&kKATMessage,
  };
  uint32_t msg_digest_data[kP384DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_384(msg, &msg_digest));

  // Allocate space for the signature.
  uint32_t sig[kP384SignatureWords] = {0};

  // Generate a signature for the message.
  LOG_INFO("Signing...");
  CHECK_STATUS_OK(otcrypto_ecdsa_p384_sign_config_k(
      &private_key, &secret_scalar, msg_digest,
      (otcrypto_word32_buf_t){.data = sig, .len = ARRAYSIZE(sig)}));

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
  otcrypto_word32_buf_t valid_sig = {
      .data = sig_data,
      .len = 24,
  };
  otcrypto_const_word32_buf_t valid_const_sig = {
      .data = sig_data,
      .len = 24,
  };
  hardened_bool_t verify_res;

  // ECDSA keygen negative tests
  CHECK(otcrypto_ecdsa_p384_keygen(NULL, &valid_pub).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_ecdsa_p384_keygen(&valid_priv, NULL).value ==
        OTCRYPTO_BAD_ARGS.value);

  otcrypto_blinded_key_t bad_priv_null = {
      .config = kPrivateKeyConfig,
      .keyblob_length = 112,
      .keyblob = NULL,
  };
  CHECK(otcrypto_ecdsa_p384_keygen(&bad_priv_null, &valid_pub).value ==
        OTCRYPTO_BAD_ARGS.value);

  otcrypto_key_config_t bad_mode_cfg = kPrivateKeyConfig;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeEcdhP384;
  otcrypto_blinded_key_t bad_priv_mode = {
      .config = bad_mode_cfg,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  bad_priv_mode.checksum = integrity_blinded_checksum(&bad_priv_mode);
  CHECK(otcrypto_ecdsa_p384_keygen(&bad_priv_mode, &valid_pub).value ==
        OTCRYPTO_BAD_ARGS.value);

  otcrypto_unblinded_key_t bad_pub_len = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = 95,
      .key = pub_key_data,
  };
  bad_pub_len.checksum = integrity_unblinded_checksum(&bad_pub_len);
  CHECK(otcrypto_ecdsa_p384_keygen(&valid_priv, &bad_pub_len).value ==
        OTCRYPTO_BAD_ARGS.value);

  // ECDSA sign negative tests
  CHECK(otcrypto_ecdsa_p384_sign(NULL, valid_digest, valid_sig).value ==
        OTCRYPTO_BAD_ARGS.value);

  otcrypto_hash_digest_t bad_digest_null = {
      .data = NULL,
      .len = 12,
  };
  CHECK(
      otcrypto_ecdsa_p384_sign(&valid_priv, bad_digest_null, valid_sig).value ==
      OTCRYPTO_BAD_ARGS.value);

  otcrypto_hash_digest_t bad_digest_len = {
      .data = digest_data,
      .len = 11,
  };
  CHECK(
      otcrypto_ecdsa_p384_sign(&valid_priv, bad_digest_len, valid_sig).value ==
      OTCRYPTO_BAD_ARGS.value);

  otcrypto_word32_buf_t bad_sig_null = {
      .data = NULL,
      .len = 24,
  };
  CHECK(
      otcrypto_ecdsa_p384_sign(&valid_priv, valid_digest, bad_sig_null).value ==
      OTCRYPTO_BAD_ARGS.value);

  otcrypto_blinded_key_t bad_priv_chk = {
      .config = kPrivateKeyConfig,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  bad_priv_chk.checksum = valid_priv.checksum ^ 0xFFFFFFFF;
  CHECK(
      otcrypto_ecdsa_p384_sign(&bad_priv_chk, valid_digest, valid_sig).value ==
      OTCRYPTO_BAD_ARGS.value);

  // ECDSA verify negative tests
  CHECK(otcrypto_ecdsa_p384_verify(NULL, valid_digest, valid_const_sig,
                                   &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_ecdsa_p384_verify(&valid_pub, valid_digest, valid_const_sig,
                                   NULL)
            .value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_unblinded_key_t bad_pub_chk = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = 96,
      .key = pub_key_data,
  };
  bad_pub_chk.checksum = valid_pub.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_ecdsa_p384_verify(&bad_pub_chk, valid_digest, valid_const_sig,
                                   &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_const_word32_buf_t bad_const_sig_len = {
      .data = sig_data,
      .len = 23,
  };
  CHECK(otcrypto_ecdsa_p384_verify(&valid_pub, valid_digest, bad_const_sig_len,
                                   &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);

  return OTCRYPTO_OK;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  // Initialize the entropy complex.
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  EXECUTE_TEST(result, sign_then_verify_test);
  EXECUTE_TEST(result, sign_kat);
  EXECUTE_TEST(result, run_ecdsa_negative_tests);

  return status_ok(result);
}
