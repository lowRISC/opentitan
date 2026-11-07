// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha1.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

/**
 * Android KeyMint VTS (`SigningOperationsTest.Rsa*` &
 * `EncryptionOperationsTest.Rsa*`) conformance test suite for `otcrypto_rsa`.
 *
 * Upstream AOSP Reference:
 *   `hardware/interfaces/security/keymint/aidl/vts/functional/KeyMintTest.cpp`
 *   (Signing lines 2935-3415; Encryption lines 5410-5834)
 *
 * Test Mapping:
 *   - `rsa_vts_signing_no_digest_and_raw_test`:
 *     - `TEST_P(SigningOperationsTest, RsaSuccess)` (L2935)
 *     - `TEST_P(SigningOperationsTest, RsaPkcs1NoDigestSuccess)` (L3122)
 *     - `TEST_P(SigningOperationsTest, RsaPkcs1NoDigestTooLong)` (L3141)
 *     - `TEST_P(SigningOperationsTest, RsaNoDigest)` (L3321)
 *     - `TEST_P(SigningOperationsTest, RsaTooShortMessage)` (L3359)
 *     - `TEST_P(SigningOperationsTest, RsaSignTooLargeMessage)` (L3399)
 *   - `rsa_vts_signing_pkcs1_and_pss_hashes_test`:
 *     - `TEST_P(SigningOperationsTest, RsaAllPaddingsAndDigests)` (L2954)
 *     - `TEST_P(SigningOperationsTest, RsaPssSha256Success)` (L3039)
 *     - `TEST_P(SigningOperationsTest, RsaPkcs1Sha256Success)` (L3104)
 *   - `rsa_vts_encryption_modes_test`:
 *     - `TEST_P(EncryptionOperationsTest, RsaNoPaddingSuccess)` (L5410)
 *     - `TEST_P(EncryptionOperationsTest, RsaNoPaddingShortMessage)` (L5439)
 *     - `TEST_P(EncryptionOperationsTest, RsaOaepSuccess)` (L5463)
 *     - `TEST_P(EncryptionOperationsTest, RsaOaepInvalidDigest)` (L5525)
 *     - `TEST_P(EncryptionOperationsTest, RsaOaepDecryptWithWrongDigest)`
 * (L5561)
 *     - `TEST_P(EncryptionOperationsTest, RsaPkcs1Success)` (L5801)
 *     - `CipherTest.java:956` (`testMaxSizedPlaintextSupported`) & `1036`
 *       (`testLargerThanMaxSizedPlaintextRejected`)
 *   - `rsa_vts_cts_empty_plaintext_and_no_digest_test`:
 *     - `CipherTest.java:398` (`testEmptyPlaintextEncryptsAndDecrypts`)
 *     - `TEST_P(EncryptionOperationsTest, RsaPkcs1Success)` (L5801)
 *     - `TEST_P(SigningOperationsTest, RsaNoDigest)` (L3321, 0-byte message)
 */

enum {
  kRsa2048NumBytes = 2048 / 8,
  kRsa2048NumWords = kRsa2048NumBytes / sizeof(uint32_t),
  kMaxPkcs1v15PayloadBytes = kRsa2048NumBytes - 11,
};

// Test RSA-2048 key pair (e = 65537).
static const uint32_t kTestModulus[kRsa2048NumWords] = {
    0x40d984b1, 0x3611356d, 0x9eb2f35c, 0x031a892c, 0x16354662, 0x6a260bad,
    0xb2b807d6, 0xb7de7ccb, 0x278492e0, 0x41adab06, 0x9e60110f, 0x1414eeff,
    0x8b80e14e, 0x5eb5ae79, 0x0d98fa5b, 0x58bece1f, 0xcf6bdca8, 0x82f5611f,
    0x351e3869, 0x075005d6, 0xe813fe23, 0xdd967a37, 0x682d1c41, 0x9fdd2d8c,
    0x21bdd5fc, 0x4fc459c7, 0x508c9293, 0x1f9ac759, 0x55aacb04, 0x58389f05,
    0x0d0b00fb, 0x59bb4141, 0x68f9e0bf, 0xc2f1a546, 0x0a71ad19, 0x9c400301,
    0xa4f8ecb9, 0xcdf39538, 0xaabe9cb0, 0xd9f7b2dc, 0x0e8b292d, 0x8ef6c717,
    0x720e9520, 0xb0c6a23e, 0xda1e92b1, 0x8b6b4800, 0x2f25082b, 0x7f2d6711,
    0x426fc94f, 0x9926ba5a, 0x89bd4d2b, 0x977718d5, 0x5a8406be, 0x87d090f3,
    0x639f9975, 0x5948488b, 0x1d3d9cd7, 0x28c7956b, 0xebb97a3e, 0x1edbf4e2,
    0x105cc797, 0x924ec514, 0x146810df, 0xb1ab4a49,
};

static const uint32_t kTestPrivateExponent[kRsa2048NumWords] = {
    0x0b19915b, 0xa6a935e6, 0x426b2e10, 0xb4ff0629, 0x7322343b, 0x3f28c8d5,
    0x190757ce, 0x87409d6b, 0xd88e282b, 0x01c13c2a, 0xebb79189, 0x74cbeab9,
    0x93de5d54, 0xae1bc80a, 0x083a75f2, 0xd574d229, 0xeb46696e, 0x7648cfb6,
    0xe7ad1b36, 0xbd0e81b2, 0x19c72703, 0xebea5085, 0xf8c7d152, 0x34dcf84d,
    0xa437187f, 0x41e4f88e, 0xe4e35f9f, 0xcd8bc6f8, 0x7f98e2f2, 0xffdf75ca,
    0x3698226e, 0x903f2a56, 0xbf21a6dc, 0x97cbf653, 0xe9d80cb3, 0x55dc1685,
    0xe0ebae21, 0xc8171e18, 0x8e73d26d, 0xbbdbaac1, 0x886e8007, 0x673c9da4,
    0xe2cb0698, 0xa9f1ba2d, 0xedab4f0a, 0x197e890c, 0x65e7e736, 0x1de28f24,
    0x57cf5137, 0x631ff441, 0x22539942, 0xcee3fd41, 0xd22b5f8a, 0x995dd87a,
    0xcaa6815c, 0x08ca0fd3, 0x8f996093, 0x30b7c446, 0xf69b11f7, 0xa298dd00,
    0xfd4e8120, 0x059df602, 0x25feb268, 0x0f3f749e,
};

static const uint8_t kTestMessage[] = "KeyMint VTS/CTS RSA test message.";
static const size_t kTestMessageLen = sizeof(kTestMessage) - 1;

static const uint8_t kTestLabel[] = "KeyMint OAEP label";
static const size_t kTestLabelLen = sizeof(kTestLabel) - 1;

/**
 * Helper to construct RSA-2048 public and private keys for a given key mode.
 */
static status_t construct_rsa2048_keypair(otcrypto_key_mode_t key_mode,
                                          uint32_t *pub_key_data,
                                          otcrypto_unblinded_key_t *public_key,
                                          uint32_t *priv_keyblob,
                                          otcrypto_blinded_key_t *private_key) {
  otcrypto_const_word32_buf_t modulus = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kTestModulus, ARRAYSIZE(kTestModulus));
  otcrypto_const_word32_buf_t d_share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kTestPrivateExponent,
                        ARRAYSIZE(kTestPrivateExponent));
  uint32_t share1[kRsa2048NumWords] = {0};
  otcrypto_const_word32_buf_t d_share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share1, ARRAYSIZE(share1));

  *public_key = (otcrypto_unblinded_key_t){
      .key_mode = key_mode,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_key_data,
  };
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &modulus,
                                        public_key));

  *private_key = (otcrypto_blinded_key_t){
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = key_mode,
              .key_length = kOtcryptoRsa2048PrivateKeyBytes,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob = priv_keyblob,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
  };
  TRY(otcrypto_rsa_private_key_from_exponents(
      kOtcryptoRsaSize2048, &modulus, &d_share0, &d_share1, private_key));
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:2935` — `TEST_P(SigningOperationsTest, RsaSuccess)`
 *   - `KeyMintTest.cpp:3122` —
 *     `TEST_P(SigningOperationsTest, RsaPkcs1NoDigestSuccess)`
 *   - `KeyMintTest.cpp:3141` —
 *     `TEST_P(SigningOperationsTest, RsaPkcs1NoDigestTooLong)`
 *   - `KeyMintTest.cpp:3321` — `TEST_P(SigningOperationsTest, RsaNoDigest)`
 *   - `KeyMintTest.cpp:3359` —
 *     `TEST_P(SigningOperationsTest, RsaTooShortMessage)`
 *   - `KeyMintTest.cpp:3399` —
 *     `TEST_P(SigningOperationsTest, RsaSignTooLargeMessage)`
 */
static status_t rsa_vts_signing_no_digest_and_raw_test(void) {
  LOG_INFO("Testing SigningOperationsTest.RsaNoDigest (PKCS#1 v1.5 & Raw)");
  uint32_t pub_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes, sizeof(uint32_t))];
  uint32_t priv_blob[ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes,
                              sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key;
  otcrypto_blinded_key_t private_key;

  // 1. PKCS#1 v1.5 Sign/Verify with `kOtcryptoHashModeNull` (unhashed raw
  // message up to k - 11 = 245 bytes; Note: otcrypto_hash_digest_t.len is in
  // 32-bit words, so word-aligned lengths up to 244 bytes are supported).
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaSignPkcs, pub_data,
                                &public_key, priv_blob, &private_key));

  uint32_t raw_digest_words[61];  // 244 bytes (max word-aligned <= 245 bytes)
  for (size_t i = 0; i < ARRAYSIZE(raw_digest_words); ++i) {
    raw_digest_words[i] = 0x10203040u + (uint32_t)i;
  }
  otcrypto_hash_digest_t null_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = raw_digest_words,
      .len = ARRAYSIZE(raw_digest_words),
  };

  uint32_t sig[kRsa2048NumWords];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, ARRAYSIZE(sig));

  TRY(otcrypto_rsa_sign(&private_key, null_digest, kOtcryptoRsaPaddingPkcs,
                        &sig_buf));
  hardened_bool_t verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&public_key, null_digest, kOtcryptoRsaPaddingPkcs,
                          &const_sig_buf, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  // Tamper with the unhashed message and verify PKCS#1 v1.5 verification fails.
  raw_digest_words[0] ^= 1u;
  TRY(otcrypto_rsa_verify(&public_key, null_digest, kOtcryptoRsaPaddingPkcs,
                          &const_sig_buf, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolFalse);
  raw_digest_words[0] ^= 1u;

  // PKCS#1 v1.5 with `kOtcryptoHashModeNull` must reject payloads > 245 bytes
  // (e.g., 62 words = 248 bytes).
  uint32_t too_long_digest_words[62] = {0};
  otcrypto_hash_digest_t too_long_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = too_long_digest_words,
      .len = ARRAYSIZE(too_long_digest_words),
  };
  TRY_CHECK(otcrypto_rsa_sign(&private_key, too_long_digest,
                              kOtcryptoRsaPaddingPkcs, &sig_buf)
                .value == OTCRYPTO_BAD_ARGS.value);

  // 2. Raw RSA (`PaddingMode::NONE` + `Digest::NONE`):
  // KeyMint left-pads short messages with zero bytes (big-endian) = right-pads
  // with zero words in little-endian representation.
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaRaw, pub_data, &public_key,
                                priv_blob, &private_key));
  uint32_t raw_block[kRsa2048NumWords] = {0};
  memcpy(raw_block, kTestMessage, kTestMessageLen);
  otcrypto_hash_digest_t raw_block_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = raw_block,
      .len = ARRAYSIZE(raw_block),
  };
  TRY(otcrypto_rsa_sign(&private_key, raw_block_digest, kOtcryptoRsaPaddingNull,
                        &sig_buf));
  verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&public_key, raw_block_digest,
                          kOtcryptoRsaPaddingNull, &const_sig_buf, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  // Raw RSA must reject input numerically >= modulus.
  uint32_t ge_modulus[kRsa2048NumWords];
  memcpy(ge_modulus, kTestModulus, sizeof(ge_modulus));
  otcrypto_hash_digest_t ge_mod_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = ge_modulus,
      .len = ARRAYSIZE(ge_modulus),
  };
  TRY_CHECK(otcrypto_rsa_sign(&private_key, ge_mod_digest,
                              kOtcryptoRsaPaddingNull, &sig_buf)
                .value == OTCRYPTO_BAD_ARGS.value);

  // KeyMintTest.cpp:3321 (`SigningOperationsTest.RsaNoDigest`):
  // RSA-PSS (`kOtcryptoRsaPaddingPss`) with `Digest::NONE`
  // (`kOtcryptoHashModeNull`) must fail with `OTCRYPTO_BAD_ARGS`.
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaSignPss, pub_data,
                                &public_key, priv_blob, &private_key));
  TRY_CHECK(otcrypto_rsa_sign(&private_key, null_digest, kOtcryptoRsaPaddingPss,
                              &sig_buf)
                .value == OTCRYPTO_BAD_ARGS.value);

  return OK_STATUS();
}

/**
 * SigningOperationsTest.RsaAllPaddingsAndDigests, RsaPkcs1Sha256Success, &
 * RsaPssSha256Success (`KeyMintTest.cpp:2954-3115`).
 *
 * Tests both PKCS#1 v1.5 and PSS across SHA-1, SHA-256, SHA-384, and SHA-512,
 * plus corrupted signature rejection (`++corrupt[64]`).
 */
static status_t rsa_vts_signing_pkcs1_and_pss_hashes_test(void) {
  LOG_INFO(
      "Testing SigningOperationsTest.RsaAllPaddingsAndDigests "
      "(PKCS#1 v1.5 & PSS across SHA-1/256/384/512)");
  uint32_t pub_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes, sizeof(uint32_t))];
  uint32_t priv_blob[ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes,
                              sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key;
  otcrypto_blinded_key_t private_key;

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kTestMessage, kTestMessageLen);
  uint32_t sha1_words[160 / 32];
  otcrypto_hash_digest_t sha1_digest = {
      .mode = kOtcryptoHashModeSha1,
      .data = sha1_words,
      .len = ARRAYSIZE(sha1_words),
  };
  TRY(otcrypto_sha1(&msg_buf, &sha1_digest));

  uint32_t sha256_words[256 / 32];
  otcrypto_hash_digest_t sha256_digest = {
      .mode = kOtcryptoHashModeSha256,
      .data = sha256_words,
      .len = ARRAYSIZE(sha256_words),
  };
  TRY(otcrypto_sha2_256(&msg_buf, &sha256_digest));

  uint32_t sha384_words[384 / 32];
  otcrypto_hash_digest_t sha384_digest = {
      .mode = kOtcryptoHashModeSha384,
      .data = sha384_words,
      .len = ARRAYSIZE(sha384_words),
  };
  TRY(otcrypto_sha2_384(&msg_buf, &sha384_digest));

  uint32_t sha512_words[512 / 32];
  otcrypto_hash_digest_t sha512_digest = {
      .mode = kOtcryptoHashModeSha512,
      .data = sha512_words,
      .len = ARRAYSIZE(sha512_words),
  };
  TRY(otcrypto_sha2_512(&msg_buf, &sha512_digest));

  const otcrypto_hash_digest_t kDigests[4] = {sha1_digest, sha256_digest,
                                              sha384_digest, sha512_digest};
  const otcrypto_rsa_padding_t kPaddings[2] = {kOtcryptoRsaPaddingPkcs,
                                               kOtcryptoRsaPaddingPss};
  const otcrypto_key_mode_t kKeyModes[2] = {kOtcryptoKeyModeRsaSignPkcs,
                                            kOtcryptoKeyModeRsaSignPss};

  for (size_t p = 0; p < ARRAYSIZE(kPaddings); ++p) {
    TRY(construct_rsa2048_keypair(kKeyModes[p], pub_data, &public_key,
                                  priv_blob, &private_key));
    for (size_t d = 0; d < ARRAYSIZE(kDigests); ++d) {
      uint32_t sig[kRsa2048NumWords];
      otcrypto_word32_buf_t sig_buf =
          OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
      otcrypto_const_word32_buf_t const_sig_buf =
          OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, ARRAYSIZE(sig));

      TRY(otcrypto_rsa_sign(&private_key, kDigests[d], kPaddings[p], &sig_buf));
      hardened_bool_t verif_ok = kHardenedBoolFalse;
      TRY(otcrypto_rsa_verify(&public_key, kDigests[d], kPaddings[p],
                              &const_sig_buf, &verif_ok));
      TRY_CHECK(verif_ok == kHardenedBoolTrue);

      // KeyMintTest.cpp:2998: Corrupt middle word of signature and verify
      // verification fails (`verif_ok == kHardenedBoolFalse`).
      sig[kRsa2048NumWords / 2] ^= 1u;
      verif_ok = kHardenedBoolTrue;
      TRY(otcrypto_rsa_verify(&public_key, kDigests[d], kPaddings[p],
                              &const_sig_buf, &verif_ok));
      TRY_CHECK(verif_ok == kHardenedBoolFalse);
    }
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:5410` —
 *     `TEST_P(EncryptionOperationsTest, RsaNoPaddingSuccess)`
 *   - `KeyMintTest.cpp:5439` —
 *     `TEST_P(EncryptionOperationsTest, RsaNoPaddingShortMessage)`
 *   - `KeyMintTest.cpp:5463` —
 *     `TEST_P(EncryptionOperationsTest, RsaOaepSuccess)`
 *   - `KeyMintTest.cpp:5525` —
 *     `TEST_P(EncryptionOperationsTest, RsaOaepInvalidDigest)`
 *   - `KeyMintTest.cpp:5561` —
 *     `TEST_P(EncryptionOperationsTest, RsaOaepDecryptWithWrongDigest)`
 *   - `KeyMintTest.cpp:5801` —
 *     `TEST_P(EncryptionOperationsTest, RsaPkcs1Success)`
 */
static status_t rsa_vts_encryption_modes_test(void) {
  LOG_INFO(
      "Testing EncryptionOperationsTest.RsaNoPadding*, RsaPkcs1*, RsaOaep*");
  uint32_t pub_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes, sizeof(uint32_t))];
  uint32_t priv_blob[ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes,
                              sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key;
  otcrypto_blinded_key_t private_key;

  uint32_t ciphertext[kRsa2048NumWords];
  otcrypto_word32_buf_t ct_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, ciphertext, ARRAYSIZE(ciphertext));
  otcrypto_const_word32_buf_t const_ct_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, ciphertext, ARRAYSIZE(ciphertext));
  otcrypto_const_byte_buf_t empty_label =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  otcrypto_const_byte_buf_t label_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kTestLabel, kTestLabelLen);

  uint8_t decrypted[kRsa2048NumBytes];
  size_t decrypted_len = 0;

  // 1. PKCS#1 v1.5 Encryption (`kOtcryptoKeyModeRsaEncryptPkcs`):
  // Test max message length (245B) and rejection of 246B.
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaEncryptPkcs, pub_data,
                                &public_key, priv_blob, &private_key));
  uint8_t max_pkcs_msg[kMaxPkcs1v15PayloadBytes];
  for (size_t i = 0; i < sizeof(max_pkcs_msg); ++i) {
    max_pkcs_msg[i] = (uint8_t)(i ^ 0xa5);
  }
  otcrypto_const_byte_buf_t max_pkcs_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, max_pkcs_msg, sizeof(max_pkcs_msg));
  otcrypto_byte_buf_t pkcs_pt_out = OTCRYPTO_MAKE_BUF(
      otcrypto_byte_buf_t, decrypted, kMaxPkcs1v15PayloadBytes);

  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &max_pkcs_in,
                           &empty_label, &ct_buf));
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull, &const_ct_buf,
                           &empty_label, &pkcs_pt_out, &decrypted_len));
  TRY_CHECK(decrypted_len == sizeof(max_pkcs_msg));
  TRY_CHECK_ARRAYS_EQ(decrypted, max_pkcs_msg, decrypted_len);

  uint8_t too_long_pkcs[kMaxPkcs1v15PayloadBytes + 1] = {0};
  otcrypto_const_byte_buf_t too_long_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, too_long_pkcs, sizeof(too_long_pkcs));
  TRY_CHECK(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull,
                                 &too_long_in, &empty_label, &ct_buf)
                .value == OTCRYPTO_BAD_ARGS.value);

  // 2. Raw RSA Encryption (`kOtcryptoKeyModeRsaRaw`):
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaRaw, pub_data, &public_key,
                                priv_blob, &private_key));
  uint8_t raw_pt[kRsa2048NumBytes] = {0};
  memcpy(raw_pt, kTestMessage, kTestMessageLen);
  otcrypto_const_byte_buf_t raw_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, raw_pt, sizeof(raw_pt));
  otcrypto_byte_buf_t raw_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, sizeof(decrypted));

  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &raw_in,
                           &empty_label, &ct_buf));
  decrypted_len = 0;
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull, &const_ct_buf,
                           &empty_label, &raw_out, &decrypted_len));
  TRY_CHECK(decrypted_len == kRsa2048NumBytes);
  TRY_CHECK_ARRAYS_EQ(decrypted, raw_pt, kRsa2048NumBytes);

  // 3. RSA-OAEP with SHA-1, SHA-256, SHA-384, and SHA-512 (with label and
  // wrong-label failure):
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaEncryptOaep, pub_data,
                                &public_key, priv_blob, &private_key));
  otcrypto_const_byte_buf_t msg_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kTestMessage, kTestMessageLen);
  const otcrypto_hash_mode_t kOaepHashes[4] = {
      kOtcryptoHashModeSha1, kOtcryptoHashModeSha256, kOtcryptoHashModeSha384,
      kOtcryptoHashModeSha512};

  for (size_t h = 0; h < ARRAYSIZE(kOaepHashes); ++h) {
    TRY(otcrypto_rsa_encrypt(&public_key, kOaepHashes[h], &msg_in, &label_buf,
                             &ct_buf));
    decrypted_len = 0;
    TRY(otcrypto_rsa_decrypt(&private_key, kOaepHashes[h], &const_ct_buf,
                             &label_buf, &raw_out, &decrypted_len));
    TRY_CHECK(decrypted_len == kTestMessageLen);
    TRY_CHECK_ARRAYS_EQ(decrypted, kTestMessage, kTestMessageLen);

    // Decrypting with a mismatched OAEP label must fail.
    TRY_CHECK(otcrypto_rsa_decrypt(&private_key, kOaepHashes[h], &const_ct_buf,
                                   &empty_label, &raw_out, &decrypted_len)
                  .value == OTCRYPTO_BAD_ARGS.value);
  }

  // KeyMintTest.cpp:5497 (`RsaOaepSuccess`), 5525 (`RsaOaepInvalidDigest`),
  // & 5561 (`RsaOaepDecryptWithWrongDigest`):
  // - OAEP encryption is randomized (`ciphertext1 != ciphertext2`).
  uint32_t ciphertext2[kRsa2048NumWords];
  otcrypto_word32_buf_t ct2_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, ciphertext2, ARRAYSIZE(ciphertext2));
  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeSha1, &msg_in,
                           &empty_label, &ct_buf));
  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeSha1, &msg_in,
                           &empty_label, &ct2_buf));
  TRY_CHECK(memcmp(ciphertext, ciphertext2, sizeof(ciphertext)) != 0);

  // - `RsaOaepInvalidDigest`: OAEP with `Digest::NONE`
  // (`kOtcryptoHashModeNull`)
  //   fails with `OTCRYPTO_BAD_ARGS`.
  TRY_CHECK(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &msg_in,
                                 &empty_label, &ct_buf)
                .value == OTCRYPTO_BAD_ARGS.value);

  // - `RsaOaepDecryptWithWrongDigest`: Encrypt with SHA-1 (`ct_buf`), decrypt
  //   with SHA-256 fails with `OTCRYPTO_BAD_ARGS`.
  TRY_CHECK(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeSha256,
                                 &const_ct_buf, &empty_label, &raw_out,
                                 &decrypted_len)
                .value == OTCRYPTO_BAD_ARGS.value);

  return OK_STATUS();
}

/**
 * Source:
 *   - `CipherTest.java:398` — `testEmptyPlaintextEncryptsAndDecrypts`
 *   - `KeyMintTest.cpp:5801` —
 *     `TEST_P(EncryptionOperationsTest, RsaPkcs1Success)` (0-byte message
 *     encryption/decryption and caller buffer sizing)
 *   - `KeyMintTest.cpp:3321` — `TEST_P(SigningOperationsTest, RsaNoDigest)`
 *     (0-byte message signing/verification)
 */
static status_t rsa_vts_cts_empty_plaintext_and_no_digest_test(void) {
  LOG_INFO(
      "Testing Android CTS testEmptyPlaintextEncryptsAndDecrypts & KeyMint VTS "
      "RsaNoDigest (0-byte message)");

  uint32_t pub_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes, sizeof(uint32_t))];
  uint32_t priv_blob[ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes,
                              sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key;
  otcrypto_blinded_key_t private_key;

  uint32_t sig[kRsa2048NumWords];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, ARRAYSIZE(sig));

  // 1. `CipherTest.java:398` (`testEmptyPlaintextEncryptsAndDecrypts`) &
  // `KeyMintTest.cpp:5801` (`RsaPkcs1Success`): 0-byte PKCS#1 v1.5
  // encryption/decryption round-trip:
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaEncryptPkcs, pub_data,
                                &public_key, priv_blob, &private_key));
  otcrypto_const_byte_buf_t empty_pt =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  otcrypto_const_byte_buf_t empty_label =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &empty_pt,
                           &empty_label, &sig_buf));

  uint8_t decrypted[kRsa2048NumBytes];
  size_t decrypted_len = 999;
  otcrypto_byte_buf_t max_pkcs_out = OTCRYPTO_MAKE_BUF(
      otcrypto_byte_buf_t, decrypted, kMaxPkcs1v15PayloadBytes);
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull, &const_sig_buf,
                           &empty_label, &max_pkcs_out, &decrypted_len));
  TRY_CHECK(decrypted_len == 0);

  // 2. Decrypting a 0-byte PKCS#1 v1.5 plaintext into a 64-byte output buffer
  // should succeed (`OTCRYPTO_OK` with `decrypted_len == 0`; currently fails
  // in `rsa_decrypt_finalize` (`rsa_encryption.c:127-137`) because it requires
  // `plaintext_max_bytelen >= k - 11` before inspecting the padding).
  otcrypto_byte_buf_t small_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, 64);
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull, &const_sig_buf,
                           &empty_label, &small_out, &decrypted_len));
  TRY_CHECK(decrypted_len == 0);

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:3321` — `TEST_P(SigningOperationsTest, RsaNoDigest)`
 *     (0-byte message signing and verification with `RSA_PKCS1_1_5_SIGN` +
 *     `Digest::NONE`)
 */
static status_t rsa_vts_signing_zero_length_no_digest_test(void) {
  LOG_INFO(
      "Testing KeyMint VTS SigningOperationsTest.RsaNoDigest (0-byte message)");

  uint32_t pub_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes, sizeof(uint32_t))];
  uint32_t priv_blob[ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes,
                              sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key;
  otcrypto_blinded_key_t private_key;

  uint32_t sig[kRsa2048NumWords];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, ARRAYSIZE(sig));

  // KeyMint VTS `SigningOperationsTest.RsaNoDigest` (`KeyMintTest.cpp:3321`)
  // 0-byte message: `otcrypto_rsa_sign` and `otcrypto_rsa_verify` with
  // `kOtcryptoRsaPaddingPkcs` + `kOtcryptoHashModeNull` and `len = 0` should
  // succeed (`OTCRYPTO_OK`; currently fails in `digest_check` at
  // `rsa_signature.c:45` and `digest_info_length_get` at `rsa_padding.c:35`).
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaSignPkcs, pub_data,
                                &public_key, priv_blob, &private_key));
  uint32_t dummy_word = 0;
  otcrypto_hash_digest_t empty_raw_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = &dummy_word,
      .len = 0,
  };
  TRY(otcrypto_rsa_sign(&private_key, empty_raw_digest, kOtcryptoRsaPaddingPkcs,
                        &sig_buf));
  hardened_bool_t verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&public_key, empty_raw_digest,
                          kOtcryptoRsaPaddingPkcs, &const_sig_buf, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));

  EXECUTE_TEST(result, rsa_vts_signing_no_digest_and_raw_test);
  EXECUTE_TEST(result, rsa_vts_signing_pkcs1_and_pss_hashes_test);
  EXECUTE_TEST(result, rsa_vts_encryption_modes_test);
  EXECUTE_TEST(result, rsa_vts_cts_empty_plaintext_and_no_digest_test);
  EXECUTE_TEST(result, rsa_vts_signing_zero_length_no_digest_test);

  return status_ok(result);
}
