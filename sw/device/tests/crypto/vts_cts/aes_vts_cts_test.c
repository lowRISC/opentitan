// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

/**
 * Android KeyMint VTS (`EncryptionOperationsTest.Aes*`) and Android CTS
 * (`StrongboxAES*CipherTest`, including `testDecryptWithMangledPadding`)
 * conformance test suite for `otcrypto_aes`.
 *
 * Upstream AOSP References:
 *   - `hardware/interfaces/security/keymint/aidl/vts/functional/`
 *     - `KeyMintTest.cpp` (lines 5877-6869)
 *   - `cts/tests/tests/keystore/src/android/keystore/cts/`
 *     - `CipherTest.java`
 *     - `BlockCipherTestBase.java`
 *
 * Test Mapping:
 *   - `aes_ecb_round_trip_success_test`:
 *     - `TEST_P(EncryptionOperationsTest, AesEcbRoundTripSuccess)` (L5877)
 *   - `aes_ecb_cbc_pkcs7_padding_test`:
 *     - `TEST_P(EncryptionOperationsTest, AesEcbPkcs7Padding)` (L6087)
 *     - `BlockCipherTestBase.java:1118` (`testGeneratedPadding`)
 *   - `aes_ecb_cbc_no_padding_wrong_input_size_test`:
 *     - `KeyMintTest.cpp:6060` (`AesEcbCbcNoPaddingWrongInputSize`)
 *   - `aes_wrong_padding_test`:
 *     - `TEST_P(EncryptionOperationsTest, AesWrongPadding)` (L5968, L6114)
 *   - `aes_pkcs7_padding_corrupted_and_mangled_test`:
 *     - `TEST_P(EncryptionOperationsTest, AesEcbPkcs7PaddingCorrupted)` (L6135)
 *     - `TEST_P(EncryptionOperationsTest, AesCbcPkcs7PaddingCorrupted)` (L6869)
 *     - `BlockCipherTestBase.java:1176` (`testDecryptWithMangledPadding`)
 *     - `BlockCipherTestBase.java:1202` (`testDecryptWithMissingPadding`)
 *   - `aes_pkcs7_ciphertext_too_short_test`:
 *     - `KeyMintTest.cpp:6172` (`AesEcbPkcs7CiphertextTooShort`)
 *   - `aes_ctr_round_trip_and_sp800_38a_test`:
 *     - `TEST_P(EncryptionOperationsTest, AesCtrRoundTripSuccess)` (L6204)
 *     - `TEST_P(EncryptionOperationsTest, AesCtrSp80038aTestVector)` (L6648)
 *     - `TEST_P(EncryptionOperationsTest, AesCtrInvalidCallerNonce)` (L6683)
 *   - `aes_cbc_round_trip_test`:
 *     - `TEST_P(EncryptionOperationsTest, AesCbcRoundTripSuccess)` (L6715)
 *     - `TEST_P(EncryptionOperationsTest, AesCallerNonce)` (L6792)
 *     - `TEST_P(EncryptionOperationsTest, AesInvalidCallerNonce)` (L6834)
 *   - `aes_cts_kat_vectors_and_vts_incremental_test`:
 *     - `CipherTest.java:167-182` (`KAT_VECTORS` for `AES/ECB/NoPadding`,
 *       `AES/ECB/PKCS7Padding`, `AES/CBC/NoPadding`, `AES/CBC/PKCS7Padding`)
 *     - `KeyMintTest.cpp:6286-6585` (`Aes{128,256}{CBC,ECB}*OneByteAtATime`)
 *     - `TEST_P(EncryptionOperationsTest, AesEcbIncremental)` (L6251)
 *     - `TEST_P(EncryptionOperationsTest, AesCbcIncremental)` (L6260)
 *     - `TEST_P(EncryptionOperationsTest, AesCtrIncremental)` (L6269)
 *   - `aes_empty_plaintext_no_padding_test`:
 *     - `TEST_P(EncryptionOperationsTest, AesCbcZeroInputSuccess)` (L6749)
 *     - `CipherTest.java:398` (`testEmptyPlaintextEncryptsAndDecrypts`)
 *   - `aes_ctr_unaligned_kat_vectors_test`:
 *     - `CipherTest.java:183-186` (`KAT_VECTORS["AES/CTR/NoPadding"]`)
 *     - `KeyMintTest.cpp:6318` & `AES128CTRNoPaddingCipherTest.java:21-31`
 *       (`Aes128CTRNoPaddingOneByteAtATime`)
 *     - `KeyMintTest.cpp:6526` & `AES256CTRNoPaddingCipherTest.java:21-31`
 *       (`Aes256CTRNoPaddingOneByteAtATime`)
 */

enum {
  kAesBlockBytes = 16,
  kAesBlockWords = kAesBlockBytes / sizeof(uint32_t),
  kAesKey128Bytes = 16,
  kAesKey256Bytes = 32,
  kAesMaxKeyWords = kAesKey256Bytes / sizeof(uint32_t),
};

static const uint32_t kKeyMask[kAesMaxKeyWords] = {
    0x1b81540c, 0x220733c9, 0xbf8b380d, 0x05850b42,
    0x3370c9a2, 0x8922d979, 0x1663b2a7, 0xc3b2a580,
};

static const uint32_t kTestKeys[2][kAesMaxKeyWords] = {
    {
        0x16157e2b,
        0xa6d2ae28,
        0x8815f7ab,
        0x3c4fcf09,
        0x00000000,
        0x00000000,
        0x00000000,
        0x00000000,
    },
    {
        0x16157e2b,
        0xa6d2ae28,
        0x8815f7ab,
        0x3c4fcf09,
        0x1f352c07,
        0x3b6108d7,
        0x2d9810a3,
        0x0914dff4,
    },
};

static const size_t kKeySizes[2] = {kAesKey128Bytes, kAesKey256Bytes};

static const uint32_t kDefaultIv[kAesBlockWords] = {
    0x03020100,
    0x07060504,
    0x0b0a0908,
    0x0f0e0d0c,
};

// NIST SP 800-38A Section F.5 CTR test vectors.
static const uint8_t kSp80038aPlaintext[64] = {
    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e,
    0x11, 0x73, 0x93, 0x17, 0x2a, 0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03,
    0xac, 0x9c, 0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51, 0x30,
    0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11, 0xe5, 0xfb, 0xc1, 0x19,
    0x1a, 0x0a, 0x52, 0xef, 0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f, 0x9b,
    0x17, 0xad, 0x2b, 0x41, 0x7b, 0xe6, 0x6c, 0x37, 0x10,
};

static const uint32_t kSp80038aInitCounter[kAesBlockWords] = {
    0xf3f2f1f0,
    0xf7f6f5f4,
    0xfbfaf9f8,
    0xfffefdfc,
};

// F.5.1 CTR-AES128
static const uint32_t kSp80038aCtr128Key[4] = {
    0x16157e2b,
    0xa6d2ae28,
    0x8815f7ab,
    0x3c4fcf09,
};
static const uint8_t kSp80038aCtr128Ciphertext[64] = {
    0x87, 0x4d, 0x61, 0x91, 0xb6, 0x20, 0xe3, 0x26, 0x1b, 0xef, 0x68,
    0x64, 0x99, 0x0d, 0xb6, 0xce, 0x98, 0x06, 0xf6, 0x6b, 0x79, 0x70,
    0xfd, 0xff, 0x86, 0x17, 0x18, 0x7b, 0xb9, 0xff, 0xfd, 0xff, 0x5a,
    0xe4, 0xdf, 0x3e, 0xdb, 0xd5, 0xd3, 0x5e, 0x5b, 0x4f, 0x09, 0x02,
    0x0d, 0xb0, 0x3e, 0xab, 0x1e, 0x03, 0x1d, 0xda, 0x2f, 0xbe, 0x03,
    0xd1, 0x79, 0x21, 0x70, 0xa0, 0xf3, 0x00, 0x9c, 0xee,
};

// F.5.5 CTR-AES256
static const uint32_t kSp80038aCtr256Key[8] = {
    0x10eb3d60, 0xbe71ca15, 0xf0ae732b, 0x81777d85,
    0x072c351f, 0xd708613b, 0xa310982d, 0xf4df1409,
};
static const uint8_t kSp80038aCtr256Ciphertext[64] = {
    0x60, 0x1e, 0xc3, 0x13, 0x77, 0x57, 0x89, 0xa5, 0xb7, 0xa7, 0xf5,
    0x04, 0xbb, 0xf3, 0xd2, 0x28, 0xf4, 0x43, 0xe3, 0xca, 0x4d, 0x62,
    0xb5, 0x9a, 0xca, 0x84, 0xe9, 0x90, 0xca, 0xca, 0xf5, 0xc5, 0x2b,
    0x09, 0x30, 0xda, 0xa2, 0x3d, 0xe9, 0x4c, 0xe8, 0x70, 0x17, 0xba,
    0x2d, 0x84, 0x98, 0x8d, 0xdf, 0xc9, 0xc5, 0x8d, 0xb6, 0x7a, 0xad,
    0xa6, 0x13, 0xc2, 0xdd, 0x08, 0x45, 0x79, 0x41, 0xa6,
};

/**
 * Helper to build a blinded AES key.
 */
static void build_aes_key(const uint32_t *raw_key, size_t key_len,
                          otcrypto_key_mode_t key_mode, uint32_t *keyblob,
                          size_t keyblob_words, otcrypto_blinded_key_t *key) {
  size_t key_words = key_len / sizeof(uint32_t);
  for (size_t i = 0; i < key_words; ++i) {
    keyblob[i] = raw_key[i] ^ kKeyMask[i];
    keyblob[key_words + i] = kKeyMask[i];
  }
  key->config = (otcrypto_key_config_t){
      .version = otcrypto_lib_version(),
      .key_mode = key_mode,
      .key_length = key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  key->keyblob_length = keyblob_words * sizeof(uint32_t);
  key->keyblob = keyblob;
  key->checksum = otcrypto_integrity_blinded_checksum(key);
}

/**
 * Helper to encrypt with PKCS#7 padding, then decrypt and
 * strip padding via `otcrypto_aes_padding_strip`.
 */
static status_t run_aes_padded_roundtrip(otcrypto_blinded_key_t *key,
                                         otcrypto_aes_mode_t cipher_mode,
                                         otcrypto_aes_padding_t padding_mode,
                                         const uint32_t *initial_iv,
                                         const uint8_t *message,
                                         size_t message_len) {
  size_t padded_len = 0;
  TRY(otcrypto_aes_padded_plaintext_length(message_len, padding_mode,
                                           &padded_len));
  size_t expected_padded_len =
      message_len + kAesBlockBytes - (message_len % kAesBlockBytes);
  TRY_CHECK(padded_len == expected_padded_len);

  uint8_t ciphertext[80];
  uint8_t decrypted[80];
  TRY_CHECK(padded_len <= sizeof(ciphertext));

  uint32_t iv_words[kAesBlockWords];
  memcpy(iv_words, initial_iv, sizeof(iv_words));
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

  otcrypto_const_byte_buf_t pt_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, message, message_len);
  otcrypto_byte_buf_t ct_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, padded_len);

  TRY(otcrypto_aes(key, &iv, cipher_mode, kOtcryptoAesOperationEncrypt, &pt_in,
                   padding_mode, &ct_out));

  // Reset IV for decryption. `otcrypto_aes` accepts `padding_mode` on decrypt
  // and returns the full padded block(s), which the caller strips via
  // `otcrypto_aes_padding_strip`.
  memcpy(iv_words, initial_iv, sizeof(iv_words));
  otcrypto_const_byte_buf_t ct_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, ciphertext, padded_len);
  otcrypto_byte_buf_t pt_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, padded_len);
  TRY(otcrypto_aes(key, &iv, cipher_mode, kOtcryptoAesOperationDecrypt, &ct_in,
                   padding_mode, &pt_out));

  size_t unpadded_len = 0;
  otcrypto_byte_buf_t padded_pt =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, padded_len);
  TRY(otcrypto_aes_padding_strip(&padded_pt, padding_mode, &unpadded_len));
  TRY_CHECK(unpadded_len == message_len);
  if (message_len > 0) {
    TRY_CHECK_ARRAYS_EQ(decrypted, message, message_len);
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:5877` —
 *     `TEST_P(EncryptionOperationsTest, AesEcbRoundTripSuccess)`
 *
 * Verifies AES-ECB round-trip encryption and decryption across AES-128 and
 * AES-256 keys (deterministic `ct1 == ct2`, one-shot and block-by-block).
 */
static status_t aes_ecb_round_trip_success_test(void) {
  LOG_INFO("Testing AesEcbRoundTripSuccess");
  const uint8_t kMessage[64] =
      "1234567890123456789012345678901234567890123456789012345678901234";
  uint8_t ciphertext[sizeof(kMessage)];
  uint8_t decrypted[sizeof(kMessage)];

  for (size_t k = 0; k < ARRAYSIZE(kKeySizes); ++k) {
    uint32_t keyblob[2 * kAesMaxKeyWords];
    otcrypto_blinded_key_t key;
    build_aes_key(kTestKeys[k], kKeySizes[k], kOtcryptoKeyModeAesEcb, keyblob,
                  2 * (kKeySizes[k] / sizeof(uint32_t)), &key);

    uint32_t iv_words[kAesBlockWords] = {0};
    otcrypto_word32_buf_t iv =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

    otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, kMessage, sizeof(kMessage));
    otcrypto_byte_buf_t ct_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, sizeof(ciphertext));
    TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeEcb,
                     kOtcryptoAesOperationEncrypt, &pt_in,
                     kOtcryptoAesPaddingNull, &ct_out));

    // KeyMintTest.cpp:5894 (`AesEcbRoundTripSuccess`): ECB encryption is
    // deterministic (`ciphertext1 == ciphertext2`).
    uint8_t ciphertext2[sizeof(kMessage)];
    otcrypto_byte_buf_t ct_out2 = OTCRYPTO_MAKE_BUF(
        otcrypto_byte_buf_t, ciphertext2, sizeof(ciphertext2));
    TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeEcb,
                     kOtcryptoAesOperationEncrypt, &pt_in,
                     kOtcryptoAesPaddingNull, &ct_out2));
    TRY_CHECK_ARRAYS_EQ(ciphertext, ciphertext2, sizeof(ciphertext));

    // Decrypt in 16-byte block chunks and verify it matches one-shot encrypt.
    for (size_t offset = 0; offset < sizeof(kMessage);
         offset += kAesBlockBytes) {
      otcrypto_const_byte_buf_t block_ct = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, ciphertext + offset, kAesBlockBytes);
      otcrypto_byte_buf_t block_pt = OTCRYPTO_MAKE_BUF(
          otcrypto_byte_buf_t, decrypted + offset, kAesBlockBytes);
      TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeEcb,
                       kOtcryptoAesOperationDecrypt, &block_ct,
                       kOtcryptoAesPaddingNull, &block_pt));
    }
    TRY_CHECK_ARRAYS_EQ(decrypted, kMessage, sizeof(kMessage));
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:6087` —
 *     `TEST_P(EncryptionOperationsTest, AesEcbPkcs7Padding)`
 *   - `KeyMintTest.cpp:6863` —
 *     `TEST_P(EncryptionOperationsTest, AesCbcPkcs7Padding)`
 *
 * Verifies that AES PKCS#7 padding works for any message length from 0 to 48
 * bytes (`ciphertext.size() == i + 16 - (i % 16)`, including 0-byte plaintext
 * -> 16-byte pad block) in both ECB and CBC modes across AES-128 and AES-256.
 */
static status_t aes_ecb_cbc_pkcs7_padding_test(void) {
  LOG_INFO("Testing AesEcbPkcs7Padding & AesCbcPkcs7Padding (0..48 bytes)");
  uint8_t message[48];
  for (size_t i = 0; i < sizeof(message); ++i) {
    message[i] = (uint8_t)(i ^ 0x3c);
  }

  for (size_t k = 0; k < ARRAYSIZE(kKeySizes); ++k) {
    uint32_t keyblob[2 * kAesMaxKeyWords];
    otcrypto_blinded_key_t key;

    // 1. ECB + PKCS#7 for all lengths 0..48.
    build_aes_key(kTestKeys[k], kKeySizes[k], kOtcryptoKeyModeAesEcb, keyblob,
                  2 * (kKeySizes[k] / sizeof(uint32_t)), &key);
    for (size_t len = 0; len <= sizeof(message); ++len) {
      TRY(run_aes_padded_roundtrip(&key, kOtcryptoAesModeEcb,
                                   kOtcryptoAesPaddingPkcs7, kDefaultIv,
                                   message, len));
    }

    // 2. CBC + PKCS#7 for all lengths 0..48.
    build_aes_key(kTestKeys[k], kKeySizes[k], kOtcryptoKeyModeAesCbc, keyblob,
                  2 * (kKeySizes[k] / sizeof(uint32_t)), &key);
    for (size_t len = 0; len <= sizeof(message); ++len) {
      TRY(run_aes_padded_roundtrip(&key, kOtcryptoAesModeCbc,
                                   kOtcryptoAesPaddingPkcs7, kDefaultIv,
                                   message, len));
    }
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:6060` —
 *     `TEST_P(EncryptionOperationsTest, AesEcbCbcNoPaddingWrongInputSize)`
 *
 * Verifies that AES encryption fails with `OTCRYPTO_BAD_ARGS` when provided an
 * input (`16 * 2 - 1 = 31` bytes) that is not a multiple of the block size and
 * `kOtcryptoAesPaddingNull` is specified.
 */
static status_t aes_ecb_cbc_no_padding_wrong_input_size_test(void) {
  LOG_INFO("Testing AesEcbCbcNoPaddingWrongInputSize");
  const uint8_t kMessage31B[31] = "1234567890123456789012345678901";
  uint8_t output[32];

  otcrypto_aes_mode_t cipher_modes[2] = {kOtcryptoAesModeEcb,
                                         kOtcryptoAesModeCbc};
  otcrypto_key_mode_t key_modes[2] = {kOtcryptoKeyModeAesEcb,
                                      kOtcryptoKeyModeAesCbc};

  for (size_t m = 0; m < ARRAYSIZE(cipher_modes); ++m) {
    uint32_t keyblob[2 * kAesMaxKeyWords];
    otcrypto_blinded_key_t key;
    build_aes_key(kTestKeys[0], kAesKey128Bytes, key_modes[m], keyblob,
                  2 * (kAesKey128Bytes / sizeof(uint32_t)), &key);

    uint32_t iv_words[kAesBlockWords];
    memcpy(iv_words, kDefaultIv, sizeof(iv_words));
    otcrypto_word32_buf_t iv =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

    otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, kMessage31B, sizeof(kMessage31B));
    otcrypto_byte_buf_t ct_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, output, sizeof(output));

    otcrypto_status_t status =
        otcrypto_aes(&key, &iv, cipher_modes[m], kOtcryptoAesOperationEncrypt,
                     &pt_in, kOtcryptoAesPaddingNull, &ct_out);
    TRY_CHECK(status.value == OTCRYPTO_BAD_ARGS.value);
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:6029` —
 *     `TEST_P(EncryptionOperationsTest, AesEcbWrongPadding)`
 *
 * Verifies that `otcrypto_aes` and `otcrypto_aes_padded_plaintext_length`
 * reject invalid padding mode values with `OTCRYPTO_BAD_ARGS`.
 */
static status_t aes_wrong_padding_test(void) {
  LOG_INFO("Testing AesEcbWrongPadding");
  uint32_t keyblob[2 * kAesMaxKeyWords];
  otcrypto_blinded_key_t key;
  build_aes_key(kTestKeys[0], kAesKey128Bytes, kOtcryptoKeyModeAesEcb, keyblob,
                2 * (kAesKey128Bytes / sizeof(uint32_t)), &key);

  uint8_t message[kAesBlockBytes] = "1234567890123456";
  uint8_t ciphertext[kAesBlockBytes];
  uint32_t iv_words[kAesBlockWords] = {0};
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));
  otcrypto_const_byte_buf_t pt_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, message, sizeof(message));
  otcrypto_byte_buf_t ct_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, sizeof(ciphertext));

  otcrypto_aes_padding_t invalid_padding = (otcrypto_aes_padding_t)0xdeadbeef;
  size_t padded_len = 0;
  TRY_CHECK(otcrypto_aes_padded_plaintext_length(sizeof(message),
                                                 invalid_padding, &padded_len)
                .value == OTCRYPTO_BAD_ARGS.value);
  TRY_CHECK(otcrypto_aes(&key, &iv, kOtcryptoAesModeEcb,
                         kOtcryptoAesOperationEncrypt, &pt_in, invalid_padding,
                         &ct_out)
                .value == OTCRYPTO_BAD_ARGS.value);
  TRY_CHECK(otcrypto_aes(&key, &iv, kOtcryptoAesModeEcb,
                         kOtcryptoAesOperationDecrypt, &pt_in, invalid_padding,
                         &ct_out)
                .value == OTCRYPTO_BAD_ARGS.value);
  TRY_CHECK(
      otcrypto_aes_padding_strip(&ct_out, invalid_padding, &padded_len).value ==
      OTCRYPTO_BAD_ARGS.value);
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:6135` —
 *     `TEST_P(EncryptionOperationsTest, AesEcbPkcs7PaddingCorrupted)`
 *   - `KeyMintTest.cpp:6869` —
 *     `TEST_P(EncryptionOperationsTest, AesCbcPkcs7PaddingCorrupted)`
 *   - Android CTS (`CipherTest.java`):
 *     `StrongboxAES256ECBPKCS7PaddingCipherTest#testDecryptWithMangledPadding`
 *
 * Verifies that:
 * 1. Decrypting corrupted ciphertext fails `otcrypto_aes_padding_strip`.
 * 2. Mangling any PKCS#7 padding byte (pad value 0, pad value > 16, or
 *    inconsistent pad byte in `[16 - pad_len, 15)`) is rejected with
 *    `OTCRYPTO_BAD_ARGS`.
 */
static status_t aes_pkcs7_padding_corrupted_and_mangled_test(void) {
  LOG_INFO("Testing AesEcb/CbcPkcs7PaddingCorrupted & MangledPadding");
  uint32_t keyblob[2 * kAesMaxKeyWords];
  otcrypto_aes_mode_t modes[] = {kOtcryptoAesModeEcb, kOtcryptoAesModeCbc};
  otcrypto_key_mode_t key_modes[] = {kOtcryptoKeyModeAesEcb,
                                     kOtcryptoKeyModeAesCbc};

  const uint8_t kMessage[1] = {'a'};
  uint8_t ciphertext[kAesBlockBytes];
  uint8_t decrypted[kAesBlockBytes];
  uint32_t iv_words[kAesBlockWords] = {0};
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

  // 1. Corrupt ciphertext in both ECB and CBC modes and verify decryption +
  // padding strip fails.
  for (size_t m = 0; m < ARRAYSIZE(modes); ++m) {
    otcrypto_blinded_key_t key;
    build_aes_key(kTestKeys[1], kAesKey256Bytes, key_modes[m], keyblob,
                  2 * (kAesKey256Bytes / sizeof(uint32_t)), &key);

    memset(iv_words, 0, sizeof(iv_words));
    otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, kMessage, sizeof(kMessage));
    otcrypto_byte_buf_t ct_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, sizeof(ciphertext));
    TRY(otcrypto_aes(&key, &iv, modes[m], kOtcryptoAesOperationEncrypt, &pt_in,
                     kOtcryptoAesPaddingPkcs7, &ct_out));

    bool failed_as_expected = false;
    for (size_t i = 0; i < 4; ++i) {
      ciphertext[sizeof(ciphertext) / 2]++;
      memset(iv_words, 0, sizeof(iv_words));
      otcrypto_const_byte_buf_t ct_in = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, ciphertext, sizeof(ciphertext));
      otcrypto_byte_buf_t pt_out =
          OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, sizeof(decrypted));
      TRY(otcrypto_aes(&key, &iv, modes[m], kOtcryptoAesOperationDecrypt,
                       &ct_in, kOtcryptoAesPaddingPkcs7, &pt_out));

      size_t unpadded_len = 0;
      otcrypto_byte_buf_t padded_pt =
          OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, sizeof(decrypted));
      otcrypto_status_t status = otcrypto_aes_padding_strip(
          &padded_pt, kOtcryptoAesPaddingPkcs7, &unpadded_len);
      if (status.value != OTCRYPTO_OK.value) {
        TRY_CHECK(status.value == OTCRYPTO_BAD_ARGS.value);
        failed_as_expected = true;
        break;
      }
    }
    TRY_CHECK(failed_as_expected);
  }

  // 2. Direct PKCS#7 mangled padding verification
  // (`StrongboxAES256ECBPKCS7PaddingCipherTest#testDecryptWithMangledPadding`):
  // Test pad_byte == 0 and pad_byte > 16.
  uint8_t block[kAesBlockBytes];
  size_t unpadded_len = 0;
  otcrypto_byte_buf_t block_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, block, sizeof(block));

  memset(block, 0x00, sizeof(block));
  TRY_CHECK(otcrypto_aes_padding_strip(&block_buf, kOtcryptoAesPaddingPkcs7,
                                       &unpadded_len)
                .value == OTCRYPTO_BAD_ARGS.value);

  for (uint32_t bad_pad = kAesBlockBytes + 1; bad_pad <= 0xff; ++bad_pad) {
    memset(block, (int)bad_pad, sizeof(block));
    TRY_CHECK(otcrypto_aes_padding_strip(&block_buf, kOtcryptoAesPaddingPkcs7,
                                         &unpadded_len)
                  .value == OTCRYPTO_BAD_ARGS.value);
  }

  // Test corrupting each individual byte within valid PKCS#7 padding of length
  // 2..16.
  for (size_t pad_len = 2; pad_len <= kAesBlockBytes; ++pad_len) {
    for (size_t corrupt_idx = kAesBlockBytes - pad_len;
         corrupt_idx < kAesBlockBytes - 1; ++corrupt_idx) {
      memset(block, 'A', kAesBlockBytes - pad_len);
      memset(block + kAesBlockBytes - pad_len, (int)pad_len, pad_len);
      block[corrupt_idx] ^= 0x01;
      TRY_CHECK(otcrypto_aes_padding_strip(&block_buf, kOtcryptoAesPaddingPkcs7,
                                           &unpadded_len)
                    .value == OTCRYPTO_BAD_ARGS.value);
    }
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:6172` —
 *     `TEST_P(EncryptionOperationsTest, AesEcbPkcs7CiphertextTooShort)`
 *
 * Verifies that AES decryption and padding strip reject buffers whose length
 * is 0 or not a multiple of the 16-byte block size (`15` bytes).
 */
static status_t aes_pkcs7_ciphertext_too_short_test(void) {
  LOG_INFO("Testing AesEcbPkcs7CiphertextTooShort");
  uint32_t keyblob[2 * kAesMaxKeyWords];
  otcrypto_blinded_key_t key;
  build_aes_key(kTestKeys[0], kAesKey128Bytes, kOtcryptoKeyModeAesEcb, keyblob,
                2 * (kAesKey128Bytes / sizeof(uint32_t)), &key);

  uint8_t ciphertext[kAesBlockBytes] = {0};
  uint8_t decrypted[kAesBlockBytes] = {0};
  uint32_t iv_words[kAesBlockWords] = {0};
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

  otcrypto_const_byte_buf_t short_ct = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, ciphertext, kAesBlockBytes - 1);
  otcrypto_byte_buf_t short_pt =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, kAesBlockBytes - 1);
  TRY_CHECK(otcrypto_aes(&key, &iv, kOtcryptoAesModeEcb,
                         kOtcryptoAesOperationDecrypt, &short_ct,
                         kOtcryptoAesPaddingNull, &short_pt)
                .value == OTCRYPTO_BAD_ARGS.value);

  size_t unpadded_len = 0;
  TRY_CHECK(otcrypto_aes_padding_strip(&short_pt, kOtcryptoAesPaddingPkcs7,
                                       &unpadded_len)
                .value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_byte_buf_t empty_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, NULL, 0);
  TRY_CHECK(otcrypto_aes_padding_strip(&empty_buf, kOtcryptoAesPaddingPkcs7,
                                       &unpadded_len)
                .value == OTCRYPTO_BAD_ARGS.value);
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:6204` —
 *     `TEST_P(EncryptionOperationsTest, AesCtrRoundTripSuccess)`
 *   - `KeyMintTest.cpp:6606-6661` —
 *     `TEST_P(EncryptionOperationsTest, AesCtrSp80038aTestVector)`
 *     (NIST SP 800-38A Section F.5.1 AES-128 and F.5.5 AES-256; StrongBox
 *      skips AES-192 per `InvalidKeySizes(Algorithm::AES)`)
 *   - `KeyMintTest.cpp:6683` —
 *     `TEST_P(EncryptionOperationsTest, AesCtrInvalidCallerNonce)`
 */
static status_t aes_ctr_round_trip_and_sp800_38a_test(void) {
  LOG_INFO("Testing AesCtrRoundTripSuccess & AesCtrSp80038aTestVector");
  const struct {
    const uint32_t *key;
    size_t key_len;
    const uint8_t *expected_ct;
  } kVectors[] = {
      {kSp80038aCtr128Key, 16, kSp80038aCtr128Ciphertext},
      {kSp80038aCtr256Key, 32, kSp80038aCtr256Ciphertext},
  };

  uint8_t ciphertext[sizeof(kSp80038aPlaintext)];
  uint8_t decrypted[sizeof(kSp80038aPlaintext)];

  for (size_t v = 0; v < ARRAYSIZE(kVectors); ++v) {
    uint32_t keyblob[2 * kAesMaxKeyWords];
    otcrypto_blinded_key_t key;
    build_aes_key(kVectors[v].key, kVectors[v].key_len, kOtcryptoKeyModeAesCtr,
                  keyblob, 2 * (kVectors[v].key_len / sizeof(uint32_t)), &key);

    // One-shot encrypt.
    uint32_t iv_words[kAesBlockWords];
    memcpy(iv_words, kSp80038aInitCounter, sizeof(iv_words));
    otcrypto_word32_buf_t iv =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

    otcrypto_const_byte_buf_t pt_in =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kSp80038aPlaintext,
                          sizeof(kSp80038aPlaintext));
    otcrypto_byte_buf_t ct_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, sizeof(ciphertext));
    TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeCtr,
                     kOtcryptoAesOperationEncrypt, &pt_in,
                     kOtcryptoAesPaddingNull, &ct_out));
    TRY_CHECK_ARRAYS_EQ(ciphertext, kVectors[v].expected_ct,
                        sizeof(ciphertext));

    // Streaming block-by-block decrypt using `iv` updated in-place by
    // `otcrypto_aes`.
    memcpy(iv_words, kSp80038aInitCounter, sizeof(iv_words));
    for (size_t offset = 0; offset < sizeof(ciphertext);
         offset += kAesBlockBytes) {
      otcrypto_const_byte_buf_t block_ct = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, ciphertext + offset, kAesBlockBytes);
      otcrypto_byte_buf_t block_pt = OTCRYPTO_MAKE_BUF(
          otcrypto_byte_buf_t, decrypted + offset, kAesBlockBytes);
      TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeCtr,
                       kOtcryptoAesOperationDecrypt, &block_ct,
                       kOtcryptoAesPaddingNull, &block_pt));
    }
    TRY_CHECK_ARRAYS_EQ(decrypted, kSp80038aPlaintext,
                        sizeof(kSp80038aPlaintext));
  }

  // KeyMintTest.cpp:6204 (`AesCtrRoundTripSuccess`) & 6683
  // (`AesCtrInvalidCallerNonce`):
  uint32_t ctr_keyblob[2 * kAesMaxKeyWords];
  otcrypto_blinded_key_t ctr_key;
  build_aes_key(kSp80038aCtr128Key, 16, kOtcryptoKeyModeAesCtr, ctr_keyblob, 8,
                &ctr_key);
  uint32_t iv1_words[kAesBlockWords] = {0x11111111, 0x22222222, 0x33333333,
                                        0x44444444};
  uint32_t iv2_words[kAesBlockWords] = {0x55555555, 0x66666666, 0x77777777,
                                        0x88888888};
  otcrypto_word32_buf_t iv1 =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv1_words, ARRAYSIZE(iv1_words));
  otcrypto_word32_buf_t iv2 =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv2_words, ARRAYSIZE(iv2_words));
  const uint8_t kCtrMsg[16] = "1234567890123456";
  uint8_t ctr_ct1[16] = {0};
  uint8_t ctr_ct2[16] = {0};
  uint8_t ctr_dec[16] = {0};
  otcrypto_const_byte_buf_t ctr_pt_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kCtrMsg, sizeof(kCtrMsg));
  otcrypto_byte_buf_t ctr_ct1_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ctr_ct1, sizeof(ctr_ct1));
  otcrypto_byte_buf_t ctr_ct2_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ctr_ct2, sizeof(ctr_ct2));
  TRY(otcrypto_aes(&ctr_key, &iv1, kOtcryptoAesModeCtr,
                   kOtcryptoAesOperationEncrypt, &ctr_pt_in,
                   kOtcryptoAesPaddingNull, &ctr_ct1_out));
  TRY(otcrypto_aes(&ctr_key, &iv2, kOtcryptoAesModeCtr,
                   kOtcryptoAesOperationEncrypt, &ctr_pt_in,
                   kOtcryptoAesPaddingNull, &ctr_ct2_out));
  // Distinct nonces produce distinct ciphertexts (`ciphertext1 !=
  // ciphertext2`).
  TRY_CHECK(memcmp(ctr_ct1, ctr_ct2, sizeof(ctr_ct1)) != 0);

  // Decrypting `ctr_ct1` with wrong nonce (`iv2`) produces `decrypted != pt`.
  uint32_t wrong_iv_words[kAesBlockWords] = {0x55555555, 0x66666666, 0x77777777,
                                             0x88888888};
  otcrypto_word32_buf_t wrong_iv = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, wrong_iv_words, ARRAYSIZE(wrong_iv_words));
  otcrypto_const_byte_buf_t ctr_ct1_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, ctr_ct1, sizeof(ctr_ct1));
  otcrypto_byte_buf_t ctr_dec_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ctr_dec, sizeof(ctr_dec));
  TRY(otcrypto_aes(&ctr_key, &wrong_iv, kOtcryptoAesModeCtr,
                   kOtcryptoAesOperationDecrypt, &ctr_ct1_in,
                   kOtcryptoAesPaddingNull, &ctr_dec_out));
  TRY_CHECK(memcmp(ctr_dec, kCtrMsg, sizeof(kCtrMsg)) != 0);

  // `AesCtrInvalidCallerNonce`: IV length != 4 words (e.g., 3 words) ->
  // `OTCRYPTO_BAD_ARGS`.
  otcrypto_word32_buf_t short_iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv1_words, 3);
  TRY_CHECK(otcrypto_aes(&ctr_key, &short_iv, kOtcryptoAesModeCtr,
                         kOtcryptoAesOperationEncrypt, &ctr_pt_in,
                         kOtcryptoAesPaddingNull, &ctr_ct1_out)
                .value == OTCRYPTO_BAD_ARGS.value);

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:6715` —
 *     `TEST_P(EncryptionOperationsTest, AesCbcRoundTripSuccess)`
 *   - `KeyMintTest.cpp:6792` —
 *     `TEST_P(EncryptionOperationsTest, AesCallerNonce)`
 *   - `KeyMintTest.cpp:6834` —
 *     `TEST_P(EncryptionOperationsTest, AesInvalidCallerNonce)`
 */
static status_t aes_cbc_round_trip_test(void) {
  LOG_INFO(
      "Testing AesCbcRoundTripSuccess, AesCallerNonce & AesInvalidCallerNonce");
  const uint8_t kMessage[64] =
      "1234567890123456789012345678901234567890123456789012345678901234";
  uint8_t ciphertext_oneshot[sizeof(kMessage)];
  uint8_t ciphertext_stream[sizeof(kMessage)];
  uint8_t decrypted[sizeof(kMessage)];

  for (size_t k = 0; k < ARRAYSIZE(kKeySizes); ++k) {
    uint32_t keyblob[2 * kAesMaxKeyWords];
    otcrypto_blinded_key_t key;
    build_aes_key(kTestKeys[k], kKeySizes[k], kOtcryptoKeyModeAesCbc, keyblob,
                  2 * (kKeySizes[k] / sizeof(uint32_t)), &key);

    // One-shot CBC encrypt.
    uint32_t iv_words[kAesBlockWords];
    memcpy(iv_words, kDefaultIv, sizeof(iv_words));
    otcrypto_word32_buf_t iv =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));
    otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, kMessage, sizeof(kMessage));
    otcrypto_byte_buf_t ct_out = OTCRYPTO_MAKE_BUF(
        otcrypto_byte_buf_t, ciphertext_oneshot, sizeof(ciphertext_oneshot));
    TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc,
                     kOtcryptoAesOperationEncrypt, &pt_in,
                     kOtcryptoAesPaddingNull, &ct_out));

    // Block-by-block streaming CBC encrypt (IV is updated in-place).
    memcpy(iv_words, kDefaultIv, sizeof(iv_words));
    for (size_t offset = 0; offset < sizeof(kMessage);
         offset += kAesBlockBytes) {
      otcrypto_const_byte_buf_t block_pt = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, kMessage + offset, kAesBlockBytes);
      otcrypto_byte_buf_t block_ct = OTCRYPTO_MAKE_BUF(
          otcrypto_byte_buf_t, ciphertext_stream + offset, kAesBlockBytes);
      TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc,
                       kOtcryptoAesOperationEncrypt, &block_pt,
                       kOtcryptoAesPaddingNull, &block_ct));
    }
    TRY_CHECK_ARRAYS_EQ(ciphertext_stream, ciphertext_oneshot,
                        sizeof(kMessage));

    // Block-by-block streaming CBC decrypt.
    memcpy(iv_words, kDefaultIv, sizeof(iv_words));
    for (size_t offset = 0; offset < sizeof(kMessage);
         offset += kAesBlockBytes) {
      otcrypto_const_byte_buf_t block_ct =
          OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t,
                            ciphertext_oneshot + offset, kAesBlockBytes);
      otcrypto_byte_buf_t block_pt = OTCRYPTO_MAKE_BUF(
          otcrypto_byte_buf_t, decrypted + offset, kAesBlockBytes);
      TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc,
                       kOtcryptoAesOperationDecrypt, &block_ct,
                       kOtcryptoAesPaddingNull, &block_pt));
    }
    TRY_CHECK_ARRAYS_EQ(decrypted, kMessage, sizeof(kMessage));

    // Zero-length input with PKCS#7 padding produces a single 16-byte padding
    // block.
    TRY(run_aes_padded_roundtrip(&key, kOtcryptoAesModeCbc,
                                 kOtcryptoAesPaddingPkcs7, kDefaultIv, kMessage,
                                 0));

    // KeyMintTest.cpp:6792 (`AesCallerNonce`) & 6834 (`AesInvalidCallerNonce`):
    // Decrypting with wrong caller IV `"aaaaaaaaaaaaaaaa"` produces
    // `decrypted != kMessage`, and invalid IV length (3 words) fails with
    // `OTCRYPTO_BAD_ARGS`.
    uint32_t wrong_cbc_iv_words[kAesBlockWords] = {0x61616161, 0x61616161,
                                                   0x61616161, 0x61616161};
    otcrypto_word32_buf_t wrong_cbc_iv =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, wrong_cbc_iv_words,
                          ARRAYSIZE(wrong_cbc_iv_words));
    otcrypto_const_byte_buf_t ct_oneshot_in =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, ciphertext_oneshot,
                          sizeof(ciphertext_oneshot));
    otcrypto_byte_buf_t dec_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, sizeof(decrypted));
    TRY(otcrypto_aes(&key, &wrong_cbc_iv, kOtcryptoAesModeCbc,
                     kOtcryptoAesOperationDecrypt, &ct_oneshot_in,
                     kOtcryptoAesPaddingNull, &dec_out));
    TRY_CHECK(memcmp(decrypted, kMessage, sizeof(kMessage)) != 0);

    otcrypto_word32_buf_t bad_len_iv =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, 3);
    TRY_CHECK(otcrypto_aes(&key, &bad_len_iv, kOtcryptoAesModeCbc,
                           kOtcryptoAesOperationEncrypt, &pt_in,
                           kOtcryptoAesPaddingNull, &ct_out)
                  .value == OTCRYPTO_BAD_ARGS.value);
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `CipherTest.java:167-182` & `291-292` — `KAT_VECTORS` for
 *     `AES/ECB/NoPadding`, `AES/ECB/PKCS7Padding`, `AES/CBC/NoPadding`, and
 *     `AES/CBC/PKCS7Padding` using `AES128_KAT_KEY_BYTES`
 *   - `KeyMintTest.cpp:6286-6585` & `AES{128,256}*CipherTest.java` —
 *     `Aes{128,256}{CBC,ECB}{NoPadding,PKCS7Padding}OneByteAtATime`
 *   - `KeyMintTest.cpp:6251` —
 *     `TEST_P(EncryptionOperationsTest, AesEcbIncremental)`
 *   - `KeyMintTest.cpp:6260` —
 *     `TEST_P(EncryptionOperationsTest, AesCbcIncremental)`
 *   - `KeyMintTest.cpp:6269` —
 *     `TEST_P(EncryptionOperationsTest, AesCtrIncremental)`
 */
static status_t aes_cts_kat_vectors_and_vts_incremental_test(void) {
  LOG_INFO(
      "Testing Android CTS CipherTest.java KAT_VECTORS and KeyMint VTS "
      "AesEcbIncremental / AesCbcIncremental / AesCtrIncremental");

  // Source: `CipherTest.java:291-292` — `AES128_KAT_KEY_BYTES`
  // ("7d9f11a0da111e9d8bdd14f04648ed91").
  const uint32_t kCtsAes128KatKey[4] = {
      0xa0119f7d,
      0x9d1e11da,
      0xf014dd8b,
      0x91ed4846,
  };

  uint32_t keyblob[2 * kAesMaxKeyWords];
  otcrypto_blinded_key_t key;
  uint32_t iv_words[kAesBlockWords] = {0};
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));
  uint8_t out_buf[64] = {0};
  uint8_t dec_buf[64] = {0};

  // 1. Source: `CipherTest.java:167-169` — `KAT_VECTORS["AES/ECB/NoPadding"]`
  // (32B).
  const uint8_t kCtsAesEcbNoPadPt[32] = {
      0x03, 0x83, 0x91, 0x1b, 0xb1, 0x51, 0x9d, 0x58, 0xe6, 0x65, 0x6f,
      0x3f, 0xd3, 0x56, 0x39, 0xc5, 0x02, 0xdb, 0xeb, 0x21, 0x96, 0xce,
      0xa9, 0x37, 0xfc, 0xa2, 0x72, 0x66, 0x6c, 0xb4, 0xa8, 0x0b,
  };
  const uint8_t kCtsAesEcbNoPadCt[32] = {
      0x65, 0x74, 0xc5, 0x06, 0x52, 0x83, 0xb8, 0x9e, 0x0c, 0x93, 0x00,
      0x19, 0xe4, 0x65, 0x5d, 0x85, 0x16, 0xb9, 0x81, 0x70, 0xdb, 0x65,
      0x16, 0xcd, 0x83, 0xe5, 0x89, 0xbd, 0x9c, 0x5e, 0x5a, 0xdc,
  };
  build_aes_key(kCtsAes128KatKey, 16, kOtcryptoKeyModeAesEcb, keyblob, 8, &key);
  otcrypto_const_byte_buf_t ecb_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kCtsAesEcbNoPadPt, sizeof(kCtsAesEcbNoPadPt));
  otcrypto_byte_buf_t ecb_out = OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, out_buf,
                                                  sizeof(kCtsAesEcbNoPadCt));
  TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeEcb, kOtcryptoAesOperationEncrypt,
                   &ecb_in, kOtcryptoAesPaddingNull, &ecb_out));
  TRY_CHECK_ARRAYS_EQ(out_buf, kCtsAesEcbNoPadCt, sizeof(kCtsAesEcbNoPadCt));

  // 2. Source: `CipherTest.java:170-173` —
  // `KAT_VECTORS["AES/ECB/PKCS7Padding"]` (37B -> 48B).
  const uint8_t kCtsAesEcbPkcs7Pt[37] = {
      0x1a, 0xd3, 0xd7, 0x3a, 0x3c, 0xfa, 0x66, 0xda, 0xc7, 0x8a,
      0x51, 0xa9, 0x5c, 0x2c, 0xb2, 0x12, 0x5e, 0xa7, 0x01, 0xe6,
      0xe9, 0xec, 0xbc, 0xa2, 0x41, 0x5b, 0x43, 0x6f, 0x02, 0x58,
      0xe2, 0xba, 0x74, 0x39, 0xb6, 0x75, 0x45,
  };
  const uint8_t kCtsAesEcbPkcs7Ct[48] = {
      0x92, 0x0f, 0x87, 0x3f, 0x2f, 0x9e, 0x91, 0xba, 0xc4, 0xc9, 0xc9, 0x48,
      0xd6, 0x64, 0x96, 0xa2, 0x1b, 0x8b, 0x26, 0x06, 0x85, 0x04, 0x90, 0xda,
      0xc7, 0xab, 0xec, 0xae, 0x83, 0x31, 0x74, 0x88, 0xee, 0x55, 0x0b, 0x99,
      0x73, 0xac, 0x5c, 0xd1, 0x42, 0xf3, 0x87, 0xd7, 0xd2, 0xa1, 0x27, 0x52,
  };
  otcrypto_const_byte_buf_t ecb_p_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kCtsAesEcbPkcs7Pt, sizeof(kCtsAesEcbPkcs7Pt));
  otcrypto_byte_buf_t ecb_p_out = OTCRYPTO_MAKE_BUF(
      otcrypto_byte_buf_t, out_buf, sizeof(kCtsAesEcbPkcs7Ct));
  TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeEcb, kOtcryptoAesOperationEncrypt,
                   &ecb_p_in, kOtcryptoAesPaddingPkcs7, &ecb_p_out));
  TRY_CHECK_ARRAYS_EQ(out_buf, kCtsAesEcbPkcs7Ct, sizeof(kCtsAesEcbPkcs7Ct));

  // 3. Source: `CipherTest.java:174-177` — `KAT_VECTORS["AES/CBC/NoPadding"]`
  // (32B) encrypted in two 16B chunks using the in-place updated IV.
  const uint8_t kCtsAesCbcNoPadPt[32] = {
      0x1d, 0xff, 0xe2, 0x1c, 0x8f, 0x18, 0x27, 0x6c, 0x3a, 0x39, 0xed,
      0x0c, 0x53, 0xab, 0x25, 0x7b, 0x84, 0xef, 0xce, 0xda, 0xb6, 0x00,
      0x95, 0xc4, 0xca, 0xdd, 0x13, 0x11, 0x43, 0x05, 0x8c, 0xf7,
  };
  const uint8_t kCtsAesCbcNoPadIv[16] = {
      0x10, 0xb3, 0xee, 0xa6, 0xcc, 0x8a, 0x7d, 0x6f,
      0x48, 0x33, 0x7e, 0x9b, 0x69, 0x87, 0xd2, 0x8c,
  };
  const uint8_t kCtsAesCbcNoPadCt[32] = {
      0x47, 0xab, 0x11, 0x5b, 0xfa, 0xdc, 0xa9, 0x1e, 0xae, 0xbe, 0xc7,
      0x3a, 0xb9, 0x42, 0xa0, 0x6f, 0x31, 0x21, 0xfd, 0xd5, 0xaa, 0x55,
      0xd2, 0x23, 0xbd, 0x2c, 0xbc, 0xc3, 0x85, 0x5e, 0x1e, 0xf8,
  };
  build_aes_key(kCtsAes128KatKey, 16, kOtcryptoKeyModeAesCbc, keyblob, 8, &key);
  memcpy(iv_words, kCtsAesCbcNoPadIv, sizeof(iv_words));
  otcrypto_const_byte_buf_t cbc_pt1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kCtsAesCbcNoPadPt, 16);
  otcrypto_byte_buf_t cbc_ct1 =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, out_buf, 16);
  TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc, kOtcryptoAesOperationEncrypt,
                   &cbc_pt1, kOtcryptoAesPaddingNull, &cbc_ct1));
  otcrypto_const_byte_buf_t cbc_pt2 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kCtsAesCbcNoPadPt + 16, 16);
  otcrypto_byte_buf_t cbc_ct2 =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, out_buf + 16, 16);
  TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc, kOtcryptoAesOperationEncrypt,
                   &cbc_pt2, kOtcryptoAesPaddingNull, &cbc_ct2));
  TRY_CHECK_ARRAYS_EQ(out_buf, kCtsAesCbcNoPadCt, sizeof(kCtsAesCbcNoPadCt));

  // 4. Source: `CipherTest.java:178-182` —
  // `KAT_VECTORS["AES/CBC/PKCS7Padding"]` (39B -> 48B).
  const uint8_t kCtsAesCbcPkcs7Pt[39] = {
      0x9d, 0x49, 0xfb, 0x97, 0x0b, 0x23, 0xbf, 0xe7, 0x42, 0xae,
      0x7c, 0x45, 0xa7, 0x73, 0xad, 0xa9, 0xfa, 0xad, 0x84, 0x70,
      0x8c, 0x88, 0x58, 0xa0, 0x6e, 0x4a, 0x19, 0x2e, 0x0a, 0x90,
      0xe2, 0xf6, 0x08, 0x35, 0x48, 0xe0, 0xbf, 0x3f, 0x67,
  };
  const uint8_t kCtsAesCbcPkcs7Iv[16] = {
      0xec, 0xd8, 0x7b, 0xf9, 0xc4, 0x9f, 0x37, 0xdc,
      0xd2, 0x29, 0x4e, 0x30, 0x91, 0x92, 0x28, 0x9a,
  };
  const uint8_t kCtsAesCbcPkcs7Ct[48] = {
      0xae, 0xb6, 0x4f, 0x48, 0xec, 0x18, 0xa0, 0x86, 0xed, 0xa7, 0xee, 0x08,
      0x09, 0x48, 0x65, 0x1a, 0x50, 0xb6, 0xf5, 0x82, 0xab, 0x54, 0xaa, 0xc5,
      0x45, 0x4c, 0x9a, 0xb0, 0xa4, 0xde, 0x5b, 0x4a, 0x4a, 0xba, 0xc5, 0x26,
      0xa4, 0x30, 0x70, 0x11, 0xd1, 0x28, 0x81, 0xf1, 0x84, 0x9c, 0x32, 0xae,
  };
  memcpy(iv_words, kCtsAesCbcPkcs7Iv, sizeof(iv_words));
  otcrypto_const_byte_buf_t cbc_p_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kCtsAesCbcPkcs7Pt, sizeof(kCtsAesCbcPkcs7Pt));
  otcrypto_byte_buf_t cbc_p_out = OTCRYPTO_MAKE_BUF(
      otcrypto_byte_buf_t, out_buf, sizeof(kCtsAesCbcPkcs7Ct));
  TRY(otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc, kOtcryptoAesOperationEncrypt,
                   &cbc_p_in, kOtcryptoAesPaddingPkcs7, &cbc_p_out));
  TRY_CHECK_ARRAYS_EQ(out_buf, kCtsAesCbcPkcs7Ct, sizeof(kCtsAesCbcPkcs7Ct));

  // 4b. StrongBox KeyMint VTS
  // `Aes{128,256}{CBC,ECB}{NoPadding,PKCS7Padding}OneByteAtATime`
  // (`KeyMintTest.cpp:6286-6585` & `AES{128,256}*CipherTest.java`):
  const uint8_t kVts128CbcNoPadKey[16] = {0x7e, 0x3d, 0x72, 0x3c, 0x09, 0xa9,
                                          0x85, 0x2b, 0x24, 0xf5, 0x84, 0xf9,
                                          0xd9, 0x16, 0xf6, 0xa8};
  const uint8_t kVts128CbcNoPadIv[16] = {0x94, 0x4a, 0xe2, 0x74, 0xd9, 0x83,
                                         0x89, 0x2e, 0xad, 0xe4, 0x22, 0x27,
                                         0x48, 0x58, 0xa9, 0x6a};
  const uint8_t kVts128CbcNoPadPt[48] = {
      0x04, 0x4e, 0x15, 0x89, 0x9a, 0x08, 0x0a, 0xad, 0xeb, 0x67, 0x78, 0xf6,
      0x43, 0x23, 0xb6, 0x4d, 0x2c, 0xbc, 0xba, 0xdb, 0x33, 0x8d, 0xf9, 0x3b,
      0x9a, 0xc4, 0x59, 0xd4, 0xf4, 0x10, 0x29, 0x80, 0x9f, 0xff, 0x37, 0x08,
      0x1c, 0x22, 0xef, 0x27, 0x8f, 0x89, 0x6a, 0xb2, 0x13, 0xa2, 0xa6, 0x31};
  const uint8_t kVts128CbcNoPadCt[48] = {
      0xb4, 0x19, 0x29, 0x3f, 0xcb, 0xd6, 0x86, 0xf2, 0x91, 0x3d, 0x1c, 0xf9,
      0x47, 0xe5, 0x10, 0xd4, 0x2f, 0xaf, 0xed, 0xe5, 0x59, 0x3c, 0x98, 0xaf,
      0xd6, 0xae, 0xe2, 0x72, 0x59, 0x6a, 0x56, 0xfe, 0x42, 0xc2, 0x2f, 0x2a,
      0x5e, 0x3b, 0x6a, 0x02, 0xba, 0x9d, 0x8d, 0x0d, 0xe1, 0xe9, 0xa8, 0x10};
  const uint8_t kVts128CbcPkcs7Key[16] = {0xf1, 0x6e, 0x69, 0x84, 0x72, 0x57,
                                          0x8e, 0x91, 0x9d, 0x92, 0x80, 0x62,
                                          0x62, 0xc5, 0x16, 0x9f};
  const uint8_t kVts128CbcPkcs7Iv[16] = {0xef, 0x74, 0x35, 0x40, 0xf8, 0x42,
                                         0x1a, 0xca, 0x12, 0x8a, 0x32, 0x47,
                                         0x52, 0x1f, 0x3e, 0x7d};
  const uint8_t kVts128CbcPkcs7Pt[57] = {
      0x5b, 0xeb, 0xf3, 0x35, 0x69, 0xd9, 0x0b, 0xf5, 0xe8, 0x53, 0x81, 0x4e,
      0x12, 0xe7, 0xc7, 0xaa, 0x57, 0x58, 0x01, 0x3f, 0x75, 0x57, 0x73, 0xe2,
      0x9f, 0x4a, 0x25, 0xec, 0x26, 0xee, 0xb7, 0x65, 0xf7, 0xf2, 0xdc, 0x25,
      0x1f, 0x7d, 0xc6, 0x2a, 0xef, 0xca, 0x1e, 0x8a, 0x5a, 0x11, 0xa1, 0xdc,
      0xd4, 0x4f, 0x0b, 0xd8, 0xfb, 0x59, 0x3a, 0x5a, 0xe3};
  const uint8_t kVts128CbcPkcs7Ct[64] = {
      0x31, 0x97, 0xcf, 0x6d, 0xb9, 0x46, 0x61, 0x88, 0xb5, 0xfe, 0xd3,
      0x75, 0x32, 0x93, 0x24, 0xee, 0x7d, 0x60, 0x92, 0xa8, 0xc0, 0xe4,
      0x1d, 0xfa, 0xf4, 0x9e, 0x37, 0x24, 0x27, 0x14, 0x27, 0x89, 0x6d,
      0x56, 0xa6, 0x24, 0x3c, 0x0d, 0x59, 0xd6, 0x63, 0x97, 0x22, 0xaf,
      0x93, 0xcd, 0x53, 0x44, 0x9b, 0xdd, 0xab, 0xf9, 0xc5, 0xf1, 0x53,
      0xeb, 0xdb, 0xfe, 0xd9, 0xed, 0x98, 0xc8, 0xcc, 0x37};
  const uint8_t kVts128EcbNoPadKey[16] = {0x7d, 0xa2, 0x46, 0x7f, 0x06, 0x88,
                                          0x54, 0xb3, 0xcb, 0x36, 0xe5, 0xc3,
                                          0x33, 0xa1, 0x66, 0x19};
  const uint8_t kVts128EcbNoPadPt[48] = {
      0x9a, 0x07, 0xc9, 0x57, 0x5a, 0xd9, 0xce, 0x20, 0x9d, 0xf9, 0xf3, 0x95,
      0x39, 0x65, 0xce, 0xbe, 0x82, 0x08, 0x58, 0x7c, 0x7a, 0xe5, 0x75, 0xa1,
      0x90, 0x4b, 0xf2, 0x50, 0x48, 0x94, 0x6d, 0x7b, 0x61, 0x68, 0xa9, 0xa2,
      0x7b, 0xce, 0x55, 0x4b, 0xea, 0x94, 0xef, 0x26, 0xe6, 0xc7, 0x42, 0xa0};
  const uint8_t kVts128EcbNoPadCt[48] = {
      0x8c, 0x47, 0xe4, 0x94, 0x20, 0xfc, 0x92, 0xac, 0x4c, 0xa2, 0xc6, 0x01,
      0xbc, 0x3f, 0x8a, 0xc3, 0x1d, 0x01, 0xb2, 0x60, 0xb7, 0xb8, 0x49, 0xf2,
      0xb8, 0xee, 0xdf, 0xff, 0xed, 0x8f, 0x36, 0xc3, 0x1c, 0xbd, 0xa0, 0xd2,
      0x2f, 0x95, 0xc9, 0xc2, 0xa4, 0x8c, 0x34, 0x7e, 0x8c, 0x77, 0xac, 0x82};
  const uint8_t kVts128EcbPkcs7Key[16] = {0xc3, 0xbe, 0x04, 0xbc, 0xcb, 0x3d,
                                          0x99, 0xb8, 0x52, 0x90, 0xf1, 0x13,
                                          0xfe, 0x7a, 0xf1, 0x94};
  const uint8_t kVts128EcbPkcs7Pt[53] = {
      0x34, 0x8c, 0x21, 0x3f, 0xd8, 0xdf, 0x3f, 0x99, 0x0c, 0x20, 0xc5,
      0xac, 0xbf, 0x07, 0xb3, 0x4b, 0x62, 0x64, 0xae, 0x24, 0x57, 0x84,
      0xa5, 0xa6, 0x17, 0x6d, 0xbf, 0xb1, 0xc2, 0xe7, 0xdd, 0x27, 0xe5,
      0x2c, 0xc9, 0x2b, 0x8e, 0xee, 0x40, 0x61, 0x4f, 0x05, 0xb5, 0x07,
      0xb3, 0x55, 0xf6, 0x35, 0x4a, 0x27, 0x05, 0xbd, 0x86};
  const uint8_t kVts128EcbPkcs7Ct[64] = {
      0x07, 0xcd, 0x05, 0xc4, 0x1f, 0xed, 0xed, 0xdc, 0x5d, 0xb4, 0xb3,
      0xe3, 0x5e, 0x67, 0x61, 0x53, 0x18, 0x4a, 0x11, 0x9a, 0xa4, 0xdf,
      0xdd, 0xc2, 0x90, 0x61, 0x6f, 0x1f, 0xa6, 0x00, 0x93, 0x1d, 0xe6,
      0xbe, 0xa9, 0xbd, 0xb9, 0x0d, 0x1d, 0x73, 0x38, 0x99, 0x94, 0x6f,
      0x8c, 0x8e, 0x5c, 0x0c, 0x43, 0x83, 0xf9, 0x9f, 0x5d, 0x88, 0xe2,
      0x7f, 0x3e, 0xbc, 0x0c, 0x6e, 0x52, 0x75, 0x9e, 0xd3};
  const uint8_t kVts256CbcNoPadKey[32] = {
      0xdd, 0x2f, 0x20, 0xdc, 0x6b, 0x98, 0xc1, 0x00, 0xba, 0xc9, 0x19,
      0x12, 0x0f, 0xf9, 0x5e, 0xb5, 0xd9, 0x60, 0x03, 0xf8, 0x22, 0x99,
      0x87, 0xb2, 0x83, 0xa1, 0xe7, 0x77, 0xb0, 0xcd, 0x5c, 0x30};
  const uint8_t kVts256CbcNoPadIv[16] = {0x23, 0xb4, 0xd8, 0x52, 0x39, 0xfb,
                                         0x90, 0xdb, 0x93, 0xb0, 0x7a, 0x98,
                                         0x1e, 0x90, 0xa1, 0x70};
  const uint8_t kVts256CbcNoPadPt[48] = {
      0x2f, 0xbe, 0x5d, 0x46, 0xdc, 0xa5, 0xce, 0xa4, 0x33, 0xe5, 0x50, 0xd8,
      0xb2, 0x91, 0x74, 0x0a, 0xb9, 0x55, 0x1c, 0x2a, 0x2d, 0x37, 0x68, 0x0d,
      0x7f, 0xb7, 0xb9, 0x93, 0x22, 0x5f, 0x58, 0x49, 0x4c, 0xb5, 0x3c, 0xac,
      0xa3, 0x53, 0xe4, 0xb6, 0x37, 0xba, 0x05, 0x68, 0x7b, 0xe2, 0x0f, 0x8d};
  const uint8_t kVts256CbcNoPadCt[48] = {
      0x5a, 0xba, 0x24, 0xfc, 0x31, 0x69, 0x36, 0xc8, 0x36, 0x90, 0x61, 0xee,
      0x8f, 0xe4, 0x63, 0xe4, 0xfa, 0xed, 0x04, 0x28, 0x8e, 0x20, 0x44, 0x56,
      0x62, 0x6b, 0x98, 0x8c, 0x0e, 0x37, 0x6b, 0x60, 0x47, 0xda, 0x1e, 0x4f,
      0xd7, 0xc4, 0xe1, 0xcf, 0x26, 0x56, 0x09, 0x7f, 0x75, 0xae, 0x86, 0x85};
  const uint8_t kVts256CbcPkcs7Key[32] = {
      0x03, 0xab, 0x25, 0x10, 0x52, 0x0f, 0x5c, 0xfe, 0xbf, 0xab, 0x0a,
      0x17, 0xa7, 0xf8, 0x32, 0x4c, 0x96, 0x34, 0x91, 0x1f, 0x6f, 0xc5,
      0x9e, 0x58, 0x6f, 0x85, 0x34, 0x6b, 0xb3, 0x8a, 0xc8, 0x8a};
  const uint8_t kVts256CbcPkcs7Iv[16] = {0x9a, 0xf9, 0x69, 0x67, 0x19, 0x5b,
                                         0xb0, 0x18, 0x4f, 0x12, 0x9b, 0xef,
                                         0xfa, 0x82, 0x41, 0xae};
  const uint8_t kVts256CbcPkcs7Pt[47] = {
      0x2d, 0x69, 0x44, 0x65, 0x3a, 0xc1, 0x49, 0x88, 0xa7, 0x72, 0xa2, 0x73,
      0x0b, 0x7c, 0x5b, 0xfa, 0x99, 0xa2, 0x17, 0x32, 0xae, 0x26, 0xf4, 0x0c,
      0xdc, 0x5b, 0x3a, 0x28, 0x74, 0xc7, 0x94, 0x25, 0x45, 0xa8, 0x2b, 0x73,
      0xc4, 0x80, 0x78, 0xb9, 0xda, 0xe6, 0x22, 0x61, 0xc6, 0x59, 0x09};
  const uint8_t kVts256CbcPkcs7Ct[48] = {
      0x26, 0xb3, 0x08, 0xf7, 0xe1, 0x66, 0x8b, 0x55, 0x70, 0x5a, 0x79, 0xc8,
      0xb3, 0xad, 0x10, 0xe2, 0x44, 0x65, 0x5f, 0x70, 0x5f, 0x02, 0x7f, 0x39,
      0x0a, 0x5c, 0x34, 0xe4, 0x53, 0x6f, 0x51, 0x94, 0x03, 0xa7, 0x19, 0x87,
      0xb9, 0x51, 0x24, 0x07, 0x3d, 0x69, 0xf2, 0xa3, 0xcb, 0x95, 0xb0, 0xab};
  const uint8_t kVts256EcbNoPadKey[32] = {
      0xfa, 0x46, 0x22, 0xd9, 0xcf, 0x64, 0x85, 0x07, 0x5d, 0xae, 0xdd,
      0x33, 0xd2, 0xc4, 0xff, 0xfd, 0xf8, 0x59, 0xe2, 0xed, 0xb7, 0xf7,
      0xdf, 0x4f, 0x04, 0x60, 0x3f, 0x7e, 0x64, 0x7f, 0xae, 0x90};
  const uint8_t kVts256EcbNoPadPt[48] = {
      0x96, 0xcc, 0xab, 0xbe, 0x0c, 0x68, 0x97, 0x0d, 0x8c, 0xde, 0xe2, 0xb3,
      0x0a, 0xb4, 0x3c, 0x2d, 0x61, 0xcc, 0x50, 0xee, 0x68, 0x27, 0x1e, 0x77,
      0x57, 0x1e, 0x72, 0x47, 0x8d, 0x71, 0x3a, 0x31, 0xa4, 0x76, 0xd6, 0x80,
      0x6b, 0x81, 0x16, 0x08, 0x9c, 0x6e, 0xc5, 0x0b, 0xb5, 0x43, 0x20, 0x0f};
  const uint8_t kVts256EcbNoPadCt[48] = {
      0x0e, 0x81, 0x83, 0x9e, 0x9d, 0xfb, 0xfe, 0x3b, 0x50, 0x3d, 0x61, 0x9e,
      0x67, 0x6a, 0xbe, 0x5a, 0xc8, 0x0f, 0xac, 0x3f, 0x24, 0x5d, 0x8f, 0x09,
      0xb9, 0x13, 0x4b, 0x1b, 0x32, 0xa6, 0x7d, 0xc8, 0x3e, 0x37, 0x7f, 0xaf,
      0x24, 0x62, 0x88, 0x93, 0x11, 0x36, 0xbe, 0xf2, 0xa0, 0x7c, 0x0b, 0xe4};
  const uint8_t kVts256EcbPkcs7Key[32] = {
      0xbf, 0x3f, 0x07, 0xc6, 0x84, 0x67, 0xfe, 0xad, 0x0c, 0xa8, 0xe2,
      0x75, 0x45, 0x00, 0xab, 0x51, 0x42, 0x58, 0xab, 0xf0, 0x2e, 0xb7,
      0xe6, 0x15, 0xa4, 0x93, 0xbc, 0xaa, 0xa4, 0x5d, 0x5e, 0xe1};
  const uint8_t kVts256EcbPkcs7Pt[32] = {
      0xaf, 0x07, 0x57, 0xe4, 0x90, 0x18, 0xda, 0xd6, 0x28, 0xf1, 0x69,
      0x98, 0x62, 0x8a, 0x40, 0x7d, 0xb5, 0xf2, 0x82, 0x91, 0xbe, 0xf3,
      0xbc, 0x2e, 0x4d, 0x8a, 0x5a, 0x31, 0xfb, 0x23, 0x8e, 0x6f};
  const uint8_t kVts256EcbPkcs7Ct[48] = {
      0x21, 0xec, 0x30, 0x11, 0x07, 0x4b, 0xf1, 0xef, 0x14, 0x06, 0x43, 0xd4,
      0x71, 0x30, 0x32, 0x6c, 0x5e, 0x18, 0x3f, 0x61, 0x23, 0x7c, 0x69, 0xbc,
      0x77, 0x55, 0x1c, 0xa2, 0x07, 0xd7, 0x1f, 0xc2, 0xb9, 0x0c, 0xfa, 0xc6,
      0xc8, 0xd2, 0xd1, 0x25, 0xe5, 0xcd, 0x9f, 0xf3, 0x53, 0xde, 0xe0, 0xdf};
  const struct {
    const uint8_t *key;
    size_t key_len;
    otcrypto_key_mode_t key_mode;
    otcrypto_aes_mode_t aes_mode;
    otcrypto_aes_padding_t padding;
    const uint8_t *iv;
    const uint8_t *pt;
    size_t pt_len;
    const uint8_t *ct;
    size_t ct_len;
  } kVtsBlockKatVectors[8] = {
      {kVts128CbcNoPadKey, 16, kOtcryptoKeyModeAesCbc, kOtcryptoAesModeCbc,
       kOtcryptoAesPaddingNull, kVts128CbcNoPadIv, kVts128CbcNoPadPt, 48,
       kVts128CbcNoPadCt, 48},
      {kVts128CbcPkcs7Key, 16, kOtcryptoKeyModeAesCbc, kOtcryptoAesModeCbc,
       kOtcryptoAesPaddingPkcs7, kVts128CbcPkcs7Iv, kVts128CbcPkcs7Pt, 57,
       kVts128CbcPkcs7Ct, 64},
      {kVts128EcbNoPadKey, 16, kOtcryptoKeyModeAesEcb, kOtcryptoAesModeEcb,
       kOtcryptoAesPaddingNull, NULL, kVts128EcbNoPadPt, 48, kVts128EcbNoPadCt,
       48},
      {kVts128EcbPkcs7Key, 16, kOtcryptoKeyModeAesEcb, kOtcryptoAesModeEcb,
       kOtcryptoAesPaddingPkcs7, NULL, kVts128EcbPkcs7Pt, 53, kVts128EcbPkcs7Ct,
       64},
      {kVts256CbcNoPadKey, 32, kOtcryptoKeyModeAesCbc, kOtcryptoAesModeCbc,
       kOtcryptoAesPaddingNull, kVts256CbcNoPadIv, kVts256CbcNoPadPt, 48,
       kVts256CbcNoPadCt, 48},
      {kVts256CbcPkcs7Key, 32, kOtcryptoKeyModeAesCbc, kOtcryptoAesModeCbc,
       kOtcryptoAesPaddingPkcs7, kVts256CbcPkcs7Iv, kVts256CbcPkcs7Pt, 47,
       kVts256CbcPkcs7Ct, 48},
      {kVts256EcbNoPadKey, 32, kOtcryptoKeyModeAesEcb, kOtcryptoAesModeEcb,
       kOtcryptoAesPaddingNull, NULL, kVts256EcbNoPadPt, 48, kVts256EcbNoPadCt,
       48},
      {kVts256EcbPkcs7Key, 32, kOtcryptoKeyModeAesEcb, kOtcryptoAesModeEcb,
       kOtcryptoAesPaddingPkcs7, NULL, kVts256EcbPkcs7Pt, 32, kVts256EcbPkcs7Ct,
       48},
  };
  for (size_t v = 0; v < ARRAYSIZE(kVtsBlockKatVectors); ++v) {
    uint32_t v_key_words[kAesMaxKeyWords] = {0};
    memcpy(v_key_words, kVtsBlockKatVectors[v].key,
           kVtsBlockKatVectors[v].key_len);
    build_aes_key(v_key_words, kVtsBlockKatVectors[v].key_len,
                  kVtsBlockKatVectors[v].key_mode, keyblob,
                  2 * (kVtsBlockKatVectors[v].key_len / sizeof(uint32_t)),
                  &key);
    if (kVtsBlockKatVectors[v].iv != NULL) {
      memcpy(iv_words, kVtsBlockKatVectors[v].iv, sizeof(iv_words));
    } else {
      memset(iv_words, 0, sizeof(iv_words));
    }
    otcrypto_const_byte_buf_t v_pt =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kVtsBlockKatVectors[v].pt,
                          kVtsBlockKatVectors[v].pt_len);
    otcrypto_byte_buf_t v_ct = OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, out_buf,
                                                 kVtsBlockKatVectors[v].ct_len);
    TRY(otcrypto_aes(&key, &iv, kVtsBlockKatVectors[v].aes_mode,
                     kOtcryptoAesOperationEncrypt, &v_pt,
                     kVtsBlockKatVectors[v].padding, &v_ct));
    TRY_CHECK_ARRAYS_EQ(out_buf, kVtsBlockKatVectors[v].ct,
                        kVtsBlockKatVectors[v].ct_len);

    if (kVtsBlockKatVectors[v].iv != NULL) {
      memcpy(iv_words, kVtsBlockKatVectors[v].iv, sizeof(iv_words));
    }
    otcrypto_const_byte_buf_t v_ct_in =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kVtsBlockKatVectors[v].ct,
                          kVtsBlockKatVectors[v].ct_len);
    otcrypto_byte_buf_t v_dec_out = OTCRYPTO_MAKE_BUF(
        otcrypto_byte_buf_t, dec_buf, kVtsBlockKatVectors[v].ct_len);
    TRY(otcrypto_aes(&key, &iv, kVtsBlockKatVectors[v].aes_mode,
                     kOtcryptoAesOperationDecrypt, &v_ct_in,
                     kVtsBlockKatVectors[v].padding, &v_dec_out));
    if (kVtsBlockKatVectors[v].padding == kOtcryptoAesPaddingPkcs7) {
      size_t unpadded_len = 0;
      TRY(otcrypto_aes_padding_strip(&v_dec_out, kOtcryptoAesPaddingPkcs7,
                                     &unpadded_len));
      TRY_CHECK(unpadded_len == kVtsBlockKatVectors[v].pt_len);
    }
    TRY_CHECK_ARRAYS_EQ(dec_buf, kVtsBlockKatVectors[v].pt,
                        kVtsBlockKatVectors[v].pt_len);
  }

  // 5. KeyMint VTS `AesEcbIncremental`, `AesCbcIncremental`, &
  // `AesCtrIncremental` (`KeyMintTest.cpp:6251-6275`, lengths 16..240 step 48)
  // across StrongBox CTS `CipherTest.java:291-298` (`importKatKeys`) keys
  // (`AES128_KAT_KEY_BYTES` and `AES256_KAT_KEY_BYTES`).
  const uint32_t kCtsAes256KatKey[8] = {
      0xc11c60cf, 0x4d43af0a, 0x7174011f, 0x22f2af36,
      0x26b47faf, 0x179001d1, 0x3f4c2112, 0x5f1218ea,
  };
  const struct {
    const uint32_t *words;
    size_t key_len;
  } kCtsKatKeys[2] = {
      {kCtsAes128KatKey, 16},
      {kCtsAes256KatKey, 32},
  };
  uint8_t msg_240[240];
  for (size_t i = 0; i < sizeof(msg_240); ++i) {
    msg_240[i] = (uint8_t)(i & 0xff);
  }
  uint8_t ct_oneshot[240];
  uint8_t ct_inc[240];
  const otcrypto_key_mode_t kIncKeyModes[3] = {
      kOtcryptoKeyModeAesEcb, kOtcryptoKeyModeAesCbc, kOtcryptoKeyModeAesCtr};
  const otcrypto_aes_mode_t kIncAesModes[3] = {
      kOtcryptoAesModeEcb, kOtcryptoAesModeCbc, kOtcryptoAesModeCtr};
  for (size_t k = 0; k < ARRAYSIZE(kCtsKatKeys); ++k) {
    for (size_t m = 0; m < ARRAYSIZE(kIncAesModes); ++m) {
      build_aes_key(kCtsKatKeys[k].words, kCtsKatKeys[k].key_len,
                    kIncKeyModes[m], keyblob,
                    2 * (kCtsKatKeys[k].key_len / sizeof(uint32_t)), &key);
      for (size_t len = 16; len <= sizeof(msg_240); len += 48) {
        memcpy(iv_words, kDefaultIv, sizeof(iv_words));
        otcrypto_const_byte_buf_t pt_all =
            OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg_240, len);
        otcrypto_byte_buf_t ct_all =
            OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ct_oneshot, len);
        TRY(otcrypto_aes(&key, &iv, kIncAesModes[m],
                         kOtcryptoAesOperationEncrypt, &pt_all,
                         kOtcryptoAesPaddingNull, &ct_all));

        memcpy(iv_words, kDefaultIv, sizeof(iv_words));
        for (size_t off = 0; off < len; off += 16) {
          otcrypto_const_byte_buf_t b_pt =
              OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg_240 + off, 16);
          otcrypto_byte_buf_t b_ct =
              OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ct_inc + off, 16);
          TRY(otcrypto_aes(&key, &iv, kIncAesModes[m],
                           kOtcryptoAesOperationEncrypt, &b_pt,
                           kOtcryptoAesPaddingNull, &b_ct));
        }
        TRY_CHECK_ARRAYS_EQ(ct_inc, ct_oneshot, len);
      }
    }
  }
  return OK_STATUS();
}

typedef struct aes_zero_input_case {
  size_t key_idx;
  otcrypto_key_mode_t key_mode;
  otcrypto_aes_mode_t aes_mode;
} aes_zero_input_case_t;

static const aes_zero_input_case_t kAesZeroInputCases[] = {
    {0, kOtcryptoKeyModeAesEcb, kOtcryptoAesModeEcb},
    {0, kOtcryptoKeyModeAesCbc, kOtcryptoAesModeCbc},
    {0, kOtcryptoKeyModeAesCtr, kOtcryptoAesModeCtr},
    {1, kOtcryptoKeyModeAesEcb, kOtcryptoAesModeEcb},
    {1, kOtcryptoKeyModeAesCbc, kOtcryptoAesModeCbc},
    {1, kOtcryptoKeyModeAesCtr, kOtcryptoAesModeCtr},
};

static const aes_zero_input_case_t *current_zero_input_case = NULL;

/**
 * Source:
 *   - `KeyMintTest.cpp:6749` —
 *     `TEST_P(EncryptionOperationsTest, AesCbcZeroInputSuccess)`
 *   - `CipherTest.java:398` — `testEmptyPlaintextEncryptsAndDecrypts`
 *     (`AES/ECB/NoPadding`, `AES/CBC/NoPadding`, and `AES/CTR/NoPadding`)
 *
 * Zero-length input with `kOtcryptoAesPaddingNull` (0 blocks) should succeed
 * (`OTCRYPTO_OK`) with 0-byte output.
 */
static status_t aes_empty_plaintext_no_padding_test(void) {
  size_t k = current_zero_input_case->key_idx;
  LOG_INFO(
      "Testing AesCbcZeroInputSuccess / testEmptyPlaintextEncryptsAndDecrypts "
      "(key_bytes=%u, mode=0x%x)",
      kKeySizes[k], current_zero_input_case->aes_mode);

  uint32_t keyblob[2 * kAesMaxKeyWords];
  otcrypto_blinded_key_t key;
  build_aes_key(kTestKeys[k], kKeySizes[k], current_zero_input_case->key_mode,
                keyblob, 2 * (kKeySizes[k] / sizeof(uint32_t)), &key);
  uint32_t iv_words[kAesBlockWords];
  memcpy(iv_words, kDefaultIv, sizeof(iv_words));
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));
  uint8_t dummy = 0;
  otcrypto_const_byte_buf_t empty_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, &dummy, 0);
  otcrypto_byte_buf_t empty_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, &dummy, 0);

  TRY(otcrypto_aes(&key, &iv, current_zero_input_case->aes_mode,
                   kOtcryptoAesOperationEncrypt, &empty_in,
                   kOtcryptoAesPaddingNull, &empty_out));
  memcpy(iv_words, kDefaultIv, sizeof(iv_words));
  TRY(otcrypto_aes(&key, &iv, current_zero_input_case->aes_mode,
                   kOtcryptoAesOperationDecrypt, &empty_in,
                   kOtcryptoAesPaddingNull, &empty_out));
  return OK_STATUS();
}

static const uint8_t kCtsCtrKatKey[16] = {
    0x7d, 0x9f, 0x11, 0xa0, 0xda, 0x11, 0x1e, 0x9d,
    0x8b, 0xdd, 0x14, 0xf0, 0x46, 0x48, 0xed, 0x91,
};
static const uint8_t kCtsCtrKatIv[16] = {
    0x94, 0xd9, 0xf7, 0xa6, 0xd1, 0x6f, 0x58, 0x01,
    0x88, 0x19, 0xb6, 0x68, 0x02, 0x0b, 0x68, 0xcc,
};
static const uint8_t kCtsCtrKatPt[33] = {
    0xb4, 0xe7, 0x86, 0xca, 0xb9, 0xdf, 0x48, 0xd2, 0xfc, 0xe0, 0xc7,
    0x87, 0x26, 0x51, 0x31, 0x4d, 0xb1, 0x31, 0x8d, 0x1f, 0x31, 0xa1,
    0xb1, 0x0a, 0x2c, 0x33, 0x4d, 0x25, 0x55, 0xb4, 0x11, 0x76, 0x68,
};
static const uint8_t kCtsCtrKatCt[33] = {
    0x02, 0x2e, 0x74, 0x57, 0x2a, 0x70, 0xbe, 0x57, 0xa0, 0xb6, 0x5b,
    0x2f, 0xb5, 0xbc, 0x9b, 0x80, 0x3c, 0xe4, 0x89, 0x73, 0xb6, 0x16,
    0x3f, 0x52, 0x8b, 0xbe, 0x1f, 0xd0, 0x01, 0xe2, 0x9d, 0x33, 0x0a,
};
static const uint8_t kVtsAes128CtrKey[16] = {
    0x47, 0x13, 0xa7, 0xb2, 0xf9, 0x3e, 0xfe, 0x80,
    0x9b, 0x42, 0xec, 0xc4, 0x52, 0x13, 0xef, 0x9f,
};
static const uint8_t kVtsAes128CtrIv[16] = {
    0xeb, 0xfa, 0x19, 0xb0, 0xeb, 0xf3, 0xd5, 0x7f,
    0xea, 0xbd, 0x4c, 0x4b, 0xd0, 0x4b, 0xea, 0x01,
};
static const uint8_t kVtsAes128CtrPt[55] = {
    0x6d, 0x2c, 0x07, 0xe1, 0xfc, 0x86, 0xf9, 0x9c, 0x6e, 0x2a, 0x8f,
    0x65, 0x67, 0x82, 0x8b, 0x42, 0x62, 0xa9, 0xc2, 0x3d, 0x0f, 0x3e,
    0xd8, 0xab, 0x32, 0x48, 0x22, 0x83, 0xc7, 0x97, 0x96, 0xf0, 0xad,
    0xba, 0x1b, 0xcd, 0x37, 0x36, 0x08, 0x49, 0x96, 0x45, 0x2a, 0x91,
    0x7f, 0xae, 0x98, 0x00, 0x5a, 0xeb, 0xe6, 0x1f, 0x9e, 0x91, 0xc3,
};
static const uint8_t kVtsAes128CtrCt[55] = {
    0x34, 0x5d, 0xeb, 0x1d, 0x67, 0xb9, 0x5e, 0x60, 0x0e, 0x05, 0xca,
    0xd4, 0xc3, 0x2e, 0xc3, 0x81, 0xaa, 0xdb, 0x3e, 0x2c, 0x1e, 0xc7,
    0xe0, 0xfb, 0x95, 0x6d, 0xc3, 0x8e, 0x68, 0x60, 0xcf, 0x05, 0x53,
    0x53, 0x55, 0x66, 0xe1, 0xb1, 0x2f, 0xa9, 0xf8, 0x7d, 0x29, 0x26,
    0x6c, 0xa2, 0x6d, 0xf4, 0x27, 0x23, 0x3d, 0xf0, 0x35, 0xdf, 0x28,
};
static const uint8_t kVtsAes256CtrKey[32] = {
    0x92, 0x8b, 0x38, 0x0a, 0x8f, 0xed, 0x4b, 0x4b, 0x4c, 0xfe, 0xb5,
    0x6e, 0x0c, 0x66, 0xa4, 0xcb, 0x0f, 0x9f, 0xf5, 0x8d, 0x61, 0xac,
    0x68, 0xbc, 0xfd, 0x0e, 0x3f, 0xbd, 0x91, 0x0a, 0x68, 0x4f,
};
static const uint8_t kVtsAes256CtrIv[16] = {
    0x0b, 0x67, 0x8a, 0x52, 0x49, 0xe6, 0xee, 0xda,
    0x46, 0x1d, 0xfb, 0x47, 0x76, 0xb6, 0xc5, 0x8e,
};
static const uint8_t kVtsAes256CtrPt[36] = {
    0xf3, 0x58, 0xde, 0x57, 0x54, 0x3b, 0x29, 0x7e, 0x99, 0x7c, 0xba, 0x46,
    0xfb, 0x91, 0x00, 0x55, 0x3d, 0x6a, 0xbd, 0x65, 0x37, 0x7e, 0x55, 0xb9,
    0xaa, 0xc3, 0x00, 0x64, 0x00, 0xea, 0xd1, 0x1f, 0x6d, 0xb3, 0xc8, 0x84,
};
static const uint8_t kVtsAes256CtrCt[36] = {
    0xa0, 0x7a, 0x35, 0xfb, 0xd1, 0x77, 0x6a, 0xd8, 0x14, 0x62, 0xe1, 0x93,
    0x5f, 0x54, 0x23, 0x37, 0xad, 0xd6, 0x09, 0x62, 0xbf, 0x28, 0x92, 0x49,
    0x47, 0x68, 0x17, 0xb6, 0xdd, 0xd5, 0x32, 0xa7, 0xbe, 0x30, 0xd4, 0xc3,
};

typedef struct unaligned_ctr_vector {
  const uint8_t *key;
  size_t key_len;
  const uint8_t *iv;
  const uint8_t *pt;
  const uint8_t *ct;
  size_t len;
} unaligned_ctr_vector_t;

static const unaligned_ctr_vector_t kUnalignedCtrVectors[3] = {
    {kCtsCtrKatKey, 16, kCtsCtrKatIv, kCtsCtrKatPt, kCtsCtrKatCt, 33},
    {kVtsAes128CtrKey, 16, kVtsAes128CtrIv, kVtsAes128CtrPt, kVtsAes128CtrCt,
     55},
    {kVtsAes256CtrKey, 32, kVtsAes256CtrIv, kVtsAes256CtrPt, kVtsAes256CtrCt,
     36},
};

static const unaligned_ctr_vector_t *current_unaligned_ctr_vec = NULL;

/**
 * Source:
 *   - `CipherTest.java:183-186` — `KAT_VECTORS["AES/CTR/NoPadding"]` (33B)
 *   - `KeyMintTest.cpp:6318, 6526` & `AES{128,256}CTRNoPaddingCipherTest.java`
 *     — `Aes{128,256}CTRNoPaddingOneByteAtATime` (55B, 36B)
 *
 * Verifies the StrongBox non-block-aligned CTR KAT vectors.
 */
static status_t aes_ctr_unaligned_kat_vectors_test(void) {
  LOG_INFO(
      "Testing StrongBox Android CTS & KeyMint VTS non-block-aligned AES-CTR "
      "KAT vector (key_len=%u, len=%u)",
      current_unaligned_ctr_vec->key_len, current_unaligned_ctr_vec->len);

  uint32_t ctr_key_words[kAesMaxKeyWords] = {0};
  memcpy(ctr_key_words, current_unaligned_ctr_vec->key,
         current_unaligned_ctr_vec->key_len);
  uint32_t ctr_keyblob[2 * kAesMaxKeyWords];
  otcrypto_blinded_key_t ctr_key;
  build_aes_key(ctr_key_words, current_unaligned_ctr_vec->key_len,
                kOtcryptoKeyModeAesCtr, ctr_keyblob,
                2 * (current_unaligned_ctr_vec->key_len / sizeof(uint32_t)),
                &ctr_key);
  uint32_t ctr_iv_words[kAesBlockWords];
  memcpy(ctr_iv_words, current_unaligned_ctr_vec->iv, sizeof(ctr_iv_words));
  otcrypto_word32_buf_t ctr_iv = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, ctr_iv_words, ARRAYSIZE(ctr_iv_words));
  otcrypto_const_byte_buf_t ctr_pt_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, current_unaligned_ctr_vec->pt,
      current_unaligned_ctr_vec->len);
  uint8_t ctr_out_buf[64] = {0};
  otcrypto_byte_buf_t ctr_ct_out = OTCRYPTO_MAKE_BUF(
      otcrypto_byte_buf_t, ctr_out_buf, current_unaligned_ctr_vec->len);
  TRY(otcrypto_aes(&ctr_key, &ctr_iv, kOtcryptoAesModeCtr,
                   kOtcryptoAesOperationEncrypt, &ctr_pt_in,
                   kOtcryptoAesPaddingNull, &ctr_ct_out));
  TRY_CHECK_ARRAYS_EQ(ctr_out_buf, current_unaligned_ctr_vec->ct,
                      current_unaligned_ctr_vec->len);

  memcpy(ctr_iv_words, current_unaligned_ctr_vec->iv, sizeof(ctr_iv_words));
  otcrypto_const_byte_buf_t ctr_ct_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, current_unaligned_ctr_vec->ct,
      current_unaligned_ctr_vec->len);
  uint8_t ctr_dec_buf[64] = {0};
  otcrypto_byte_buf_t ctr_pt_out = OTCRYPTO_MAKE_BUF(
      otcrypto_byte_buf_t, ctr_dec_buf, current_unaligned_ctr_vec->len);
  TRY(otcrypto_aes(&ctr_key, &ctr_iv, kOtcryptoAesModeCtr,
                   kOtcryptoAesOperationDecrypt, &ctr_ct_in,
                   kOtcryptoAesPaddingNull, &ctr_pt_out));
  TRY_CHECK_ARRAYS_EQ(ctr_dec_buf, current_unaligned_ctr_vec->pt,
                      current_unaligned_ctr_vec->len);
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));

  EXECUTE_TEST(result, aes_ecb_round_trip_success_test);
  EXECUTE_TEST(result, aes_ecb_cbc_pkcs7_padding_test);
  EXECUTE_TEST(result, aes_ecb_cbc_no_padding_wrong_input_size_test);
  EXECUTE_TEST(result, aes_wrong_padding_test);
  EXECUTE_TEST(result, aes_pkcs7_padding_corrupted_and_mangled_test);
  EXECUTE_TEST(result, aes_pkcs7_ciphertext_too_short_test);
  EXECUTE_TEST(result, aes_ctr_round_trip_and_sp800_38a_test);
  EXECUTE_TEST(result, aes_cbc_round_trip_test);
  EXECUTE_TEST(result, aes_cts_kat_vectors_and_vts_incremental_test);

  for (size_t i = 0; i < ARRAYSIZE(kAesZeroInputCases); ++i) {
    current_zero_input_case = &kAesZeroInputCases[i];
    EXECUTE_TEST(result, aes_empty_plaintext_no_padding_test);
  }
  for (size_t i = 0; i < ARRAYSIZE(kUnalignedCtrVectors); ++i) {
    current_unaligned_ctr_vec = &kUnalignedCtrVectors[i];
    EXECUTE_TEST(result, aes_ctr_unaligned_kat_vectors_test);
  }

  // Note: KeyMint VTS `AesCtrIncompatiblePaddingMode` (`KeyMintTest.cpp:6668`)
  // is not implemented here because `otcrypto_aes` applies padding
  // independently of cipher mode. Rejecting non-null padding modes when
  // operating in `kOtcryptoAesModeCtr` is the responsibility of the KeyMint
  // wrapper (see `README.md` Item 2).

  return status_ok(result);
}
