// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/tdes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

/**
 * Android KeyMint VTS (`EncryptionOperationsTest.TripleDes*`) and Android CTS
 * (`StrongboxDESede*`) conformance test suite for `otcrypto_tdes`.
 *
 * Upstream AOSP References:
 *   - `hardware/interfaces/security/keymint/aidl/vts/functional/`
 *     - `KeyMintTest.cpp` (lines 7375-7885)
 *   - `cts/tests/tests/keystore/src/android/keystore/cts/`
 *     - `CipherTest.java`
 *     - `BlockCipherTestBase.java`
 *     - `DESedeCipherTestBase.java`
 *
 * Test Mapping:
 *   - `tdes_ecb_cbc_round_trip_success_test`:
 *     - `KeyMintTest.cpp:7375` (`TripleDesEcbRoundTripSuccess`)
 *     - `KeyMintTest.cpp:7601` (`TripleDesCbcRoundTripSuccess`)
 *   - `tdes_ecb_cbc_pkcs7_padding_test`:
 *     - `TEST_P(EncryptionOperationsTest, TripleDesEcbPkcs7Padding)` (L7420)
 *     - `TEST_P(EncryptionOperationsTest, TripleDesCbcPkcs7Padding)` (L7764)
 *   - `tdes_pkcs7_padding_corrupted_test`:
 *     - `KeyMintTest.cpp:7459` (`TripleDesEcbPkcs7PaddingCorrupted`)
 *     - `KeyMintTest.cpp:7810` (`TripleDesCbcPkcs7PaddingCorrupted`)
 *   - `tdes_wrong_input_size_and_caller_iv_test`:
 *     - `TEST_P(EncryptionOperationsTest, TripleDesInvalidCallerIv)` (L7633)
 *     - `TEST_P(EncryptionOperationsTest, TripleDesCallerIv)` (L7652)
 *     - `KeyMintTest.cpp:7737` (`TripleDesEcbCbcNoPaddingWrongInputSize`)
 *   - `tdes_kat_vectors_test`:
 *     - `TEST_P(EncryptionOperationsTest, TripleDesTestVector)` (L7506-L7599)
 *   - `tdes_cbc_incremental_no_padding_test`:
 *     - `KeyMintTest.cpp:7851` (`TripleDesCbcIncrementalNoPadding`)
 *   - `tdes_cts_kat_vectors_test`:
 *     - `CipherTest.java:273-287` & `300-301` (`KAT_VECTORS` for
 *       `DESede/CBC/NoPadding`, `DESede/CBC/PKCS7Padding`,
 *       `DESede/ECB/NoPadding`, `DESede/ECB/PKCS7Padding`)
 *     - `StrongboxDESedeCBCNoPaddingCipherTest.java` /
 *       `DESedeCBCNoPaddingCipherTest.java` (16B `DESede/CBC/NoPadding` KAT)
 *     - `BlockCipherTestBase.java:1202` (`testDecryptWithMissingPadding`)
 *   - `tdes_cts_empty_plaintext_no_padding_test`:
 *     - `CipherTest.java:398` (`testEmptyPlaintextEncryptsAndDecrypts`)
 */

enum {
  kTdesBlockBytes = 8,
  kTdesBlockWords = kTdesBlockBytes / sizeof(uint32_t),
  kTdesKeyBytes = 24,
  kTdesKeyWords = kTdesKeyBytes / sizeof(uint32_t),
};

static const uint32_t kTdesKeyMask[kTdesKeyWords] = {
    0x1b81540c, 0x220733c9, 0xbf8b380d, 0x05850b42, 0x3370c9a2, 0x8922d979,
};

static const uint8_t kDefaultKeyBytes[kTdesKeyBytes] = {
    0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x23, 0x45, 0x67, 0x89,
    0xab, 0xcd, 0xef, 0x01, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23,
};

static const uint8_t kDefaultIvBytes[kTdesBlockBytes] = {
    0x12, 0x34, 0x56, 0x78, 0x90, 0xab, 0xcd, 0xef,
};

typedef struct tdes_test_vector {
  otcrypto_tdes_mode_t mode;
  otcrypto_tdes_padding_t padding;
  size_t pt_len;
  size_t ct_len;
  const uint8_t *key;
  const uint8_t *iv;
  const uint8_t *plaintext;
  const uint8_t *ciphertext;
} tdes_test_vector_t;

// Source: KeyMintTest.cpp:7508 — kTripleDesTestVectors[0] ("TECBMMT3 Encrypt
// 0")
static const uint8_t kTdesVec1Key[24] = {
    0xa2, 0xb5, 0xbc, 0x67, 0xda, 0x13, 0xdc, 0x92, 0xcd, 0x9d, 0x34, 0x4a,
    0xa2, 0x38, 0x54, 0x4a, 0x0e, 0x1f, 0xa7, 0x9e, 0xf7, 0x68, 0x10, 0xcd,
};
static const uint8_t kTdesVec1Pt[8] = {
    0x32, 0x9d, 0x86, 0xbd, 0xf1, 0xbc, 0x5a, 0xf4,
};
static const uint8_t kTdesVec1Ct[8] = {
    0xd9, 0x46, 0xc2, 0x75, 0x6d, 0x78, 0x63, 0x3f,
};

// Source: KeyMintTest.cpp:7516 — kTripleDesTestVectors[1] ("TECBMMT3 Encrypt
// 1")
static const uint8_t kTdesVec2Key[24] = {
    0x49, 0xe6, 0x92, 0x29, 0x0d, 0x2a, 0x5e, 0x46, 0xba, 0xce, 0x79, 0xb9,
    0x64, 0x8a, 0x4c, 0x5d, 0x49, 0x10, 0x04, 0xc2, 0x62, 0xdc, 0x9d, 0x49,
};
static const uint8_t kTdesVec2Pt[16] = {
    0x6b, 0x15, 0x40, 0x78, 0x1b, 0x01, 0xce, 0x19,
    0x97, 0xad, 0xae, 0x10, 0x2d, 0xbf, 0x3c, 0x5b,
};
static const uint8_t kTdesVec2Ct[16] = {
    0x4d, 0x0d, 0xc1, 0x82, 0xd6, 0xe4, 0x81, 0xac,
    0x4a, 0x3d, 0xc6, 0xab, 0x69, 0x76, 0xcc, 0xae,
};

// Source: KeyMintTest.cpp:7524 — kTripleDesTestVectors[2] ("TECBMMT3 Decrypt
// 0")
static const uint8_t kTdesVec3Key[24] = {
    0x52, 0xda, 0xec, 0x2a, 0xc7, 0xdc, 0x19, 0x58, 0x37, 0x73, 0x92, 0x68,
    0x2f, 0x37, 0x86, 0x0b, 0x2c, 0xc1, 0xea, 0x23, 0x04, 0xba, 0xb0, 0xe9,
};
static const uint8_t kTdesVec3Pt[8] = {
    0x66, 0x0e, 0x7d, 0x32, 0xdc, 0xc9, 0x0e, 0x79,
};
static const uint8_t kTdesVec3Ct[8] = {
    0x6d, 0xaa, 0xd9, 0x4c, 0xe0, 0x8a, 0xcf, 0xe7,
};

// Source: KeyMintTest.cpp:7532 — kTripleDesTestVectors[3] ("TECBMMT3 Decrypt
// 1")
static const uint8_t kTdesVec4Key[24] = {
    0x7f, 0x8f, 0xe3, 0xd3, 0xf4, 0xa4, 0x83, 0x94, 0xfb, 0x68, 0x2c, 0x29,
    0x19, 0x92, 0x6d, 0x6d, 0xdf, 0xce, 0x89, 0x32, 0x52, 0x92, 0x29, 0xce,
};
static const uint8_t kTdesVec4Pt[16] = {
    0x9b, 0x2a, 0xe9, 0xd9, 0x98, 0xef, 0xe6, 0x2f,
    0x1b, 0x59, 0x2e, 0x7e, 0x1d, 0xf8, 0xff, 0x38,
};
static const uint8_t kTdesVec4Ct[16] = {
    0xe9, 0x65, 0x3a, 0x0a, 0x1f, 0x05, 0xd3, 0x1b,
    0x9a, 0xcd, 0x12, 0xd7, 0x3a, 0xa9, 0x87, 0x9d,
};

// Source: KeyMintTest.cpp:7540 — kTripleDesTestVectors[4] ("TCBCMMT3 Encrypt
// 0")
static const uint8_t kTdesVec5Key[24] = {
    0xb5, 0xcb, 0x15, 0x04, 0x80, 0x23, 0x26, 0xc7, 0x3d, 0xf1, 0x86, 0xe3,
    0xe3, 0x52, 0xa2, 0x0d, 0xe6, 0x43, 0xb0, 0xd6, 0x3e, 0xe3, 0x0e, 0x37,
};
static const uint8_t kTdesVec5Iv[8] = {
    0x43, 0xf7, 0x91, 0x13, 0x4c, 0x56, 0x47, 0xba,
};
static const uint8_t kTdesVec5Pt[8] = {
    0xdc, 0xc1, 0x53, 0xce, 0xf8, 0x1d, 0x6f, 0x24,
};
static const uint8_t kTdesVec5Ct[8] = {
    0x92, 0x53, 0x8b, 0xd8, 0xaf, 0x18, 0xd3, 0xba,
};

// Source: KeyMintTest.cpp:7548 & 7556 — kTripleDesTestVectors[5..7]
// ("TCBCMMT3 Encrypt 1" & "TCBCMMT3 Encrypt 1 PKCS7 variant/decrypted")
static const uint8_t kTdesVec6Key[24] = {
    0xa4, 0x9d, 0x75, 0x64, 0x19, 0x9e, 0x97, 0xcb, 0x52, 0x9d, 0x2c, 0x9d,
    0x97, 0xbf, 0x2f, 0x98, 0xd3, 0x5e, 0xdf, 0x57, 0xba, 0x1f, 0x73, 0x58,
};
static const uint8_t kTdesVec6Iv[8] = {
    0xc2, 0xe9, 0x99, 0xcb, 0x62, 0x49, 0x02, 0x3c,
};
static const uint8_t kTdesVec6Pt[17] = {
    0xc6, 0x89, 0xae, 0xe3, 0x8a, 0x30, 0x1b, 0xb3, 0x16,
    0xda, 0x75, 0xdb, 0x36, 0xf1, 0x10, 0xb5, 0x00,
};
static const uint8_t kTdesVec6Ct[24] = {
    0xe9, 0xaf, 0xab, 0xa5, 0xec, 0x75, 0xea, 0x1b, 0xbe, 0x65, 0x50, 0x66,
    0x55, 0xbb, 0x4e, 0xcb, 0x82, 0x5a, 0xa2, 0x7e, 0xc0, 0x65, 0x61, 0x56,
};

// Source: KeyMintTest.cpp:7574 — kTripleDesTestVectors[8] ("TCBCMMT3 Decrypt
// 0")
static const uint8_t kTdesVec7Key[24] = {
    0x5e, 0xb6, 0x04, 0x0d, 0x46, 0x08, 0x2c, 0x7a, 0xa7, 0xd0, 0x6d, 0xfd,
    0x08, 0xdf, 0xea, 0xc8, 0xc1, 0x83, 0x64, 0xc1, 0x54, 0x8c, 0x3b, 0xa1,
};
static const uint8_t kTdesVec7Iv[8] = {
    0x41, 0x74, 0x6c, 0x7e, 0x44, 0x2d, 0x36, 0x81,
};
static const uint8_t kTdesVec7Pt[8] = {
    0xd4, 0xf0, 0x0e, 0xb4, 0x55, 0xde, 0x10, 0x34,
};
static const uint8_t kTdesVec7Ct[8] = {
    0xc5, 0x3a, 0x7b, 0x0e, 0xc4, 0x06, 0x00, 0xfe,
};

// Source: KeyMintTest.cpp:7582 — kTripleDesTestVectors[9] ("TCBCMMT3 Decrypt
// 1")
static const uint8_t kTdesVec8Key[24] = {
    0x5b, 0x1c, 0xce, 0x7c, 0x0d, 0xc1, 0xec, 0x49, 0x13, 0x0d, 0xfb, 0x4a,
    0xf4, 0x57, 0x85, 0xab, 0x91, 0x79, 0xe5, 0x67, 0xf2, 0xc7, 0xd5, 0x49,
};
static const uint8_t kTdesVec8Iv[8] = {
    0x39, 0x82, 0xbc, 0x02, 0xc3, 0x72, 0x7d, 0x45,
};
static const uint8_t kTdesVec8Pt[16] = {
    0xed, 0xae, 0x09, 0x28, 0x8e, 0x9e, 0x3b, 0xc0,
    0x57, 0x46, 0xd8, 0x72, 0xb4, 0x8e, 0x3b, 0x29,
};
static const uint8_t kTdesVec8Ct[16] = {
    0x60, 0x06, 0xf1, 0x0a, 0xde, 0xf5, 0x29, 0x91,
    0xfc, 0xc7, 0x77, 0xa1, 0x23, 0x8b, 0xbb, 0x65,
};

static const tdes_test_vector_t kTdesTestVectors[] = {
    {
        .mode = kOtcryptoTdesModeEcb,
        .padding = kOtcryptoTdesPaddingNull,
        .pt_len = sizeof(kTdesVec1Pt),
        .ct_len = sizeof(kTdesVec1Ct),
        .key = kTdesVec1Key,
        .iv = NULL,
        .plaintext = kTdesVec1Pt,
        .ciphertext = kTdesVec1Ct,
    },
    {
        .mode = kOtcryptoTdesModeEcb,
        .padding = kOtcryptoTdesPaddingNull,
        .pt_len = sizeof(kTdesVec2Pt),
        .ct_len = sizeof(kTdesVec2Ct),
        .key = kTdesVec2Key,
        .iv = NULL,
        .plaintext = kTdesVec2Pt,
        .ciphertext = kTdesVec2Ct,
    },
    {
        .mode = kOtcryptoTdesModeEcb,
        .padding = kOtcryptoTdesPaddingNull,
        .pt_len = sizeof(kTdesVec3Pt),
        .ct_len = sizeof(kTdesVec3Ct),
        .key = kTdesVec3Key,
        .iv = NULL,
        .plaintext = kTdesVec3Pt,
        .ciphertext = kTdesVec3Ct,
    },
    {
        .mode = kOtcryptoTdesModeEcb,
        .padding = kOtcryptoTdesPaddingNull,
        .pt_len = sizeof(kTdesVec4Pt),
        .ct_len = sizeof(kTdesVec4Ct),
        .key = kTdesVec4Key,
        .iv = NULL,
        .plaintext = kTdesVec4Pt,
        .ciphertext = kTdesVec4Ct,
    },
    {
        .mode = kOtcryptoTdesModeCbc,
        .padding = kOtcryptoTdesPaddingNull,
        .pt_len = sizeof(kTdesVec5Pt),
        .ct_len = sizeof(kTdesVec5Ct),
        .key = kTdesVec5Key,
        .iv = kTdesVec5Iv,
        .plaintext = kTdesVec5Pt,
        .ciphertext = kTdesVec5Ct,
    },
    {
        .mode = kOtcryptoTdesModeCbc,
        .padding = kOtcryptoTdesPaddingNull,
        .pt_len = 16,
        .ct_len = 16,
        .key = kTdesVec6Key,
        .iv = kTdesVec6Iv,
        .plaintext = kTdesVec6Pt,
        .ciphertext = kTdesVec6Ct,
    },
    {
        .mode = kOtcryptoTdesModeCbc,
        .padding = kOtcryptoTdesPaddingPkcs7,
        .pt_len = sizeof(kTdesVec6Pt),
        .ct_len = sizeof(kTdesVec6Ct),
        .key = kTdesVec6Key,
        .iv = kTdesVec6Iv,
        .plaintext = kTdesVec6Pt,
        .ciphertext = kTdesVec6Ct,
    },
    {
        .mode = kOtcryptoTdesModeCbc,
        .padding = kOtcryptoTdesPaddingNull,
        .pt_len = sizeof(kTdesVec7Pt),
        .ct_len = sizeof(kTdesVec7Ct),
        .key = kTdesVec7Key,
        .iv = kTdesVec7Iv,
        .plaintext = kTdesVec7Pt,
        .ciphertext = kTdesVec7Ct,
    },
    {
        .mode = kOtcryptoTdesModeCbc,
        .padding = kOtcryptoTdesPaddingNull,
        .pt_len = sizeof(kTdesVec8Pt),
        .ct_len = sizeof(kTdesVec8Ct),
        .key = kTdesVec8Key,
        .iv = kTdesVec8Iv,
        .plaintext = kTdesVec8Pt,
        .ciphertext = kTdesVec8Ct,
    },
};

/**
 * Helper to build a blinded 3-key TDES key.
 */
static void build_tdes_key(const uint8_t *raw_key_bytes,
                           otcrypto_key_mode_t key_mode, uint32_t *keyblob,
                           otcrypto_blinded_key_t *key) {
  uint32_t raw_words[kTdesKeyWords];
  memcpy(raw_words, raw_key_bytes, sizeof(raw_words));
  for (size_t i = 0; i < kTdesKeyWords; ++i) {
    keyblob[i] = raw_words[i] ^ kTdesKeyMask[i];
    keyblob[kTdesKeyWords + i] = kTdesKeyMask[i];
  }
  key->config = (otcrypto_key_config_t){
      .version = otcrypto_lib_version(),
      .key_mode = key_mode,
      .key_length = kTdesKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  key->keyblob_length = 2 * kTdesKeyBytes;
  key->keyblob = keyblob;
  key->checksum = otcrypto_integrity_blinded_checksum(key);
}

/**
 * Helper to encrypt with PKCS#7 padding, then decrypt and
 * strip padding via `otcrypto_tdes_padding_strip`.
 */
static status_t run_tdes_padded_roundtrip(otcrypto_blinded_key_t *key,
                                          otcrypto_tdes_mode_t cipher_mode,
                                          otcrypto_tdes_padding_t padding_mode,
                                          const uint8_t *initial_iv_bytes,
                                          const uint8_t *message,
                                          size_t message_len) {
  size_t padded_len = 0;
  TRY(otcrypto_tdes_padded_plaintext_length(message_len, padding_mode,
                                            &padded_len));
  size_t expected_padded_len =
      message_len + kTdesBlockBytes - (message_len % kTdesBlockBytes);
  TRY_CHECK(padded_len == expected_padded_len);

  uint8_t ciphertext[48];
  uint8_t decrypted[48];
  TRY_CHECK(padded_len <= sizeof(ciphertext));

  uint32_t iv_words[kTdesBlockWords] = {0};
  if (initial_iv_bytes != NULL) {
    memcpy(iv_words, initial_iv_bytes, sizeof(iv_words));
  }
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

  otcrypto_const_byte_buf_t pt_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, message, message_len);
  otcrypto_byte_buf_t ct_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, padded_len);

  TRY(otcrypto_tdes(key, &iv, cipher_mode, kOtcryptoTdesOperationEncrypt,
                    &pt_in, padding_mode, &ct_out));

  // Reset IV for decryption.
  if (initial_iv_bytes != NULL) {
    memcpy(iv_words, initial_iv_bytes, sizeof(iv_words));
  }
  otcrypto_const_byte_buf_t ct_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, ciphertext, padded_len);
  otcrypto_byte_buf_t pt_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, padded_len);
  TRY(otcrypto_tdes(key, &iv, cipher_mode, kOtcryptoTdesOperationDecrypt,
                    &ct_in, padding_mode, &pt_out));

  size_t unpadded_len = 0;
  otcrypto_byte_buf_t padded_pt =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, padded_len);
  TRY(otcrypto_tdes_padding_strip(&padded_pt, padding_mode, &unpadded_len));
  TRY_CHECK(unpadded_len == message_len);
  if (message_len > 0) {
    TRY_CHECK_ARRAYS_EQ(decrypted, message, message_len);
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:7375` —
 *     `TEST_P(EncryptionOperationsTest, TripleDesEcbRoundTripSuccess)`
 *   - `KeyMintTest.cpp:7601` —
 *     `TEST_P(EncryptionOperationsTest, TripleDesCbcRoundTripSuccess)`
 */
static status_t tdes_ecb_cbc_round_trip_success_test(void) {
  LOG_INFO(
      "Testing TripleDesEcbRoundTripSuccess & TripleDesCbcRoundTripSuccess");
  const uint8_t kMessage[64] =
      "1234567890123456789012345678901234567890123456789012345678901234";
  uint8_t ciphertext[sizeof(kMessage)];
  uint8_t decrypted[sizeof(kMessage)];

  otcrypto_tdes_mode_t cipher_modes[2] = {kOtcryptoTdesModeEcb,
                                          kOtcryptoTdesModeCbc};
  otcrypto_key_mode_t key_modes[2] = {kOtcryptoKeyModeTdesEcb,
                                      kOtcryptoKeyModeTdesCbc};

  for (size_t m = 0; m < ARRAYSIZE(cipher_modes); ++m) {
    uint32_t keyblob[2 * kTdesKeyWords];
    otcrypto_blinded_key_t key;
    build_tdes_key(kDefaultKeyBytes, key_modes[m], keyblob, &key);

    uint32_t iv_words[kTdesBlockWords];
    memcpy(iv_words, kDefaultIvBytes, sizeof(iv_words));
    otcrypto_word32_buf_t iv =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

    otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, kMessage, sizeof(kMessage));
    otcrypto_byte_buf_t ct_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, sizeof(ciphertext));
    TRY(otcrypto_tdes(&key, &iv, cipher_modes[m], kOtcryptoTdesOperationEncrypt,
                      &pt_in, kOtcryptoTdesPaddingNull, &ct_out));

    // Decrypt block-by-block (8 bytes at a time); in CBC mode `iv` is updated
    // in-place after each block.
    memcpy(iv_words, kDefaultIvBytes, sizeof(iv_words));
    for (size_t offset = 0; offset < sizeof(kMessage);
         offset += kTdesBlockBytes) {
      otcrypto_const_byte_buf_t block_ct = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, ciphertext + offset, kTdesBlockBytes);
      otcrypto_byte_buf_t block_pt = OTCRYPTO_MAKE_BUF(
          otcrypto_byte_buf_t, decrypted + offset, kTdesBlockBytes);
      TRY(otcrypto_tdes(&key, &iv, cipher_modes[m],
                        kOtcryptoTdesOperationDecrypt, &block_ct,
                        kOtcryptoTdesPaddingNull, &block_pt));
    }
    TRY_CHECK_ARRAYS_EQ(decrypted, kMessage, sizeof(kMessage));
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:7420` —
 *     `TEST_P(EncryptionOperationsTest, TripleDesEcbPkcs7Padding)`
 *   - `KeyMintTest.cpp:7764` —
 *     `TEST_P(EncryptionOperationsTest, TripleDesCbcPkcs7Padding)`
 *
 * Verifies TDES PKCS#7 padding for all message lengths from 0 to 32 bytes
 * (`ciphertext.size() == i + 8 - (i % 8)`) in both ECB and CBC modes.
 */
static status_t tdes_ecb_cbc_pkcs7_padding_test(void) {
  LOG_INFO("Testing TripleDesEcbPkcs7Padding & TripleDesCbcPkcs7Padding");
  uint8_t message[32];
  for (size_t i = 0; i < sizeof(message); ++i) {
    message[i] = (uint8_t)i;
  }

  uint32_t keyblob[2 * kTdesKeyWords];
  otcrypto_blinded_key_t key;

  // ECB + PKCS#7 for lengths 0..32.
  build_tdes_key(kDefaultKeyBytes, kOtcryptoKeyModeTdesEcb, keyblob, &key);
  for (size_t len = 0; len <= sizeof(message); ++len) {
    TRY(run_tdes_padded_roundtrip(&key, kOtcryptoTdesModeEcb,
                                  kOtcryptoTdesPaddingPkcs7, NULL, message,
                                  len));
  }

  // CBC + PKCS#7 for lengths 0..32.
  build_tdes_key(kDefaultKeyBytes, kOtcryptoKeyModeTdesCbc, keyblob, &key);
  for (size_t len = 0; len <= sizeof(message); ++len) {
    TRY(run_tdes_padded_roundtrip(&key, kOtcryptoTdesModeCbc,
                                  kOtcryptoTdesPaddingPkcs7, kDefaultIvBytes,
                                  message, len));
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:7459` —
 *     `TEST_P(EncryptionOperationsTest, TripleDesEcbPkcs7PaddingCorrupted)`
 *   - `KeyMintTest.cpp:7810` —
 *     `TEST_P(EncryptionOperationsTest, TripleDesCbcPkcs7PaddingCorrupted)`
 *   - Android CTS `StrongboxDESede*CipherTest#testDecryptWithMangledPadding`
 *
 * Verifies that corrupted ciphertext and mangled PKCS#7 padding bytes in TDES
 * (`pad_byte == 0`, `pad_byte > 8`, or mismatched padding bytes) are rejected
 * with `OTCRYPTO_BAD_ARGS`.
 */
static status_t tdes_pkcs7_padding_corrupted_test(void) {
  LOG_INFO(
      "Testing TripleDesEcbPkcs7PaddingCorrupted & "
      "TripleDesCbcPkcs7PaddingCorrupted");
  const uint8_t kMessage[1] = {'a'};
  uint8_t ciphertext[kTdesBlockBytes];
  uint8_t decrypted[kTdesBlockBytes];

  otcrypto_tdes_mode_t cipher_modes[2] = {kOtcryptoTdesModeEcb,
                                          kOtcryptoTdesModeCbc};
  otcrypto_key_mode_t key_modes[2] = {kOtcryptoKeyModeTdesEcb,
                                      kOtcryptoKeyModeTdesCbc};

  for (size_t m = 0; m < ARRAYSIZE(cipher_modes); ++m) {
    uint32_t keyblob[2 * kTdesKeyWords];
    otcrypto_blinded_key_t key;
    build_tdes_key(kDefaultKeyBytes, key_modes[m], keyblob, &key);

    uint32_t iv_words[kTdesBlockWords];
    memcpy(iv_words, kDefaultIvBytes, sizeof(iv_words));
    otcrypto_word32_buf_t iv =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

    otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, kMessage, sizeof(kMessage));
    otcrypto_byte_buf_t ct_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, sizeof(ciphertext));
    TRY(otcrypto_tdes(&key, &iv, cipher_modes[m], kOtcryptoTdesOperationEncrypt,
                      &pt_in, kOtcryptoTdesPaddingPkcs7, &ct_out));

    bool failed_as_expected = false;
    for (size_t i = 0; i < 4; ++i) {
      ciphertext[sizeof(ciphertext) / 2]++;
      memcpy(iv_words, kDefaultIvBytes, sizeof(iv_words));
      otcrypto_const_byte_buf_t ct_in = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, ciphertext, sizeof(ciphertext));
      otcrypto_byte_buf_t pt_out =
          OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, sizeof(decrypted));
      TRY(otcrypto_tdes(&key, &iv, cipher_modes[m],
                        kOtcryptoTdesOperationDecrypt, &ct_in,
                        kOtcryptoTdesPaddingPkcs7, &pt_out));

      size_t unpadded_len = 0;
      otcrypto_byte_buf_t padded_pt =
          OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, sizeof(decrypted));
      otcrypto_status_t status = otcrypto_tdes_padding_strip(
          &padded_pt, kOtcryptoTdesPaddingPkcs7, &unpadded_len);
      if (status.value != OTCRYPTO_OK.value) {
        TRY_CHECK(status.value == OTCRYPTO_BAD_ARGS.value);
        failed_as_expected = true;
        break;
      }
    }
    TRY_CHECK(failed_as_expected);
  }

  // Direct mangled padding tests on an 8-byte TDES block.
  uint8_t block[kTdesBlockBytes];
  size_t unpadded_len = 0;
  otcrypto_byte_buf_t block_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, block, sizeof(block));

  memset(block, 0x00, sizeof(block));
  TRY_CHECK(otcrypto_tdes_padding_strip(&block_buf, kOtcryptoTdesPaddingPkcs7,
                                        &unpadded_len)
                .value == OTCRYPTO_BAD_ARGS.value);

  for (uint32_t bad_pad = kTdesBlockBytes + 1; bad_pad <= 0xff; ++bad_pad) {
    memset(block, (int)bad_pad, sizeof(block));
    TRY_CHECK(otcrypto_tdes_padding_strip(&block_buf, kOtcryptoTdesPaddingPkcs7,
                                          &unpadded_len)
                  .value == OTCRYPTO_BAD_ARGS.value);
  }

  for (size_t pad_len = 2; pad_len <= kTdesBlockBytes; ++pad_len) {
    for (size_t corrupt_idx = kTdesBlockBytes - pad_len;
         corrupt_idx < kTdesBlockBytes - 1; ++corrupt_idx) {
      memset(block, 'A', kTdesBlockBytes - pad_len);
      memset(block + kTdesBlockBytes - pad_len, (int)pad_len, pad_len);
      block[corrupt_idx] ^= 0x01;
      TRY_CHECK(otcrypto_tdes_padding_strip(
                    &block_buf, kOtcryptoTdesPaddingPkcs7, &unpadded_len)
                    .value == OTCRYPTO_BAD_ARGS.value);
    }
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:7633` —
 *     `TEST_P(EncryptionOperationsTest, TripleDesInvalidCallerIv)`
 *   - `KeyMintTest.cpp:7652` —
 *     `TEST_P(EncryptionOperationsTest, TripleDesCallerIv)`
 *   - `KeyMintTest.cpp:7737` —
 *     `EncryptionOperationsTest.TripleDesEcbCbcNoPaddingWrongInputSize`
 */
static status_t tdes_wrong_input_size_and_caller_iv_test(void) {
  LOG_INFO(
      "Testing TripleDesEcbCbcNoPaddingWrongInputSize & TripleDesCallerIv");
  const uint8_t kMessage31B[31] = "1234567890123456789012345678901";
  uint8_t output[32];

  otcrypto_tdes_mode_t cipher_modes[2] = {kOtcryptoTdesModeEcb,
                                          kOtcryptoTdesModeCbc};
  otcrypto_key_mode_t key_modes[2] = {kOtcryptoKeyModeTdesEcb,
                                      kOtcryptoKeyModeTdesCbc};

  for (size_t m = 0; m < ARRAYSIZE(cipher_modes); ++m) {
    uint32_t keyblob[2 * kTdesKeyWords];
    otcrypto_blinded_key_t key;
    build_tdes_key(kDefaultKeyBytes, key_modes[m], keyblob, &key);

    uint32_t iv_words[kTdesBlockWords];
    memcpy(iv_words, kDefaultIvBytes, sizeof(iv_words));
    otcrypto_word32_buf_t iv =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

    otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, kMessage31B, sizeof(kMessage31B));
    otcrypto_byte_buf_t ct_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, output, sizeof(output));

    TRY_CHECK(otcrypto_tdes(&key, &iv, cipher_modes[m],
                            kOtcryptoTdesOperationEncrypt, &pt_in,
                            kOtcryptoTdesPaddingNull, &ct_out)
                  .value == OTCRYPTO_BAD_ARGS.value);
  }

  // Caller IV round-trip with PKCS#7 padding on 6-byte message ("123456").
  uint32_t keyblob[2 * kTdesKeyWords];
  otcrypto_blinded_key_t key;
  build_tdes_key(kDefaultKeyBytes, kOtcryptoKeyModeTdesCbc, keyblob, &key);
  const uint8_t kShortMsg[6] = {'1', '2', '3', '4', '5', '6'};
  const uint8_t kCallerIv[8] = {'1', '2', '3', '4', '5', '6', '7', '8'};
  TRY(run_tdes_padded_roundtrip(&key, kOtcryptoTdesModeCbc,
                                kOtcryptoTdesPaddingPkcs7, kCallerIv, kShortMsg,
                                sizeof(kShortMsg)));

  // `TripleDesInvalidCallerIv` (`KeyMintTest.cpp:7633`): 12-byte (3-word) IV
  // must be rejected with `OTCRYPTO_BAD_ARGS`.
  uint32_t invalid_iv_words[3] = {0x11223344, 0x55667788, 0x99aabbcc};
  otcrypto_word32_buf_t invalid_iv = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, invalid_iv_words, ARRAYSIZE(invalid_iv_words));
  uint8_t block_in[kTdesBlockBytes] = {0};
  uint8_t block_out[kTdesBlockBytes] = {0};
  otcrypto_const_byte_buf_t pt_block =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, block_in, sizeof(block_in));
  otcrypto_byte_buf_t ct_block =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, block_out, sizeof(block_out));
  TRY_CHECK(otcrypto_tdes(&key, &invalid_iv, kOtcryptoTdesModeCbc,
                          kOtcryptoTdesOperationEncrypt, &pt_block,
                          kOtcryptoTdesPaddingNull, &ct_block)
                .value == OTCRYPTO_BAD_ARGS.value);
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:7506-7599` —
 *     `TEST_P(EncryptionOperationsTest, TripleDesTestVector)`
 *     (`kTripleDesTestVectors[0..9]`: NIST CAVP `TECBMMT3` & `TCBCMMT3` +
 *     PKCS#7 variant)
 *   - NIST SP 800-67 TDES-ECB test vector
 *
 * Verifies NIST SP 800-67 / CAVP MMT single-block and multi-block TDES-ECB and
 * TDES-CBC test vectors.
 */
static status_t tdes_kat_vectors_test(void) {
  LOG_INFO("Testing TripleDesTestVector");
  for (size_t i = 0; i < ARRAYSIZE(kTdesTestVectors); ++i) {
    const tdes_test_vector_t *vec = &kTdesTestVectors[i];
    otcrypto_key_mode_t key_mode = (vec->mode == kOtcryptoTdesModeEcb)
                                       ? kOtcryptoKeyModeTdesEcb
                                       : kOtcryptoKeyModeTdesCbc;
    uint32_t keyblob[2 * kTdesKeyWords];
    otcrypto_blinded_key_t key;
    build_tdes_key(vec->key, key_mode, keyblob, &key);

    uint8_t ciphertext[32];
    uint8_t decrypted[32];
    uint32_t iv_words[kTdesBlockWords] = {0};
    if (vec->iv != NULL) {
      memcpy(iv_words, vec->iv, sizeof(iv_words));
    }
    otcrypto_word32_buf_t iv =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

    otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, vec->plaintext, vec->pt_len);
    otcrypto_byte_buf_t ct_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ciphertext, vec->ct_len);
    TRY(otcrypto_tdes(&key, &iv, vec->mode, kOtcryptoTdesOperationEncrypt,
                      &pt_in, vec->padding, &ct_out));
    TRY_CHECK_ARRAYS_EQ(ciphertext, vec->ciphertext, vec->ct_len);

    if (vec->iv != NULL) {
      memcpy(iv_words, vec->iv, sizeof(iv_words));
    }
    otcrypto_const_byte_buf_t ct_in =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, ciphertext, vec->ct_len);
    otcrypto_byte_buf_t pt_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, vec->ct_len);
    TRY(otcrypto_tdes(&key, &iv, vec->mode, kOtcryptoTdesOperationDecrypt,
                      &ct_in, vec->padding, &pt_out));
    if (vec->padding != kOtcryptoTdesPaddingNull) {
      size_t unpadded_len = 0;
      TRY(otcrypto_tdes_padding_strip(&pt_out, vec->padding, &unpadded_len));
      TRY_CHECK(unpadded_len == vec->pt_len);
    }
    TRY_CHECK_ARRAYS_EQ(decrypted, vec->plaintext, vec->pt_len);
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:7851` —
 *     `TEST_P(EncryptionOperationsTest, TripleDesCbcIncrementalNoPadding)`
 *
 * Verifies that encrypting in 8-byte blocks (updating IV in-place) produces
 * identical ciphertext to one-shot encryption for lengths 8..240 bytes.
 */
static status_t tdes_cbc_incremental_no_padding_test(void) {
  LOG_INFO("Testing TripleDesCbcIncrementalNoPadding");
  uint8_t message[240];
  for (size_t i = 0; i < sizeof(message); ++i) {
    message[i] = (uint8_t)(i & 0xff);
  }
  uint8_t ct_oneshot[sizeof(message)];
  uint8_t ct_incremental[sizeof(message)];
  uint8_t pt_decrypted[sizeof(message)];

  uint32_t keyblob[2 * kTdesKeyWords];
  otcrypto_blinded_key_t key;
  build_tdes_key(kDefaultKeyBytes, kOtcryptoKeyModeTdesCbc, keyblob, &key);

  for (size_t msg_len = kTdesBlockBytes; msg_len <= sizeof(message);
       msg_len += 3 * kTdesBlockBytes) {
    // 1. One-shot encrypt.
    uint32_t iv_words[kTdesBlockWords];
    memcpy(iv_words, kDefaultIvBytes, sizeof(iv_words));
    otcrypto_word32_buf_t iv =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

    otcrypto_const_byte_buf_t pt_in =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, message, msg_len);
    otcrypto_byte_buf_t ct_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ct_oneshot, msg_len);
    TRY(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeCbc,
                      kOtcryptoTdesOperationEncrypt, &pt_in,
                      kOtcryptoTdesPaddingNull, &ct_out));

    // 2. Block-by-block incremental encrypt.
    memcpy(iv_words, kDefaultIvBytes, sizeof(iv_words));
    for (size_t offset = 0; offset < msg_len; offset += kTdesBlockBytes) {
      otcrypto_const_byte_buf_t block_pt = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, message + offset, kTdesBlockBytes);
      otcrypto_byte_buf_t block_ct = OTCRYPTO_MAKE_BUF(
          otcrypto_byte_buf_t, ct_incremental + offset, kTdesBlockBytes);
      TRY(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeCbc,
                        kOtcryptoTdesOperationEncrypt, &block_pt,
                        kOtcryptoTdesPaddingNull, &block_ct));
    }
    TRY_CHECK_ARRAYS_EQ(ct_incremental, ct_oneshot, msg_len);

    // 3. One-shot decrypt of incrementally encrypted ciphertext.
    memcpy(iv_words, kDefaultIvBytes, sizeof(iv_words));
    otcrypto_const_byte_buf_t ct_in =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, ct_incremental, msg_len);
    otcrypto_byte_buf_t pt_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, pt_decrypted, msg_len);
    TRY(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeCbc,
                      kOtcryptoTdesOperationDecrypt, &ct_in,
                      kOtcryptoTdesPaddingNull, &pt_out));
    TRY_CHECK_ARRAYS_EQ(pt_decrypted, message, msg_len);
  }
  return OK_STATUS();
}

/**
 * Source:
 *   - `CipherTest.java:273-287` & `300-301` — `KAT_VECTORS` for
 *     `DESede/CBC/NoPadding`, `DESede/CBC/PKCS7Padding`,
 *     `DESede/ECB/NoPadding`, and `DESede/ECB/PKCS7Padding` using
 *     `DESede_KAT_KEY_BYTES`
 *   - `StrongboxDESedeCBCNoPaddingCipherTest.java` /
 *     `DESedeCBCNoPaddingCipherTest.java` (16B `DESede/CBC/NoPadding` KAT)
 *   - `BlockCipherTestBase.java:1202` — `testDecryptWithMissingPadding`
 */
static status_t tdes_cts_kat_vectors_test(void) {
  LOG_INFO(
      "Testing Android CTS CipherTest.java & StrongboxDESede*CipherTest "
      "DESede KAT vectors and padding validation");

  // Source: `CipherTest.java:300-301` — `DESede_KAT_KEY_BYTES`
  // ("5EBE2294ECD0E0F08EAB7690D2A6EE6926AE5CC854E36B6B").
  const uint8_t kCtsDesEdeKatKey[24] = {
      0x5e, 0xbe, 0x22, 0x94, 0xec, 0xd0, 0xe0, 0xf0, 0x8e, 0xab, 0x76, 0x90,
      0xd2, 0xa6, 0xee, 0x69, 0x26, 0xae, 0x5c, 0xc8, 0x54, 0xe3, 0x6b, 0x6b,
  };
  // Source: `CipherTest.java:273-276` — `KAT_VECTORS["DESede/CBC/NoPadding"]`.
  const uint8_t kCtsDesEdeCbcNoPadPt[32] = {
      0xea, 0xc1, 0xb7, 0x95, 0x9e, 0x1e, 0x23, 0xc1, 0x1d, 0xc4, 0xa0,
      0xe2, 0x33, 0xee, 0xdd, 0x99, 0xe5, 0xbf, 0x5d, 0xd3, 0x91, 0xa5,
      0xf1, 0x07, 0xd0, 0x06, 0x13, 0x3a, 0x9a, 0xf3, 0xe3, 0x85,
  };
  const uint8_t kCtsDesEdeCbcNoPadIv[8] = {
      0xec, 0xd8, 0x7b, 0xf9, 0xc4, 0x9f, 0x37, 0xdc,
  };
  const uint8_t kCtsDesEdeCbcNoPadCt[32] = {
      0x63, 0x25, 0x11, 0xc4, 0x66, 0x80, 0xd6, 0x08, 0x83, 0xa2, 0x28,
      0xe6, 0x2c, 0xd3, 0x12, 0x44, 0xad, 0x61, 0xb9, 0x87, 0xe8, 0xdf,
      0x79, 0x01, 0xda, 0xe0, 0xeb, 0x22, 0x0c, 0x83, 0x96, 0x89,
  };
  // Source: `CipherTest.java:277-280` —
  // `KAT_VECTORS["DESede/CBC/PKCS7Padding"]` &
  // `DESedeCBCNoPaddingCipherTest.java` (first 16B).
  const uint8_t kCtsDesEde16BPlaintext[16] = {
      0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,
      0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38,
  };
  const uint8_t kCtsDesEdeCbcPkcs7Iv[8] = {
      0xdf, 0xca, 0x36, 0x68, 0x48, 0xde, 0xa6, 0xbb,
  };
  const uint8_t kCtsDesEdeCbcPkcs7Ct[24] = {
      0xe7, 0x0b, 0xb5, 0x76, 0x1d, 0x79, 0x6d, 0x7b, 0x0e, 0xb4, 0x0b, 0x5b,
      0x60, 0xde, 0xb6, 0xa9, 0x72, 0x6f, 0x72, 0xd9, 0x7c, 0xf2, 0xad, 0xa4,
  };
  // Source: `CipherTest.java:281-286` — `KAT_VECTORS["DESede/ECB/NoPadding"]`
  // and `KAT_VECTORS["DESede/ECB/PKCS7Padding"]`.
  const uint8_t kCtsDesEdeEcbPkcs7Ct[24] = {
      0xad, 0xe1, 0x19, 0xf9, 0xe3, 0x5a, 0xb3, 0xe9, 0xad, 0xe1, 0x19, 0xf9,
      0xe3, 0x5a, 0xb3, 0xe9, 0x4b, 0xcb, 0x01, 0xbb, 0xc0, 0xd0, 0x55, 0x26,
  };

  const tdes_test_vector_t kCtsDesEdeVectors[] = {
      {kOtcryptoTdesModeCbc, kOtcryptoTdesPaddingNull,
       sizeof(kCtsDesEdeCbcNoPadPt), sizeof(kCtsDesEdeCbcNoPadCt),
       kCtsDesEdeKatKey, kCtsDesEdeCbcNoPadIv, kCtsDesEdeCbcNoPadPt,
       kCtsDesEdeCbcNoPadCt},
      {kOtcryptoTdesModeCbc, kOtcryptoTdesPaddingNull, 16, 16, kCtsDesEdeKatKey,
       kCtsDesEdeCbcPkcs7Iv, kCtsDesEde16BPlaintext, kCtsDesEdeCbcPkcs7Ct},
      {kOtcryptoTdesModeCbc, kOtcryptoTdesPaddingPkcs7,
       sizeof(kCtsDesEde16BPlaintext), sizeof(kCtsDesEdeCbcPkcs7Ct),
       kCtsDesEdeKatKey, kCtsDesEdeCbcPkcs7Iv, kCtsDesEde16BPlaintext,
       kCtsDesEdeCbcPkcs7Ct},
      {kOtcryptoTdesModeEcb, kOtcryptoTdesPaddingNull, 16, 16, kCtsDesEdeKatKey,
       NULL, kCtsDesEde16BPlaintext, kCtsDesEdeEcbPkcs7Ct},
      {kOtcryptoTdesModeEcb, kOtcryptoTdesPaddingPkcs7,
       sizeof(kCtsDesEde16BPlaintext), sizeof(kCtsDesEdeEcbPkcs7Ct),
       kCtsDesEdeKatKey, NULL, kCtsDesEde16BPlaintext, kCtsDesEdeEcbPkcs7Ct},
  };

  uint32_t keyblob[2 * kTdesKeyWords];
  otcrypto_blinded_key_t key;
  uint8_t out_buf[32] = {0};
  uint8_t dec_buf[32] = {0};
  uint32_t iv_words[kTdesBlockWords] = {0};
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

  for (size_t i = 0; i < ARRAYSIZE(kCtsDesEdeVectors); ++i) {
    const tdes_test_vector_t *vec = &kCtsDesEdeVectors[i];
    otcrypto_key_mode_t key_mode = (vec->mode == kOtcryptoTdesModeEcb)
                                       ? kOtcryptoKeyModeTdesEcb
                                       : kOtcryptoKeyModeTdesCbc;
    build_tdes_key(vec->key, key_mode, keyblob, &key);
    if (vec->iv != NULL) {
      memcpy(iv_words, vec->iv, sizeof(iv_words));
    } else {
      memset(iv_words, 0, sizeof(iv_words));
    }
    otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, vec->plaintext, vec->pt_len);
    otcrypto_byte_buf_t ct_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, out_buf, vec->ct_len);
    TRY(otcrypto_tdes(&key, &iv, vec->mode, kOtcryptoTdesOperationEncrypt,
                      &pt_in, vec->padding, &ct_out));
    TRY_CHECK_ARRAYS_EQ(out_buf, vec->ciphertext, vec->ct_len);

    if (vec->iv != NULL) {
      memcpy(iv_words, vec->iv, sizeof(iv_words));
    }
    otcrypto_const_byte_buf_t ct_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, vec->ciphertext, vec->ct_len);
    otcrypto_byte_buf_t pt_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, dec_buf, vec->ct_len);
    TRY(otcrypto_tdes(&key, &iv, vec->mode, kOtcryptoTdesOperationDecrypt,
                      &ct_in, vec->padding, &pt_out));
    if (vec->padding != kOtcryptoTdesPaddingNull) {
      size_t unpadded_len = 0;
      TRY(otcrypto_tdes_padding_strip(&pt_out, vec->padding, &unpadded_len));
      TRY_CHECK(unpadded_len == vec->pt_len);
    }
    TRY_CHECK_ARRAYS_EQ(dec_buf, vec->plaintext, vec->pt_len);
  }

  build_tdes_key(kDefaultKeyBytes, kOtcryptoKeyModeTdesCbc, keyblob, &key);
  uint8_t buf_in[kTdesBlockBytes] = {0};
  uint8_t buf_out[kTdesBlockBytes] = {0};
  otcrypto_const_byte_buf_t in_block =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, buf_in, sizeof(buf_in));
  otcrypto_byte_buf_t out_block =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, buf_out, sizeof(buf_out));

  // 1. Invalid padding enum must be rejected on
  // `otcrypto_tdes_padded_plaintext_length`, `otcrypto_tdes` Encrypt/Decrypt,
  // and `otcrypto_tdes_padding_strip`.
  otcrypto_tdes_padding_t invalid_padding = (otcrypto_tdes_padding_t)0xdeadbeef;
  size_t len_out = 0;
  TRY_CHECK(otcrypto_tdes_padded_plaintext_length(8, invalid_padding, &len_out)
                .value == OTCRYPTO_BAD_ARGS.value);
  TRY_CHECK(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeCbc,
                          kOtcryptoTdesOperationEncrypt, &in_block,
                          invalid_padding, &out_block)
                .value == OTCRYPTO_BAD_ARGS.value);
  TRY_CHECK(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeCbc,
                          kOtcryptoTdesOperationDecrypt, &in_block,
                          invalid_padding, &out_block)
                .value == OTCRYPTO_BAD_ARGS.value);
  TRY_CHECK(otcrypto_tdes_padding_strip(&out_block, invalid_padding, &len_out)
                .value == OTCRYPTO_BAD_ARGS.value);

  // 2. Non-multiple of 8B ciphertext rejected.
  otcrypto_const_byte_buf_t short_ct =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, buf_in, kTdesBlockBytes - 1);
  otcrypto_byte_buf_t short_pt =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, buf_out, kTdesBlockBytes - 1);
  TRY_CHECK(otcrypto_tdes(&key, &iv, kOtcryptoTdesModeCbc,
                          kOtcryptoTdesOperationDecrypt, &short_ct,
                          kOtcryptoTdesPaddingNull, &short_pt)
                .value == OTCRYPTO_BAD_ARGS.value);
  TRY_CHECK(otcrypto_tdes_padding_strip(&short_pt, kOtcryptoTdesPaddingPkcs7,
                                        &len_out)
                .value == OTCRYPTO_BAD_ARGS.value);

  return OK_STATUS();
}

typedef struct tdes_zero_input_case {
  otcrypto_key_mode_t key_mode;
  otcrypto_tdes_mode_t tdes_mode;
} tdes_zero_input_case_t;

static const tdes_zero_input_case_t kTdesZeroInputCases[] = {
    {kOtcryptoKeyModeTdesCbc, kOtcryptoTdesModeCbc},
    {kOtcryptoKeyModeTdesEcb, kOtcryptoTdesModeEcb},
};

static const tdes_zero_input_case_t *current_tdes_zero_case = NULL;

/**
 * Source:
 *   - `CipherTest.java:398` — `testEmptyPlaintextEncryptsAndDecrypts`
 *     (`DESede/CBC/NoPadding` and `DESede/ECB/NoPadding`)
 *
 * Verifies 0-byte unpadded TDES encryption succeeds with 0-byte output.
 */
static status_t tdes_cts_empty_plaintext_no_padding_test(void) {
  LOG_INFO(
      "Testing Android CTS CipherTest.testEmptyPlaintextEncryptsAndDecrypts "
      "(mode=0x%x)",
      current_tdes_zero_case->tdes_mode);
  uint32_t keyblob[2 * kTdesKeyWords];
  otcrypto_blinded_key_t key;
  uint32_t iv_words[kTdesBlockWords] = {0};
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));
  uint8_t dummy = 0;
  otcrypto_const_byte_buf_t empty_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, &dummy, 0);
  otcrypto_byte_buf_t empty_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, &dummy, 0);

  build_tdes_key(kDefaultKeyBytes, current_tdes_zero_case->key_mode, keyblob,
                 &key);
  TRY(otcrypto_tdes(&key, &iv, current_tdes_zero_case->tdes_mode,
                    kOtcryptoTdesOperationEncrypt, &empty_in,
                    kOtcryptoTdesPaddingNull, &empty_out));
  TRY(otcrypto_tdes(&key, &iv, current_tdes_zero_case->tdes_mode,
                    kOtcryptoTdesOperationDecrypt, &empty_in,
                    kOtcryptoTdesPaddingNull, &empty_out));
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));

  EXECUTE_TEST(result, tdes_ecb_cbc_round_trip_success_test);
  EXECUTE_TEST(result, tdes_ecb_cbc_pkcs7_padding_test);
  EXECUTE_TEST(result, tdes_pkcs7_padding_corrupted_test);
  EXECUTE_TEST(result, tdes_wrong_input_size_and_caller_iv_test);
  EXECUTE_TEST(result, tdes_kat_vectors_test);
  EXECUTE_TEST(result, tdes_cbc_incremental_no_padding_test);
  EXECUTE_TEST(result, tdes_cts_kat_vectors_test);
  for (size_t i = 0; i < ARRAYSIZE(kTdesZeroInputCases); ++i) {
    current_tdes_zero_case = &kTdesZeroInputCases[i];
    EXECUTE_TEST(result, tdes_cts_empty_plaintext_no_padding_test);
  }

  return status_ok(result);
}
