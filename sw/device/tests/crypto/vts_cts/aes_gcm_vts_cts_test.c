// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/aes_gcm.h"
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
 * Android KeyMint VTS (`EncryptionOperationsTest.AesGcm*`) and Android CTS
 * (`AES128GCMNoPaddingCipherTest`, `AES192GCMNoPaddingCipherTest`,
 * `AES256GCMNoPaddingCipherTest`, `AESGCMCipherTestBase`,
 * `BlockCipherTestBase`, `CipherTest`) conformance test suite for
 * `otcrypto_aes_gcm`.
 *
 * Upstream AOSP References:
 *   -
 * `hardware/interfaces/security/keymint/aidl/vts/functional/KeyMintTest.cpp`
 *     (lines 6278, 6369, 6486, 6876-7368)
 *   -
 * `cts/tests/tests/keystore/src/android/keystore/cts/AES128GCMNoPaddingCipherTest.java`
 *   -
 * `cts/tests/tests/keystore/src/android/keystore/cts/AES192GCMNoPaddingCipherTest.java`
 *   -
 * `cts/tests/tests/keystore/src/android/keystore/cts/AES256GCMNoPaddingCipherTest.java`
 *   -
 * `cts/tests/tests/keystore/src/android/keystore/cts/AESGCMCipherTestBase.java`
 *   -
 * `cts/tests/tests/keystore/src/android/keystore/cts/BlockCipherTestBase.java`
 *   - `cts/tests/tests/keystore/src/android/keystore/cts/CipherTest.java`
 *
 * Test Mapping:
 *   - `aes_gcm_kat_vectors_test`:
 *     - `AES128GCMNoPaddingCipherTest.java:21-34` (`KAT_KEY`, `KAT_IV`,
 *       `KAT_PLAINTEXT`, `KAT_CIPHERTEXT_WITHOUT_AAD`, `KAT_AAD`,
 *       `KAT_CIPHERTEXT_WITH_AAD`)
 *     - `AES192GCMNoPaddingCipherTest.java:21-34` (`KAT_KEY`, `KAT_IV`,
 *       `KAT_PLAINTEXT`, `KAT_CIPHERTEXT_WITHOUT_AAD`, `KAT_AAD`,
 *       `KAT_CIPHERTEXT_WITH_AAD`)
 *     - `AES256GCMNoPaddingCipherTest.java:21-34` (`KAT_KEY`, `KAT_IV`,
 *       `KAT_PLAINTEXT`, `KAT_CIPHERTEXT_WITHOUT_AAD`, `KAT_AAD`,
 *       `KAT_CIPHERTEXT_WITH_AAD`)
 *     - `CipherTest.java:187-191` (`KAT_VECTORS["AES/GCM/NoPadding"]`)
 *     - `TEST_P(EncryptionOperationsTest, AesGcmRoundTripSuccess)` (L6876)
 *     - `TEST_P(EncryptionOperationsTest, AesGcmDifferentNonces)` (L6967)
 *     - `TEST_P(EncryptionOperationsTest, AesGcmCorruptKey)` (L7085)
 *     - `TEST_P(EncryptionOperationsTest, AesGcmAadNoData)` (L7138)
 *     - `TEST_P(EncryptionOperationsTest, AesGcmBadAad)` (L7258)
 *     - `TEST_P(EncryptionOperationsTest, AesGcmWrongNonce)` (L7294)
 *     - `TEST_P(EncryptionOperationsTest, AesGcmCorruptTag)` (L7334)
 *     - `AESGCMCipherTestBase.java:189`
 *       (`testCiphertextBitflipDetectedWhenDecrypting`)
 *     - `AESGCMCipherTestBase.java:202`
 *       (`testAadBitflipDetectedWhenDecrypting`)
 *   - `aes_gcm_streaming_chunks_and_one_byte_test`:
 *     - `TEST_P(EncryptionOperationsTest, AesGcmIncremental)` (L6278)
 *     - `TEST_P(EncryptionOperationsTest, Aes128GCMNoPaddingOneByteAtATime)`
 *       (L6369)
 *     - `TEST_P(EncryptionOperationsTest, AesGcmMultiPartAad)` (L7181)
 *     - `AESGCMCipherTestBase.java:91`
 * (`testKatEncryptWithAadProvidedInChunks`)
 *     - `AESGCMCipherTestBase.java:126`
 *       (`testKatDecryptWithAadProvidedInChunks`)
 *     - `BlockCipherTestBase.java:783` (`testKatEncryptOneByteAtATime`)
 *     - `BlockCipherTestBase.java:870` (`testKatDecryptOneByteAtATime`)
 *   - `aes_gcm_aad_out_of_order_test`:
 *     - `TEST_P(EncryptionOperationsTest, AesGcmAadOutOfOrder)` (L7225)
 */

enum {
  kAesGcmMaxKeyWords = 256 / 32,
  kAesGcmIvWords = 12 / sizeof(uint32_t),
};

static const uint32_t kKeyMask[kAesGcmMaxKeyWords] = {
    0x01234567, 0x89abcdef, 0x00010203, 0x04050607,
    0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617,
};

typedef struct gcm_kat_vector {
  const uint8_t *key;
  size_t key_len;
  const uint8_t *iv;
  size_t iv_len;
  const uint8_t *aad;
  size_t aad_len;
  const uint8_t *plaintext;
  size_t plaintext_len;
  const uint8_t *ciphertext;
  const uint8_t *tag;
  size_t tag_len;
  otcrypto_aes_gcm_tag_len_t tag_len_enum;
} gcm_kat_vector_t;

// Source: `AES128GCMNoPaddingCipherTest.java:21-34` &
// `KeyMintTest.cpp:7085-7130` (`AesGcmCorruptKey`):
static const uint8_t kCtsAes128GcmKey[16] = {
    0xba, 0x76, 0x35, 0x4f, 0x0a, 0xed, 0x6e, 0x8d,
    0x91, 0xf4, 0x5c, 0x4f, 0xf5, 0xa0, 0x62, 0xdb,
};
static const uint8_t kCtsAes128GcmIv[12] = {
    0xb7, 0x94, 0x37, 0xae, 0x08, 0xff, 0x35, 0x5d, 0x7d, 0x8a, 0x4d, 0x0f,
};
static const uint8_t kCtsAes128GcmPt[55] = {
    0x6d, 0x75, 0x96, 0xa8, 0xfd, 0x56, 0xce, 0xae, 0xc6, 0x1d, 0xe7,
    0x94, 0x09, 0x84, 0xb7, 0x73, 0x6f, 0xec, 0x44, 0xf5, 0x72, 0xaf,
    0xc3, 0xc8, 0x95, 0x2e, 0x4d, 0xc6, 0x54, 0x1e, 0x2b, 0xc6, 0xa7,
    0x02, 0xc4, 0x40, 0xa3, 0x76, 0x10, 0x98, 0x95, 0x43, 0xf6, 0x3f,
    0xed, 0xb0, 0x47, 0xca, 0x21, 0x73, 0xbc, 0x18, 0x58, 0x19, 0x44,
};
static const uint8_t kCtsAes128GcmCt[55] = {
    0xb3, 0xf6, 0x79, 0x9e, 0x8f, 0x93, 0x26, 0xf2, 0xdf, 0x1e, 0x80,
    0xfc, 0xd2, 0xcb, 0x16, 0xd7, 0x8c, 0x9d, 0xc7, 0xcc, 0x14, 0xbb,
    0x67, 0x78, 0x62, 0xdc, 0x6c, 0x63, 0x9b, 0x3a, 0x63, 0x38, 0xd2,
    0x4b, 0x31, 0x2d, 0x39, 0x89, 0xe5, 0x92, 0x0b, 0x5d, 0xbf, 0xc9,
    0x76, 0x76, 0x5e, 0xfb, 0xfe, 0x57, 0xbb, 0x38, 0x59, 0x40, 0xa7,
};
static const uint8_t kCtsAes128GcmTagNoAad[16] = {
    0xa4, 0x3b, 0xdf, 0x05, 0xbd, 0xda, 0xe3, 0xc9,
    0xd6, 0xa2, 0xfb, 0xbd, 0xfc, 0xc0, 0xcb, 0xa0,
};
// `KAT_AAD` in `AES128GCMNoPaddingCipherTest.java:29-30` (39 bytes):
static const uint8_t kCtsAes128GcmAad39B[39] = {
    0xd3, 0xbc, 0x74, 0x58, 0x91, 0x4f, 0x45, 0xd5, 0x6d, 0x5f,
    0xcf, 0xbb, 0x2e, 0xef, 0xf2, 0xdc, 0xc0, 0xe6, 0x20, 0xc1,
    0x22, 0x9d, 0x90, 0x90, 0x4e, 0x98, 0x93, 0x0e, 0xa7, 0x1a,
    0xa4, 0x3b, 0x68, 0x98, 0xf8, 0x46, 0xf3, 0x24, 0x4d,
};
static const uint8_t kCtsAes128GcmTagWithAad[16] = {
    0x0c, 0x10, 0x62, 0x64, 0xd8, 0x15, 0x06, 0xf8,
    0xda, 0xf9, 0xcd, 0x6a, 0x1c, 0x70, 0x98, 0x8c,
};

// Source: `AES192GCMNoPaddingCipherTest.java:21-34` &
// `KeyMintTest.cpp:6486` (`Aes192GCMNoPaddingOneByteAtATime`):
static const uint8_t kCtsAes192GcmKey[24] = {
    0x21, 0x33, 0x9f, 0xc1, 0xd0, 0x11, 0xab, 0xca, 0x65, 0xd5, 0x0c, 0xe2,
    0x36, 0x52, 0x30, 0x60, 0x3f, 0xd4, 0x7d, 0x07, 0xe8, 0x83, 0x0f, 0x6e,
};
static const uint8_t kCtsAes192GcmIv[12] = {
    0xd5, 0xfb, 0x14, 0x69, 0xa8, 0xd8, 0x1d, 0xd7, 0x52, 0x86, 0xa4, 0x18,
};
static const uint8_t kCtsAes192GcmPt[33] = {
    0xcf, 0x77, 0x6d, 0xed, 0xf5, 0x3a, 0x82, 0x8d, 0x51, 0xa0, 0x07,
    0x3d, 0xb3, 0xef, 0x0d, 0xd1, 0xee, 0x19, 0xe2, 0xe9, 0xe2, 0x43,
    0xce, 0x97, 0xe9, 0x58, 0x41, 0xbb, 0x9a, 0xd4, 0xe3, 0xff, 0x52,
};
static const uint8_t kCtsAes192GcmCt[33] = {
    0x3a, 0x0d, 0x48, 0x27, 0x81, 0x11, 0xd3, 0x29, 0x6b, 0xc6, 0x63,
    0xdf, 0x8a, 0x5d, 0xbe, 0xb2, 0x47, 0x4e, 0xa4, 0x7f, 0xd8, 0x5b,
    0x60, 0x8f, 0x8d, 0x93, 0x75, 0xd9, 0xdc, 0xf7, 0xde, 0x14, 0x13,
};
static const uint8_t kCtsAes192GcmTagNoAad[16] = {
    0xad, 0x70, 0xfb, 0x0e, 0x19, 0x70, 0x66, 0x90,
    0x95, 0xad, 0x77, 0xeb, 0xb5, 0x97, 0x4a, 0xe8,
};
// `KAT_AAD` in `AES192GCMNoPaddingCipherTest.java:29-30` (31 bytes):
static const uint8_t kCtsAes192GcmAad31B[31] = {
    0x04, 0xcd, 0xc1, 0xd8, 0x40, 0xc1, 0x7d, 0xcf, 0xcc, 0xf7, 0x8b,
    0x3d, 0x79, 0x24, 0x63, 0x74, 0x0c, 0xe0, 0xbf, 0xdc, 0x16, 0x7b,
    0x98, 0xa6, 0x32, 0xe1, 0x44, 0xca, 0xfe, 0x96, 0x63,
};
static const uint8_t kCtsAes192GcmTagWithAad[16] = {
    0x80, 0x71, 0x8b, 0x9f, 0x6c, 0x02, 0x3f, 0xb0,
    0x91, 0xc7, 0x68, 0x91, 0xa9, 0x16, 0x83, 0xe2,
};

// Source: `AES256GCMNoPaddingCipherTest.java:21-34`:
static const uint8_t kCtsAes256GcmKey[32] = {
    0x79, 0x72, 0x14, 0x0d, 0x83, 0x1e, 0xed, 0xac, 0x75, 0xd5, 0xea,
    0x51, 0x5c, 0x9a, 0x4c, 0x3b, 0xb1, 0x24, 0x49, 0x9a, 0x90, 0xb5,
    0xf3, 0x17, 0xac, 0x1a, 0x68, 0x5e, 0x88, 0xfa, 0xe3, 0x95,
};
static const uint8_t kCtsAes256GcmIv[12] = {
    0xa6, 0x6c, 0x52, 0x52, 0x80, 0x8d, 0x82, 0x3d, 0xd4, 0x15, 0x1f, 0xed,
};
static const uint8_t kCtsAes256GcmPt[32] = {
    0xc2, 0xb9, 0xda, 0xbf, 0x3a, 0x55, 0xad, 0xaa, 0x94, 0xe8, 0xc0,
    0xd1, 0xe7, 0x7a, 0x84, 0xa3, 0x43, 0x5a, 0xee, 0x23, 0xb2, 0xc3,
    0xc4, 0xab, 0xb5, 0x87, 0xb0, 0x9a, 0x9c, 0x2a, 0xfb, 0xf0,
};
static const uint8_t kCtsAes256GcmCt[32] = {
    0xa9, 0x60, 0x61, 0x93, 0x14, 0x65, 0x7b, 0x2a, 0xfb, 0x96, 0xb9,
    0x3b, 0xeb, 0xb3, 0x72, 0xbf, 0xfd, 0x09, 0xe1, 0x9d, 0x53, 0xe3,
    0x51, 0xf1, 0x7d, 0x1b, 0xa2, 0x61, 0x1f, 0x9d, 0xc3, 0x3c,
};
static const uint8_t kCtsAes256GcmTagNoAad[16] = {
    0x9c, 0x92, 0xd5, 0x63, 0xe8, 0xfd, 0x38, 0x12,
    0x54, 0xac, 0x26, 0x2a, 0xa2, 0xa4, 0xea, 0x0d,
};
// `KAT_AAD` in `AES256GCMNoPaddingCipherTest.java:29-30` (48 bytes):
static const uint8_t kCtsAes256GcmAad48B[48] = {
    0x37, 0x27, 0x22, 0x9d, 0xb7, 0xa3, 0xcc, 0xda, 0x72, 0x83, 0xf6, 0x28,
    0xfb, 0x8a, 0x3c, 0xdf, 0x09, 0x3e, 0xa1, 0xf4, 0xe8, 0xbd, 0x1b, 0xc4,
    0x0a, 0x83, 0x0f, 0xc6, 0xdf, 0x6f, 0xb0, 0xe2, 0x49, 0x84, 0x5d, 0xd7,
    0xd4, 0x49, 0xb2, 0xbc, 0x3b, 0x5b, 0xa4, 0x22, 0x58, 0xfb, 0x92, 0xc7,
};
static const uint8_t kCtsAes256GcmTagWithAad[16] = {
    0x15, 0x01, 0xca, 0xa6, 0xcc, 0xa0, 0xa2, 0x81,
    0xf4, 0x2b, 0xc3, 0x10, 0xd1, 0xe4, 0x48, 0x8f,
};

// Source: `CipherTest.java:187-191` & `291-292` —
// `KAT_VECTORS["AES/GCM/NoPadding"]` with `AES128_KAT_KEY_BYTES`:
static const uint8_t kCtsCipherTestGcmKey[16] = {
    0x7d, 0x9f, 0x11, 0xa0, 0xda, 0x11, 0x1e, 0x9d,
    0x8b, 0xdd, 0x14, 0xf0, 0x46, 0x48, 0xed, 0x91,
};
static const uint8_t kCtsCipherTestGcmIv[12] = {
    0xf6, 0x7a, 0xaf, 0x97, 0xcd, 0xec, 0x65, 0xb1, 0x21, 0x88, 0x31, 0x5e,
};
static const uint8_t kCtsCipherTestGcmPt[34] = {
    0x03, 0x88, 0x9a, 0x6c, 0xa8, 0x11, 0xe3, 0xfd, 0x7e, 0x78, 0x46, 0x7e,
    0x3d, 0xae, 0x58, 0x7d, 0x21, 0x10, 0xe8, 0x0e, 0x98, 0xed, 0xbc, 0x9d,
    0xfe, 0x17, 0xaf, 0xba, 0x23, 0x8c, 0x4c, 0x49, 0x31, 0x86,
};
static const uint8_t kCtsCipherTestGcmCt[34] = {
    0x15, 0x9e, 0xb1, 0xff, 0xc8, 0x65, 0x89, 0xb3, 0x8f, 0x18, 0x09, 0x7c,
    0x32, 0xdb, 0x64, 0x6c, 0x7d, 0xe3, 0x52, 0x5b, 0x60, 0x38, 0x76, 0xc3,
    0xae, 0x67, 0x1b, 0xc2, 0xca, 0x52, 0xa5, 0x39, 0x5a, 0x37,
};
static const uint8_t kCtsCipherTestGcmTag[16] = {
    0x4b, 0x37, 0x7a, 0x91, 0x5c, 0x9e, 0xd1, 0xa3,
    0x49, 0xab, 0xf9, 0xfc, 0x54, 0xc9, 0xca, 0x81,
};

static const gcm_kat_vector_t kGcmVectors[] = {
    {kCtsAes128GcmKey, 16, kCtsAes128GcmIv, 12, NULL, 0, kCtsAes128GcmPt, 55,
     kCtsAes128GcmCt, kCtsAes128GcmTagNoAad, 16, kOtcryptoAesGcmTagLen128},
    {kCtsAes128GcmKey, 16, kCtsAes128GcmIv, 12, kCtsAes128GcmAad39B, 39,
     kCtsAes128GcmPt, 55, kCtsAes128GcmCt, kCtsAes128GcmTagWithAad, 16,
     kOtcryptoAesGcmTagLen128},
    {kCtsAes192GcmKey, 24, kCtsAes192GcmIv, 12, NULL, 0, kCtsAes192GcmPt, 33,
     kCtsAes192GcmCt, kCtsAes192GcmTagNoAad, 16, kOtcryptoAesGcmTagLen128},
    {kCtsAes192GcmKey, 24, kCtsAes192GcmIv, 12, kCtsAes192GcmAad31B, 31,
     kCtsAes192GcmPt, 33, kCtsAes192GcmCt, kCtsAes192GcmTagWithAad, 16,
     kOtcryptoAesGcmTagLen128},
    {kCtsAes256GcmKey, 32, kCtsAes256GcmIv, 12, NULL, 0, kCtsAes256GcmPt, 32,
     kCtsAes256GcmCt, kCtsAes256GcmTagNoAad, 16, kOtcryptoAesGcmTagLen128},
    {kCtsAes256GcmKey, 32, kCtsAes256GcmIv, 12, kCtsAes256GcmAad48B, 48,
     kCtsAes256GcmPt, 32, kCtsAes256GcmCt, kCtsAes256GcmTagWithAad, 16,
     kOtcryptoAesGcmTagLen128},
    {kCtsCipherTestGcmKey, 16, kCtsCipherTestGcmIv, 12, NULL, 0,
     kCtsCipherTestGcmPt, 34, kCtsCipherTestGcmCt, kCtsCipherTestGcmTag, 16,
     kOtcryptoAesGcmTagLen128},
};

/**
 * Helper to build a blinded AES-GCM key.
 */
static void build_gcm_key(const uint8_t *raw_key_bytes, size_t key_len,
                          uint32_t *keyblob, otcrypto_blinded_key_t *key) {
  size_t key_words = key_len / sizeof(uint32_t);
  uint32_t raw_words[kAesGcmMaxKeyWords] = {0};
  memcpy(raw_words, raw_key_bytes, key_len);
  for (size_t i = 0; i < key_words; ++i) {
    keyblob[i] = raw_words[i] ^ kKeyMask[i];
    keyblob[key_words + i] = kKeyMask[i];
  }
  key->config = (otcrypto_key_config_t){
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeAesGcm,
      .key_length = key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  key->keyblob_length = 2 * key_len;
  key->keyblob = keyblob;
  key->checksum = otcrypto_integrity_blinded_checksum(key);
}

/**
 * Source:
 *   - `AES128GCMNoPaddingCipherTest.java:21-34`
 *   - `AES192GCMNoPaddingCipherTest.java:21-34`
 *   - `AES256GCMNoPaddingCipherTest.java:21-34`
 *   - `CipherTest.java:187-191` (`KAT_VECTORS["AES/GCM/NoPadding"]`)
 *   - `AESGCMCipherTestBase.java:71-88` (`testKatEncryptWithAadProvidedInOneGo`
 *     & `testKatDecryptWithAadProvidedInOneGo`)
 *   - `AESGCMCipherTestBase.java:189-214`
 *     (`testCiphertextBitflipDetectedWhenDecrypting` &
 *      `testAadBitflipDetectedWhenDecrypting`)
 *   - `KeyMintTest.cpp:6876` —
 *     `TEST_P(EncryptionOperationsTest, AesGcmRoundTripSuccess)`
 *   - `KeyMintTest.cpp:6967` —
 *     `TEST_P(EncryptionOperationsTest, AesGcmDifferentNonces)`
 *   - `KeyMintTest.cpp:7085` —
 *     `TEST_P(EncryptionOperationsTest, AesGcmCorruptKey)`
 *   - `KeyMintTest.cpp:7138` —
 *     `TEST_P(EncryptionOperationsTest, AesGcmAadNoData)`
 *   - `KeyMintTest.cpp:7258` —
 *     `TEST_P(EncryptionOperationsTest, AesGcmBadAad)`
 *   - `KeyMintTest.cpp:7294` —
 *     `TEST_P(EncryptionOperationsTest, AesGcmWrongNonce)`
 *   - `KeyMintTest.cpp:7334` —
 *     `TEST_P(EncryptionOperationsTest, AesGcmCorruptTag)`
 */
static status_t aes_gcm_kat_vectors_test(void) {
  LOG_INFO("Testing AES-GCM Android CTS & KeyMint VTS KAT vectors");
  for (size_t i = 0; i < ARRAYSIZE(kGcmVectors); ++i) {
    const gcm_kat_vector_t *vec = &kGcmVectors[i];
    uint32_t keyblob[2 * kAesGcmMaxKeyWords];
    otcrypto_blinded_key_t key;
    build_gcm_key(vec->key, vec->key_len, keyblob, &key);

    uint32_t iv_words[kAesGcmIvWords];
    memcpy(iv_words, vec->iv, vec->iv_len);
    otcrypto_const_word32_buf_t iv = OTCRYPTO_MAKE_BUF(
        otcrypto_const_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

    otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, vec->plaintext, vec->plaintext_len);
    otcrypto_const_byte_buf_t aad_in =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, vec->aad, vec->aad_len);

    uint8_t actual_ct[64] = {0};
    otcrypto_byte_buf_t ct_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, actual_ct, vec->plaintext_len);

    size_t tag_words = vec->tag_len / sizeof(uint32_t);
    uint32_t actual_tag_words[4] = {0};
    otcrypto_word32_buf_t tag_out =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, actual_tag_words, tag_words);

    TRY(otcrypto_aes_gcm_encrypt(&key, &pt_in, &iv, &aad_in, vec->tag_len_enum,
                                 &ct_out, &tag_out));
    TRY_CHECK_ARRAYS_EQ(actual_ct, vec->ciphertext, vec->plaintext_len);
    TRY_CHECK_ARRAYS_EQ((const uint8_t *)actual_tag_words, vec->tag,
                        vec->tag_len);

    // One-shot decrypt and verify tag (`testKatOneShotDecryptUsingDoFinal`).
    uint8_t actual_pt[64] = {0};
    otcrypto_const_byte_buf_t ct_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, vec->ciphertext, vec->plaintext_len);
    otcrypto_byte_buf_t pt_out =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, actual_pt, vec->plaintext_len);
    otcrypto_const_word32_buf_t expected_tag = OTCRYPTO_MAKE_BUF(
        otcrypto_const_word32_buf_t, actual_tag_words, tag_words);
    hardened_bool_t success = kHardenedBoolFalse;

    TRY(otcrypto_aes_gcm_decrypt(&key, &ct_in, &iv, &aad_in, vec->tag_len_enum,
                                 &expected_tag, &pt_out, &success));
    TRY_CHECK(success == kHardenedBoolTrue);
    TRY_CHECK_ARRAYS_EQ(actual_pt, vec->plaintext, vec->plaintext_len);

    // `AesGcmCorruptTag` (`KeyMintTest.cpp:7334`): corrupt tag and verify
    // decryption reports `kHardenedBoolFalse`.
    actual_tag_words[3] ^= 0x01000000;
    success = kHardenedBoolTrue;
    TRY(otcrypto_aes_gcm_decrypt(&key, &ct_in, &iv, &aad_in, vec->tag_len_enum,
                                 &expected_tag, &pt_out, &success));
    TRY_CHECK(success == kHardenedBoolFalse);
  }

  // `AESGCMCipherTestBase.java:189`
  // (`testCiphertextBitflipDetectedWhenDecrypting`) and `202`
  // (`testAadBitflipDetectedWhenDecrypting`):
  uint32_t vts_keyblob[2 * kAesGcmMaxKeyWords];
  otcrypto_blinded_key_t vts_key;
  build_gcm_key(kCtsAes128GcmKey, sizeof(kCtsAes128GcmKey), vts_keyblob,
                &vts_key);
  uint32_t vts_iv_words[kAesGcmIvWords];
  memcpy(vts_iv_words, kCtsAes128GcmIv, sizeof(kCtsAes128GcmIv));
  otcrypto_const_word32_buf_t vts_iv = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, vts_iv_words, ARRAYSIZE(vts_iv_words));
  uint32_t vts_tag_no_aad_words[4];
  memcpy(vts_tag_no_aad_words, kCtsAes128GcmTagNoAad, 16);
  otcrypto_const_word32_buf_t vts_tag_no_aad =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, vts_tag_no_aad_words, 4);
  uint32_t vts_tag_with_aad_words[4];
  memcpy(vts_tag_with_aad_words, kCtsAes128GcmTagWithAad, 16);
  otcrypto_const_word32_buf_t vts_tag_with_aad =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, vts_tag_with_aad_words, 4);
  otcrypto_const_byte_buf_t empty_aad =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  uint8_t vts_pt[55] = {0};
  otcrypto_byte_buf_t vts_pt_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, vts_pt, sizeof(vts_pt));
  hardened_bool_t vts_ok = kHardenedBoolTrue;

  uint8_t bitflip_ct[55];
  memcpy(bitflip_ct, kCtsAes128GcmCt, sizeof(bitflip_ct));
  bitflip_ct[sizeof(bitflip_ct) / 2] ^= 0x40;
  otcrypto_const_byte_buf_t bitflip_ct_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, bitflip_ct, 55);
  TRY(otcrypto_aes_gcm_decrypt(&vts_key, &bitflip_ct_in, &vts_iv, &empty_aad,
                               kOtcryptoAesGcmTagLen128, &vts_tag_no_aad,
                               &vts_pt_out, &vts_ok));
  TRY_CHECK(vts_ok == kHardenedBoolFalse);

  uint8_t bitflip_aad[39];
  memcpy(bitflip_aad, kCtsAes128GcmAad39B, sizeof(bitflip_aad));
  bitflip_aad[sizeof(bitflip_aad) / 3] ^= 0x02;
  otcrypto_const_byte_buf_t bitflip_aad_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, bitflip_aad, 39);
  otcrypto_const_byte_buf_t vts_ct =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kCtsAes128GcmCt, 55);
  vts_ok = kHardenedBoolTrue;
  TRY(otcrypto_aes_gcm_decrypt(&vts_key, &vts_ct, &vts_iv, &bitflip_aad_in,
                               kOtcryptoAesGcmTagLen128, &vts_tag_with_aad,
                               &vts_pt_out, &vts_ok));
  TRY_CHECK(vts_ok == kHardenedBoolFalse);

  // `AesGcmCorruptKey` (`KeyMintTest.cpp:7085-7130`): corrupt `key[0] = 0` ->
  // decryption authentication must fail (`vts_ok == kHardenedBoolFalse`).
  uint8_t bad_key_bytes[16];
  memcpy(bad_key_bytes, kCtsAes128GcmKey, sizeof(bad_key_bytes));
  bad_key_bytes[0] = 0;
  build_gcm_key(bad_key_bytes, sizeof(bad_key_bytes), vts_keyblob, &vts_key);
  vts_ok = kHardenedBoolTrue;
  TRY(otcrypto_aes_gcm_decrypt(&vts_key, &vts_ct, &vts_iv, &empty_aad,
                               kOtcryptoAesGcmTagLen128, &vts_tag_no_aad,
                               &vts_pt_out, &vts_ok));
  TRY_CHECK(vts_ok == kHardenedBoolFalse);

  // `AesGcmAadNoData` (`KeyMintTest.cpp:7138`): AAD = `"1234567890123456"`
  // (16B), 0-byte message.
  build_gcm_key(kCtsAes128GcmKey, sizeof(kCtsAes128GcmKey), vts_keyblob,
                &vts_key);
  const uint8_t kAad16B[16] = "1234567890123456";
  otcrypto_const_byte_buf_t aad16_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kAad16B, sizeof(kAad16B));
  otcrypto_const_byte_buf_t empty_pt_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  otcrypto_byte_buf_t empty_ct_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, NULL, 0);
  uint32_t aad_only_tag[4] = {0};
  otcrypto_word32_buf_t aad_only_tag_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, aad_only_tag, 4);
  TRY(otcrypto_aes_gcm_encrypt(&vts_key, &empty_pt_in, &vts_iv, &aad16_in,
                               kOtcryptoAesGcmTagLen128, &empty_ct_out,
                               &aad_only_tag_out));
  otcrypto_const_word32_buf_t aad_only_tag_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, aad_only_tag, 4);
  vts_ok = kHardenedBoolFalse;
  TRY(otcrypto_aes_gcm_decrypt(&vts_key, &empty_pt_in, &vts_iv, &aad16_in,
                               kOtcryptoAesGcmTagLen128, &aad_only_tag_in,
                               &empty_ct_out, &vts_ok));
  TRY_CHECK(vts_ok == kHardenedBoolTrue);

  // `AesGcmRoundTripSuccess` (`KeyMintTest.cpp:6876`), `AesGcmDifferentNonces`
  // (`KeyMintTest.cpp:6967`), `AesGcmBadAad` (`KeyMintTest.cpp:7258`), &
  // `AesGcmWrongNonce` (`KeyMintTest.cpp:7294`):
  const uint8_t kAadFoobar[6] = "foobar";
  const uint8_t kAadBarfoo[6] = "barfoo";
  const uint8_t kMsg36[36] = "123456789012345678901234567890123456";
  uint32_t nonce0[3] = {0x30303030, 0x30303030, 0x30303030};
  uint32_t nonce1[3] = {0x31313131, 0x31313131, 0x31313131};
  otcrypto_const_word32_buf_t n0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, nonce0, 3);
  otcrypto_const_word32_buf_t n1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, nonce1, 3);
  otcrypto_const_byte_buf_t aad_foobar =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kAadFoobar, 6);
  otcrypto_const_byte_buf_t aad_barfoo =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kAadBarfoo, 6);
  otcrypto_const_byte_buf_t pt36_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kMsg36, 36);
  uint8_t ct_n0[36] = {0};
  uint8_t ct_n1[36] = {0};
  uint8_t dec36[36] = {0};
  uint32_t tag_n0[4] = {0};
  uint32_t tag_n1[4] = {0};
  otcrypto_byte_buf_t ct_n0_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ct_n0, 36);
  otcrypto_byte_buf_t ct_n1_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ct_n1, 36);
  otcrypto_word32_buf_t tag_n0_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_n0, 4);
  otcrypto_word32_buf_t tag_n1_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_n1, 4);
  TRY(otcrypto_aes_gcm_encrypt(&vts_key, &pt36_in, &n0, &aad_foobar,
                               kOtcryptoAesGcmTagLen128, &ct_n0_out,
                               &tag_n0_out));
  TRY(otcrypto_aes_gcm_encrypt(&vts_key, &pt36_in, &n1, &aad_foobar,
                               kOtcryptoAesGcmTagLen128, &ct_n1_out,
                               &tag_n1_out));
  TRY_CHECK(memcmp(ct_n0, ct_n1, 36) != 0);

  // `AesGcmBadAad`: decrypting `ct_n0` with `"barfoo"` fails authentication.
  otcrypto_const_byte_buf_t ct_n0_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, ct_n0, 36);
  otcrypto_byte_buf_t dec36_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, dec36, 36);
  otcrypto_const_word32_buf_t tag_n0_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, tag_n0, 4);
  vts_ok = kHardenedBoolTrue;
  TRY(otcrypto_aes_gcm_decrypt(&vts_key, &ct_n0_in, &n0, &aad_barfoo,
                               kOtcryptoAesGcmTagLen128, &tag_n0_in, &dec36_out,
                               &vts_ok));
  TRY_CHECK(vts_ok == kHardenedBoolFalse);

  // `AesGcmWrongNonce`: decrypting `ct_n0` with `n1` fails authentication.
  vts_ok = kHardenedBoolTrue;
  TRY(otcrypto_aes_gcm_decrypt(&vts_key, &ct_n0_in, &n1, &aad_foobar,
                               kOtcryptoAesGcmTagLen128, &tag_n0_in, &dec36_out,
                               &vts_ok));
  TRY_CHECK(vts_ok == kHardenedBoolFalse);

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:6278` —
 *     `TEST_P(EncryptionOperationsTest, AesGcmIncremental)`
 *   - `KeyMintTest.cpp:6369` —
 *     `TEST_P(EncryptionOperationsTest, Aes128GCMNoPaddingOneByteAtATime)`
 *   - `KeyMintTest.cpp:7181` —
 *     `TEST_P(EncryptionOperationsTest, AesGcmMultiPartAad)`
 *   - `AESGCMCipherTestBase.java:91-158` —
 *     `testKatEncryptWithAadProvidedInChunks` &
 *     `testKatDecryptWithAadProvidedInChunks` (chunks 1, 8, 3, 7, 23)
 *   - `BlockCipherTestBase.java:783-915` —
 *     `testKatEncryptOneByteAtATime` & `testKatDecryptOneByteAtATime`
 */
static status_t aes_gcm_streaming_chunks_and_one_byte_test(void) {
  LOG_INFO(
      "Testing AES-GCM streaming (CTS chunked AAD {1,8,3,7,23}, 1-byte "
      "updates, and VTS AesGcmMultiPartAad)");
  uint32_t keyblob[2 * kAesGcmMaxKeyWords];
  otcrypto_blinded_key_t key;
  build_gcm_key(kCtsAes128GcmKey, sizeof(kCtsAes128GcmKey), keyblob, &key);

  uint32_t iv_words[kAesGcmIvWords];
  memcpy(iv_words, kCtsAes128GcmIv, sizeof(kCtsAes128GcmIv));
  otcrypto_const_word32_buf_t iv = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

  enum { kCtsPtLen = sizeof(kCtsAes128GcmPt) };

  // 1. `AESGCMCipherTestBase.java:91-158`
  // (`testKatEncryptWithAadProvidedInChunks` &
  //  `testKatDecryptWithAadProvidedInChunks`): AAD chunk sizes {1, 8, 3, 7,
  //  23}.
  const size_t kAadMaxChunkSizes[5] = {1, 8, 3, 7, 23};
  for (size_t s = 0; s < ARRAYSIZE(kAadMaxChunkSizes); ++s) {
    size_t max_chunk = kAadMaxChunkSizes[s];
    otcrypto_aes_gcm_context_t ctx;
    TRY(otcrypto_aes_gcm_encrypt_init(&key, &iv, &ctx));
    for (size_t offset = 0; offset < sizeof(kCtsAes128GcmAad39B);
         offset += max_chunk) {
      size_t chunk = sizeof(kCtsAes128GcmAad39B) - offset;
      if (chunk > max_chunk) {
        chunk = max_chunk;
      }
      otcrypto_const_byte_buf_t aad_chunk = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, kCtsAes128GcmAad39B + offset, chunk);
      TRY(otcrypto_aes_gcm_update_aad(&ctx, &aad_chunk));
    }
    uint8_t stream_ct[kCtsPtLen] = {0};
    size_t total_written = 0;
    otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, kCtsAes128GcmPt, kCtsPtLen);
    otcrypto_byte_buf_t ct_rem =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, stream_ct, sizeof(stream_ct));
    TRY(otcrypto_aes_gcm_update_encrypted_data(&ctx, &pt_in, &ct_rem,
                                               &total_written));
    size_t final_written = 0;
    uint32_t stream_tag_words[4] = {0};
    otcrypto_byte_buf_t ct_out_final =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, stream_ct + total_written,
                          sizeof(stream_ct) - total_written);
    otcrypto_word32_buf_t stream_tag_out = OTCRYPTO_MAKE_BUF(
        otcrypto_word32_buf_t, stream_tag_words, ARRAYSIZE(stream_tag_words));
    TRY(otcrypto_aes_gcm_encrypt_final(&ctx, kOtcryptoAesGcmTagLen128,
                                       &ct_out_final, &final_written,
                                       &stream_tag_out));
    total_written += final_written;
    TRY_CHECK(total_written == kCtsPtLen);
    TRY_CHECK_ARRAYS_EQ(stream_ct, kCtsAes128GcmCt, kCtsPtLen);
    TRY_CHECK_ARRAYS_EQ((const uint8_t *)stream_tag_words,
                        kCtsAes128GcmTagWithAad,
                        sizeof(kCtsAes128GcmTagWithAad));
  }

  // 2. `KeyMintTest.cpp:6369` (`Aes128GCMNoPaddingOneByteAtATime`) &
  // `BlockCipherTestBase.java:783-915` (`testKatEncryptOneByteAtATime` /
  // `testKatDecryptOneByteAtATime`): feed AAD and plaintext/ciphertext 1 byte
  // at a time!
  otcrypto_aes_gcm_context_t ctx;
  TRY(otcrypto_aes_gcm_decrypt_init(&key, &iv, &ctx));
  for (size_t i = 0; i < sizeof(kCtsAes128GcmAad39B); ++i) {
    otcrypto_const_byte_buf_t aad_1b = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, kCtsAes128GcmAad39B + i, 1);
    TRY(otcrypto_aes_gcm_update_aad(&ctx, &aad_1b));
  }

  uint8_t stream_pt[kCtsPtLen] = {0};
  size_t pt_written = 0;
  for (size_t i = 0; i < kCtsPtLen; ++i) {
    size_t step_written = 0;
    otcrypto_const_byte_buf_t ct_1b =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kCtsAes128GcmCt + i, 1);
    otcrypto_byte_buf_t pt_rem =
        OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, stream_pt + pt_written,
                          sizeof(stream_pt) - pt_written);
    TRY(otcrypto_aes_gcm_update_encrypted_data(&ctx, &ct_1b, &pt_rem,
                                               &step_written));
    pt_written += step_written;
  }

  size_t pt_final_written = 0;
  hardened_bool_t tag_valid = kHardenedBoolFalse;
  otcrypto_byte_buf_t pt_final_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, stream_pt + pt_written,
                        sizeof(stream_pt) - pt_written);
  uint32_t expected_tag_words[4];
  memcpy(expected_tag_words, kCtsAes128GcmTagWithAad, 16);
  otcrypto_const_word32_buf_t expected_tag_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, expected_tag_words, 4);
  TRY(otcrypto_aes_gcm_decrypt_final(&ctx, &expected_tag_in,
                                     kOtcryptoAesGcmTagLen128, &pt_final_buf,
                                     &pt_final_written, &tag_valid));
  pt_written += pt_final_written;
  TRY_CHECK(tag_valid == kHardenedBoolTrue);
  TRY_CHECK(pt_written == kCtsPtLen);
  TRY_CHECK_ARRAYS_EQ(stream_pt, kCtsAes128GcmPt, kCtsPtLen);

  // 3. `KeyMintTest.cpp:7181` (`AesGcmMultiPartAad`):
  // `UpdateAad("foo")` + `UpdateAad("foo")` + `Update(message)` -> decrypt with
  // single `UpdateAad("foofoo")`.
  const uint8_t kFoo[3] = "foo";
  const uint8_t kFoofoo[6] = "foofoo";
  const uint8_t kMsg36[36] = "123456789012345678901234567890123456";
  TRY(otcrypto_aes_gcm_encrypt_init(&key, &iv, &ctx));
  otcrypto_const_byte_buf_t foo_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kFoo, 3);
  TRY(otcrypto_aes_gcm_update_aad(&ctx, &foo_in));
  TRY(otcrypto_aes_gcm_update_aad(&ctx, &foo_in));
  uint8_t mp_ct[36] = {0};
  size_t mp_written = 0;
  size_t mp_final_written = 0;
  otcrypto_const_byte_buf_t msg36_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kMsg36, 36);
  otcrypto_byte_buf_t mp_ct_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, mp_ct, 36);
  TRY(otcrypto_aes_gcm_update_encrypted_data(&ctx, &msg36_in, &mp_ct_out,
                                             &mp_written));
  uint32_t mp_tag[4] = {0};
  otcrypto_word32_buf_t mp_tag_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, mp_tag, 4);
  otcrypto_byte_buf_t mp_ct_rem = OTCRYPTO_MAKE_BUF(
      otcrypto_byte_buf_t, mp_ct + mp_written, 36 - mp_written);
  TRY(otcrypto_aes_gcm_encrypt_final(&ctx, kOtcryptoAesGcmTagLen128, &mp_ct_rem,
                                     &mp_final_written, &mp_tag_out));
  TRY_CHECK(mp_written + mp_final_written == 36);

  uint8_t mp_pt[36] = {0};
  otcrypto_const_byte_buf_t foofoo_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kFoofoo, 6);
  otcrypto_const_byte_buf_t mp_ct_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, mp_ct, 36);
  otcrypto_byte_buf_t mp_pt_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, mp_pt, 36);
  otcrypto_const_word32_buf_t mp_tag_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, mp_tag, 4);
  tag_valid = kHardenedBoolFalse;
  TRY(otcrypto_aes_gcm_decrypt(&key, &mp_ct_in, &iv, &foofoo_in,
                               kOtcryptoAesGcmTagLen128, &mp_tag_in, &mp_pt_out,
                               &tag_valid));
  TRY_CHECK(tag_valid == kHardenedBoolTrue);
  TRY_CHECK_ARRAYS_EQ(mp_pt, kMsg36, 36);

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:7225` —
 *     `TEST_P(EncryptionOperationsTest, AesGcmAadOutOfOrder)`
 *
 * Verifies that AES-GCM fails with `OTCRYPTO_BAD_ARGS` when additional
 * authenticated data (`otcrypto_aes_gcm_update_aad`) is provided after
 * `otcrypto_aes_gcm_update_encrypted_data`.
 */
static status_t aes_gcm_aad_out_of_order_test(void) {
  LOG_INFO("Testing KeyMint VTS AesGcmAadOutOfOrder");

  uint32_t keyblob[2 * kAesGcmMaxKeyWords];
  otcrypto_blinded_key_t key;
  build_gcm_key(kCtsAes128GcmKey, sizeof(kCtsAes128GcmKey), keyblob, &key);

  uint32_t iv_words[kAesGcmIvWords];
  memcpy(iv_words, kCtsAes128GcmIv, sizeof(kCtsAes128GcmIv));
  otcrypto_const_word32_buf_t iv = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

  const uint8_t kFoo[3] = "foo";
  const uint8_t kMsg36[36] = "123456789012345678901234567890123456";
  uint8_t ct_buf[36] = {0};
  size_t step_len = 0;

  otcrypto_aes_gcm_context_t ctx;
  TRY(otcrypto_aes_gcm_encrypt_init(&key, &iv, &ctx));

  otcrypto_const_byte_buf_t foo_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kFoo, sizeof(kFoo));
  otcrypto_const_byte_buf_t msg_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kMsg36, sizeof(kMsg36));
  otcrypto_byte_buf_t ct_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ct_buf, sizeof(ct_buf));

  TRY(otcrypto_aes_gcm_update_aad(&ctx, &foo_in));
  TRY(otcrypto_aes_gcm_update_encrypted_data(&ctx, &msg_in, &ct_out,
                                             &step_len));

  // Calling `update_aad` after `update_encrypted_data` (`AesGcmAadOutOfOrder`,
  // `KeyMintTest.cpp:7245`) must fail with `OTCRYPTO_BAD_ARGS`.
  TRY_CHECK(otcrypto_aes_gcm_update_aad(&ctx, &foo_in).value ==
            OTCRYPTO_BAD_ARGS.value);

  return OK_STATUS();
}

/**
 * Source:
 *   - `CipherTest.java:398` — `testEmptyPlaintextEncryptsAndDecrypts`
 *     (`AES/GCM/NoPadding`, 0-byte plaintext and 0-byte AAD)
 *   - `KeyMintTest.cpp:842` —
 *     `TEST_P(NewKeyGenerationTest, AesGcmMinMacOutOfRange)`
 *   - `KeyMintTest.cpp:7024` —
 *     `TEST_P(EncryptionOperationsTest, AesGcmTooShortTag)`
 *
 * Verifies:
 *   1. 0-byte plaintext + 0-byte AAD AES-GCM encrypt/decrypt round-trip.
 *   2. 96-bit (`12`-byte) truncated tag verification on `kCtsAes128GcmKey`,
 *      `kCtsAes192GcmKey`, and `kCtsAes256GcmKey`.
 *   3. Tag lengths `< 96` bits (`kOtcryptoAesGcmTagLen64` /
 *      `kOtcryptoAesGcmTagLen32`) must be rejected with `OTCRYPTO_BAD_ARGS` per
 *      KeyMint VTS `AesGcmMinMacOutOfRange` / `AesGcmTooShortTag` (currently
 *      fails when `FIPS_MODE` is not defined in `aes_gcm.c:216-221`, which
 *      accepts 64-bit and 32-bit tags).
 */
static status_t aes_gcm_vts_cts_empty_and_min_tag_length_test(void) {
  LOG_INFO(
      "Testing Android CTS testEmptyPlaintextEncryptsAndDecrypts & KeyMint VTS "
      "AesGcmTooShortTag (< 96-bit tag rejection)");

  uint32_t keyblob[2 * kAesGcmMaxKeyWords];
  otcrypto_blinded_key_t key;
  build_gcm_key(kCtsAes128GcmKey, sizeof(kCtsAes128GcmKey), keyblob, &key);

  uint32_t iv_words[kAesGcmIvWords];
  memcpy(iv_words, kCtsAes128GcmIv, sizeof(kCtsAes128GcmIv));
  otcrypto_const_word32_buf_t iv = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, iv_words, ARRAYSIZE(iv_words));

  // 1. `CipherTest.java:398` (`testEmptyPlaintextEncryptsAndDecrypts`):
  // 0-byte plaintext AND 0-byte AAD.
  otcrypto_const_byte_buf_t empty_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  otcrypto_byte_buf_t empty_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, NULL, 0);
  uint32_t tag_words[4] = {0};
  otcrypto_word32_buf_t tag_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_words, 4);
  TRY(otcrypto_aes_gcm_encrypt(&key, &empty_in, &iv, &empty_in,
                               kOtcryptoAesGcmTagLen128, &empty_out, &tag_out));
  otcrypto_const_word32_buf_t tag_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, tag_words, 4);
  hardened_bool_t ok = kHardenedBoolFalse;
  TRY(otcrypto_aes_gcm_decrypt(&key, &empty_in, &iv, &empty_in,
                               kOtcryptoAesGcmTagLen128, &tag_in, &empty_out,
                               &ok));
  TRY_CHECK(ok == kHardenedBoolTrue);

  // 2. 96-bit (`12`-byte) truncated tag encrypt & decrypt on
  // `kCtsAes128GcmKey`, `kCtsAes192GcmKey`, and `kCtsAes256GcmKey`:
  otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kCtsAes128GcmPt, sizeof(kCtsAes128GcmPt));
  uint8_t ct_buf[sizeof(kCtsAes128GcmCt)] = {0};
  uint8_t dec_buf[sizeof(kCtsAes128GcmPt)] = {0};
  otcrypto_byte_buf_t ct_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ct_buf, sizeof(ct_buf));
  otcrypto_const_byte_buf_t ct_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, ct_buf, sizeof(ct_buf));
  otcrypto_byte_buf_t dec_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, dec_buf, sizeof(dec_buf));
  uint32_t tag96_words[3] = {0};
  otcrypto_word32_buf_t tag96_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag96_words, 3);
  otcrypto_const_word32_buf_t tag96_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, tag96_words, 3);
  TRY(otcrypto_aes_gcm_encrypt(&key, &pt_in, &iv, &empty_in,
                               kOtcryptoAesGcmTagLen96, &ct_out, &tag96_out));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)tag96_words, kCtsAes128GcmTagNoAad, 12);
  ok = kHardenedBoolFalse;
  TRY(otcrypto_aes_gcm_decrypt(&key, &ct_in, &iv, &empty_in,
                               kOtcryptoAesGcmTagLen96, &tag96_in, &dec_out,
                               &ok));
  TRY_CHECK(ok == kHardenedBoolTrue);
  TRY_CHECK_ARRAYS_EQ(dec_buf, kCtsAes128GcmPt, sizeof(kCtsAes128GcmPt));

  // AES-192 96-bit tag:
  uint32_t keyblob192[2 * kAesGcmMaxKeyWords];
  otcrypto_blinded_key_t key192;
  build_gcm_key(kCtsAes192GcmKey, sizeof(kCtsAes192GcmKey), keyblob192,
                &key192);
  uint32_t iv192_words[kAesGcmIvWords];
  memcpy(iv192_words, kCtsAes192GcmIv, sizeof(kCtsAes192GcmIv));
  otcrypto_const_word32_buf_t iv192 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, iv192_words, ARRAYSIZE(iv192_words));
  otcrypto_const_byte_buf_t pt192_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kCtsAes192GcmPt, sizeof(kCtsAes192GcmPt));
  otcrypto_byte_buf_t ct192_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ct_buf, sizeof(kCtsAes192GcmCt));
  otcrypto_const_byte_buf_t ct192_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, ct_buf, sizeof(kCtsAes192GcmCt));
  otcrypto_byte_buf_t dec192_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, dec_buf, sizeof(kCtsAes192GcmPt));
  TRY(otcrypto_aes_gcm_encrypt(&key192, &pt192_in, &iv192, &empty_in,
                               kOtcryptoAesGcmTagLen96, &ct192_out,
                               &tag96_out));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)tag96_words, kCtsAes192GcmTagNoAad, 12);
  ok = kHardenedBoolFalse;
  TRY(otcrypto_aes_gcm_decrypt(&key192, &ct192_in, &iv192, &empty_in,
                               kOtcryptoAesGcmTagLen96, &tag96_in, &dec192_out,
                               &ok));
  TRY_CHECK(ok == kHardenedBoolTrue);
  TRY_CHECK_ARRAYS_EQ(dec_buf, kCtsAes192GcmPt, sizeof(kCtsAes192GcmPt));

  // AES-256 96-bit tag:
  uint32_t keyblob256[2 * kAesGcmMaxKeyWords];
  otcrypto_blinded_key_t key256;
  build_gcm_key(kCtsAes256GcmKey, sizeof(kCtsAes256GcmKey), keyblob256,
                &key256);
  uint32_t iv256_words[kAesGcmIvWords];
  memcpy(iv256_words, kCtsAes256GcmIv, sizeof(kCtsAes256GcmIv));
  otcrypto_const_word32_buf_t iv256 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, iv256_words, ARRAYSIZE(iv256_words));
  otcrypto_const_byte_buf_t pt256_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kCtsAes256GcmPt, sizeof(kCtsAes256GcmPt));
  otcrypto_byte_buf_t ct256_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ct_buf, sizeof(kCtsAes256GcmCt));
  otcrypto_const_byte_buf_t ct256_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, ct_buf, sizeof(kCtsAes256GcmCt));
  otcrypto_byte_buf_t dec256_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, dec_buf, sizeof(kCtsAes256GcmPt));
  TRY(otcrypto_aes_gcm_encrypt(&key256, &pt256_in, &iv256, &empty_in,
                               kOtcryptoAesGcmTagLen96, &ct256_out,
                               &tag96_out));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)tag96_words, kCtsAes256GcmTagNoAad, 12);
  ok = kHardenedBoolFalse;
  TRY(otcrypto_aes_gcm_decrypt(&key256, &ct256_in, &iv256, &empty_in,
                               kOtcryptoAesGcmTagLen96, &tag96_in, &dec256_out,
                               &ok));
  TRY_CHECK(ok == kHardenedBoolTrue);
  TRY_CHECK_ARRAYS_EQ(dec_buf, kCtsAes256GcmPt, sizeof(kCtsAes256GcmPt));

  // 3. `KeyMintTest.cpp:842` (`AesGcmMinMacOutOfRange`), `7035`
  // (`AesGcmTooShortTag`), & `7045` (`AesGcmTooShortTagOnDecrypt`): tags
  // shorter than 96 bits (`kOtcryptoAesGcmTagLen64` /
  // `kOtcryptoAesGcmTagLen32`) must be rejected with `OTCRYPTO_BAD_ARGS` on
  // both encrypt and decrypt.
  uint32_t tag64_words[2] = {0};
  otcrypto_word32_buf_t tag64_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag64_words, 2);
  otcrypto_const_word32_buf_t tag64_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, tag64_words, 2);
  otcrypto_status_t enc_tag64_status =
      otcrypto_aes_gcm_encrypt(&key, &pt_in, &iv, &empty_in,
                               kOtcryptoAesGcmTagLen64, &ct_out, &tag64_out);
  otcrypto_status_t dec_tag64_status = otcrypto_aes_gcm_decrypt(
      &key, &ct_in, &iv, &empty_in, kOtcryptoAesGcmTagLen64, &tag64_in,
      &dec_out, &ok);

  uint32_t tag32_words[1] = {0};
  otcrypto_word32_buf_t tag32_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag32_words, 1);
  otcrypto_const_word32_buf_t tag32_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, tag32_words, 1);
  otcrypto_status_t enc_tag32_status =
      otcrypto_aes_gcm_encrypt(&key, &pt_in, &iv, &empty_in,
                               kOtcryptoAesGcmTagLen32, &ct_out, &tag32_out);
  otcrypto_status_t dec_tag32_status = otcrypto_aes_gcm_decrypt(
      &key, &ct_in, &iv, &empty_in, kOtcryptoAesGcmTagLen32, &tag32_in,
      &dec_out, &ok);
  TRY_CHECK(enc_tag64_status.value == OTCRYPTO_BAD_ARGS.value &&
            dec_tag64_status.value == OTCRYPTO_BAD_ARGS.value &&
            enc_tag32_status.value == OTCRYPTO_BAD_ARGS.value &&
            dec_tag32_status.value == OTCRYPTO_BAD_ARGS.value);

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));

  EXECUTE_TEST(result, aes_gcm_kat_vectors_test);
  EXECUTE_TEST(result, aes_gcm_streaming_chunks_and_one_byte_test);
  EXECUTE_TEST(result, aes_gcm_aad_out_of_order_test);
  EXECUTE_TEST(result, aes_gcm_vts_cts_empty_and_min_tag_length_test);

  return status_ok(result);
}
