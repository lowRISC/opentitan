// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/aes_gcm/aes_gcm.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

typedef struct aes_gcm_test {
  // Key length.
  aes_key_len_t key_len;
  // IV and length (in bytes). If IV length is < 16 then the last bytes are
  // ignored.
  size_t iv_len;
  uint8_t iv[16];
  // Plaintext and length (in bytes). If the length is not a multiple of 4,
  // then the most significant bytes of the last word are ignored.
  size_t plaintext_len;
  uint8_t *plaintext;
  // Authenticated data and length (in bytes). If the length is not a multiple
  // of 4, then the most significant bytes of the last word are ignored.
  size_t aad_len;
  uint8_t *aad;
  // Expected authentication tag.
  uint8_t expected_tag[16];
  // Expected ciphertext (same length as plaintext).
  uint8_t *expected_ciphertext;
} aes_gcm_test_t;

/**
 * Randomly-generated 128-bit key for testing.
 */
static const uint32_t kKey128[4] = {
    // Key = f80a6e67211c873793a99d899c31c2e7
    0x676e0af8, 0x37871c21, 0x899da993, 0xe7c2319c};

/**
 * Randomly-generated 256-bit key for testing.
 */
static const uint32_t kKey256[8] = {
    // Key = 76592790eaf6630e670ce5784ff23a1806a1ea76b0977b1542374769247cc4ce
    0x90275976, 0x0e63f6ea, 0x78e50c67, 0x183af24f,
    0x76eaa106, 0x157b97b0, 0x69473742, 0xcec47c24};

/**
 * Authenticated data for testing.
 */
static const uint32_t kAadLen = 18;
static uint8_t kAad[20] = {
    // aad = 'authenticated data'
    //     = 61757468656e746963617465642064617461
    0x61, 0x75, 0x74, 0x68, 0x65, 0x6e, 0x74, 0x69, 0x63,
    0x61, 0x74, 0x65, 0x64, 0x20, 0x64, 0x61, 0x74, 0x61};

/**
 * Plaintext for testing.
 */
static const uint32_t kPlaintextLen = 32;
static uint8_t kPlaintext[32] = {
    // plaintext = 'authenticated and encrypted data'
    //           =
    //           61757468656e7469636174656420616e6420656e637279707465642064617461
    0x61, 0x75, 0x74, 0x68, 0x65, 0x6e, 0x74, 0x69, 0x63, 0x61, 0x74,
    0x65, 0x64, 0x20, 0x61, 0x6e, 0x64, 0x20, 0x65, 0x6e, 0x63, 0x72,
    0x79, 0x70, 0x74, 0x65, 0x64, 0x20, 0x64, 0x61, 0x74, 0x61};

/**
 * Expected ciphertext for the 256-bit key.
 */
static uint8_t kCiphertext256[32] = {
    // Ciphertext =
    // 4e6d3a963b076ba0945d29aa836f29b0fa06cdd575aab8233f1df93e80163371
    0x4e, 0x6d, 0x3a, 0x96, 0x3b, 0x07, 0x6b, 0xa0, 0x94, 0x5d, 0x29,
    0xaa, 0x83, 0x6f, 0x29, 0xb0, 0xfa, 0x06, 0xcd, 0xd5, 0x75, 0xaa,
    0xb8, 0x23, 0x3f, 0x1d, 0xf9, 0x3e, 0x80, 0x16, 0x33, 0x71};

static const aes_gcm_test_t kAesGcmTestvectors[3] = {
    // Empty input, empty aad, 96-bit IV, 128-bit key
    {
        .key_len = kAesKeyLen128,
        .iv_len = 12,
        .iv =
            {// IV = 22294cae82d82e44427dfcc3
             0x22, 0x29, 0x4c, 0xae, 0x82, 0xd8, 0x2e, 0x44, 0x42, 0x7d, 0xfc,
             0xc3},
        .plaintext_len = 0,
        .plaintext = NULL,
        .aad_len = 0,
        .aad = NULL,
        .expected_tag =
            {// Tag = b7aa223a6c75a0976633ce79d9fddf06
             0xb7, 0xaa, 0x22, 0x3a, 0x6c, 0x75, 0xa0, 0x97, 0x66, 0x33, 0xce,
             0x79, 0xd9, 0xfd, 0xdf, 0x06},
        .expected_ciphertext = NULL,
    },

    // Empty input, empty aad, 128-bit IV, 128-bit key
    {
        .key_len = kAesKeyLen128,
        .iv_len = 16,
        .iv =
            {// IV = 22294cae82d82e44427dfcc33bacdbec
             0x22, 0x29, 0x4c, 0xae, 0x82, 0xd8, 0x2e, 0x44, 0x42, 0x7d, 0xfc,
             0xc3, 0x3b, 0xac, 0xdb, 0xec},
        .plaintext_len = 0,
        .plaintext = NULL,
        .aad_len = 0,
        .aad = NULL,
        .expected_tag =
            {// Tag = 4c59f0d420d9eb8669c40ad23b5419ba
             0x4c, 0x59, 0xf0, 0xd4, 0x20, 0xd9, 0xeb, 0x86, 0x69, 0xc4, 0x0a,
             0xd2, 0x3b, 0x54, 0x19, 0xba},
        .expected_ciphertext = NULL,
    },

    // 128-bit IV, 256-bit key, real message and aad
    {
        .key_len = kAesKeyLen256,
        .iv_len = 16,
        .iv =
            {// IV = c58aded2e1bbecba8b16a5757e5475bd
             0xc5, 0x8a, 0xde, 0xd2, 0xe1, 0xbb, 0xec, 0xba, 0x8b, 0x16, 0xa5,
             0x75, 0x7e, 0x54, 0x75, 0xbd},
        .plaintext_len = kPlaintextLen,
        .plaintext = kPlaintext,
        .aad_len = kAadLen,
        .aad = kAad,
        .expected_tag =
            {// Tag = 324895b3d2f656e4fa2f8ce056137061
             0x32, 0x48, 0x95, 0xb3, 0xd2, 0xf6, 0x56, 0xe4, 0xfa, 0x2f, 0x8c,
             0xe0, 0x56, 0x13, 0x70, 0x61},
        .expected_ciphertext = kCiphertext256,
    },
};

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  for (size_t i = 0; i < ARRAYSIZE(kAesGcmTestvectors); i++) {
    LOG_INFO("Starting AES-GCM test %d of %d...", i + 1,
             ARRAYSIZE(kAesGcmTestvectors));
    const aes_gcm_test_t test = kAesGcmTestvectors[i];

    // Construct key shares by setting first share to full key and second share
    // to 0. (Note: this is not a secure construction! But it makes debugging
    // tests easier because there is only one thing to print.)
    const uint32_t *key_shares[2];
    const uint32_t share1[8] = {0};
    key_shares[1] = share1;
    if (test.key_len == kAesKeyLen128) {
      key_shares[0] = kKey128;
    } else if (test.key_len == kAesKeyLen256) {
      key_shares[0] = kKey256;
    } else {
      LOG_ERROR("No key available for key length.");
      return false;
    }

    // Call AES-GCM encrypt.
    uint8_t actual_ciphertext[test.plaintext_len];
    uint8_t actual_tag[16];
    uint64_t start = ibex_mcycle_read();
    aes_error_t err = aes_gcm_encrypt(
        test.key_len, key_shares, test.iv_len, test.iv, test.plaintext_len,
        test.plaintext, test.aad_len, test.aad, actual_ciphertext, actual_tag);
    uint64_t end = ibex_mcycle_read();
    uint32_t cycles = end - start;
    LOG_INFO("aes_gcm_encrypt() took %u cycles", cycles);
    CHECK(err == kAesOk, "AES-GCM encryption returned an error: %08x", err);

    CHECK_ARRAYS_EQ(actual_tag, test.expected_tag, sizeof(test.expected_tag));
    if (test.plaintext_len > 0) {
      CHECK_ARRAYS_EQ(actual_ciphertext, test.expected_ciphertext,
                      test.plaintext_len);
    }

    LOG_INFO("Finished AES-GCM test %d.", i + 1);
  }

  return true;
}
