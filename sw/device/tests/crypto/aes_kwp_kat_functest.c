// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/impl/aes_kwp/aes_kwp.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Buffer with 256 bits of zeroes to use for the second shares of AES keys.
static const uint32_t kZero[256 / 32] = {0, 0, 0, 0, 0, 0, 0, 0};

/**
 * Construct an AES key struct for AES-KWP from a raw word buffer.
 *
 * @param key Wrapping key data.
 * @param key_words Wrapping key length in 32-bit words.
 * @return Constructed AES key.
 */
static aes_key_t make_aes_key(const uint32_t *key, size_t key_words) {
  return (aes_key_t){
      .mode = kAesCipherModeEcb,
      .sideload = kHardenedBoolFalse,
      .key_len = key_words,
      .key_shares = {key, kZero},
  };
}

/**
 * Run an AES-KWP encryption known-answer test.
 *
 * This test uses the internal AES-KWP implementation rather than the cryptolib
 * API, since the cryptolib API pre-formats the key input and stores
 * configuration information along with the key, which makes it insuitable for
 * known-answer tests.
 *
 * @param kek Key to wrap with (key encryption key).
 * @param kek_words Length of the key encryption key in 32-bit words.
 * @param ptext Key material to wrap.
 * @param ptext_bytes Length of plaintext in bytes.
 * @param ctext Expected ciphertext.
 * @param ctext_words Length of expected ciphertext in 32-bit words.
 */
static status_t aes_kwp_wrap_kat(const uint32_t *kek, size_t kek_words,
                                 const uint32_t *ptext, size_t ptext_bytes,
                                 const uint32_t *ctext, size_t ctext_words) {
  // Construct an AES key.
  aes_key_t aes_kek = make_aes_key(kek, kek_words);

  // Run key wrapping and check the result.
  uint32_t act_ctext[ctext_words + 1];
  act_ctext[ctext_words] = 0xffffffff;
  TRY(aes_kwp_wrap(aes_kek, ptext, ptext_bytes, act_ctext));
  TRY_CHECK_ARRAYS_EQ(act_ctext, ctext, ctext_words);

  // Check that the last word of the "actual ciphertext" buffer is still the
  // same (i.e. the kwp routine did not write past the expected point).
  TRY_CHECK(act_ctext[ctext_words] == 0xffffffff);
  return OK_STATUS();
}

/**
 * Run an AES-KWP decryption known-answer test.
 *
 * This test uses the internal AES-KWP implementation rather than the cryptolib
 * API, since the cryptolib API pre-formats the key input and stores
 * configuration information along with the key, which makes it insuitable for
 * known-answer tests.
 *
 * @param kek Key to wrap with (key encryption key).
 * @param kek_words Length of the key encryption key in 32-bit words.
 * @param ctext Ciphertext.
 * @param ctext_words Length of expected ciphertext in 32-bit words.
 * @param valid Whether the ciphertext is valid or not.
 * @param ptext Expected plaintext (ignored if valid=false).
 * @param ptext_bytes Length of plaintext in bytes.
 */
static status_t aes_kwp_unwrap_kat(const uint32_t *kek, size_t kek_words,
                                   const uint32_t *ctext, size_t ctext_words,
                                   bool valid, const uint32_t *ptext,
                                   size_t ptext_bytes) {
  // Construct an AES key.
  aes_key_t aes_kek = make_aes_key(kek, kek_words);

  // Run key unwrapping.
  size_t ptext_words = (ptext_bytes + sizeof(uint32_t) - 1) / sizeof(uint32_t);
  uint32_t act_ptext[ptext_words];
  hardened_bool_t success;
  TRY(aes_kwp_unwrap(aes_kek, ctext, ctext_words * sizeof(uint32_t), &success,
                     act_ptext));

  // Check results.
  if (valid) {
    TRY_CHECK(success == kHardenedBoolTrue);
    TRY_CHECK_ARRAYS_EQ((unsigned char *)act_ptext, (unsigned char *)ptext,
                        ptext_bytes);
  } else {
    TRY_CHECK(success == kHardenedBoolFalse);
  }

  return OK_STATUS();
}

/**
 * Basic test with valid data and no padding.
 *
 * This test data was taken from the Wycheproof test set (kwp_test.json, test
 * ID 1).
 */
static status_t no_padding_test(void) {
  uint32_t kek[] = {0x6d48676f, 0x1944911e, 0x85c243cb, 0xeac1c709};
  uint32_t ptext[] = {0x2d63c08d, 0xe40bee92, 0x840240f7, 0x7082b010};
  uint32_t ctext[] = {0xa63fd68c, 0xeda58a78, 0xc83f75fa,
                      0x675a647d, 0x7c10142b, 0xe719453b};

  TRY(aes_kwp_wrap_kat(kek, ARRAYSIZE(kek), ptext, sizeof(ptext), ctext,
                       ARRAYSIZE(ctext)));
  return aes_kwp_unwrap_kat(kek, ARRAYSIZE(kek), ctext, ARRAYSIZE(ctext),
                            /*valid=*/true, ptext, sizeof(ptext));
}

/**
 * Basic test with valid data and padding.
 *
 * This test data was taken from the NIST CAVP test set (first test in the set
 * with plaintext_len=72 from KWP_AE_128.txt).
 */
static status_t needs_padding_test(void) {
  uint32_t kek[] = {0x0fe26578, 0x9a65213c, 0x620b69b4, 0xc43cdf9c};
  // Last word padded with 1 bits; these should be replaced with 0s during
  // padding.
  uint32_t ptext[] = {0xd44368bd, 0xc88d3720, 0xffffff96};
  size_t ptext_len = 9;
  uint32_t ctext[] = {0x56a9ec41, 0x7e04aad4, 0xfe4ecfb5,
                      0xe7619665, 0xc5f8b64d, 0x0035e264};

  TRY(aes_kwp_wrap_kat(kek, ARRAYSIZE(kek), ptext, ptext_len, ctext,
                       ARRAYSIZE(ctext)));
  return aes_kwp_unwrap_kat(kek, ARRAYSIZE(kek), ctext, ARRAYSIZE(ctext),
                            /*valid=*/true, ptext, ptext_len);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  EXECUTE_TEST(result, no_padding_test);
  EXECUTE_TEST(result, needs_padding_test);

  return status_ok(result);
}
