// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hkdf.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

/**
 * Represents a test for HKDF.
 */
typedef struct hkdf_test_vector {
  /**
   * Key mode for HKDF (e.g. HMAC-256). Determines hash function.
   */
  otcrypto_key_mode_t hmac_key_mode;
  /**
   * Input key derivation key (called IKM in RFC 5869).
   */
  uint32_t *ikm;
  /**
   * Length of key derivation key in bytes.
   */
  size_t ikm_bytelen;
  /**
   * Salt value. May be NULL if `salt_bytelen` is 0.
   */
  uint8_t *salt;
  /**
   * Length of salt in bytes.
   */
  size_t salt_bytelen;
  /**
   * Context string. May be NULL if `salt_bytelen` is 0.
   */
  uint8_t *info;
  /**
   * Length of info in bytes.
   */
  size_t info_bytelen;
  /**
   * Expected value for the intermediate pseudo-random key.
   *
   * This is the output of the `extract` phase and the input for the `expand`
   * phase. Its length should be the same as the hash function digest length.
   * Some test vectors may not include an expected value for the PRK, so if
   * this pointer is NULL, the PRK will not be checked.
   */
  uint32_t *prk;
  /**
   * Length of pseudo-random key in 32-bit words.
   */
  size_t prk_wordlen;
  /**
   * Expected output derived key (called OKM in RFC 5869).
   */
  uint32_t *okm;
  /**
   * Length of derived key in bytes.
   */
  size_t okm_bytelen;
} hkdf_test_vector_t;

// Random value for masking, as large as the longest test key. This value
// should not affect the result.
static const uint32_t kTestMask[] = {
    0x8cb847c3, 0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049,
    0xfd463b63, 0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345,
    0xa7ebc3e3, 0x04b2a1b9, 0x764a9630, 0x78b8f9c5, 0x3f2a1d8e, 0x8cb847c3,
    0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049, 0xfd463b63,
    0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345, 0xa7ebc3e3,
    0x04b2a1b9, 0x764a9630, 0x78b8f9c5, 0x3f2a1d8e,
};

/**
 * Call HKDF through the API and check the result.
 *
 * @param test Test vector to run.
 * @return Result (OK or error).
 */
static status_t run_test(hkdf_test_vector_t *test) {
  if (test->ikm_bytelen > sizeof(kTestMask)) {
    // If we get this error, we probably just need to make `kTestMask` longer.
    return OUT_OF_RANGE();
  }

  // Construct the input key (IKM in the RFC terminology).
  otcrypto_key_config_t ikm_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = test->hmac_key_mode,
      .key_length = test->ikm_bytelen,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t ikm_keyblob[keyblob_num_words(ikm_config)];
  TRY(keyblob_from_key_and_mask(test->ikm, kTestMask, ikm_config, ikm_keyblob));
  otcrypto_blinded_key_t ikm = {
      .config = ikm_config,
      .keyblob = ikm_keyblob,
      .keyblob_length = sizeof(ikm_keyblob),
  };
  ikm.checksum = integrity_blinded_checksum(&ikm);

  // Construct a blinded key struct for the intermediate key (PRK).
  otcrypto_key_config_t prk_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = test->hmac_key_mode,
      .key_length = test->prk_wordlen * sizeof(uint32_t),
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t prk_keyblob[keyblob_num_words(prk_config)];
  otcrypto_blinded_key_t prk = {
      .config = prk_config,
      .keyblob = prk_keyblob,
      .keyblob_length = sizeof(prk_keyblob),
  };

  // Construct a blinded key struct for the output key (OKM). The key mode here
  // doesn't really matter, it just needs to be some symmetric key.
  otcrypto_key_config_t okm_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesCtr,
      .key_length = test->okm_bytelen,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t okm_keyblob[keyblob_num_words(okm_config)];
  otcrypto_blinded_key_t okm = {
      .config = okm_config,
      .keyblob = okm_keyblob,
      .keyblob_length = sizeof(okm_keyblob),
  };

  // Construct a buffer for the salt.
  otcrypto_const_byte_buf_t salt = {
      .data = test->salt,
      .len = test->salt_bytelen,
  };

  // Construct a buffer for the context info.
  otcrypto_const_byte_buf_t info = {
      .data = test->info,
      .len = test->info_bytelen,
  };

  // Run the "extract" stage of HKDF.
  TRY(otcrypto_hkdf_extract(&ikm, salt, &prk));

  // If the test includes an expected value of PRK, then check the value.
  if (test->prk != NULL) {
    uint32_t *prk_share0;
    uint32_t *prk_share1;
    TRY(keyblob_to_shares(&prk, &prk_share0, &prk_share1));
    uint32_t unmasked_prk[test->prk_wordlen];
    for (size_t i = 0; i < ARRAYSIZE(unmasked_prk); i++) {
      unmasked_prk[i] = prk_share0[i] ^ prk_share1[i];
    }
    TRY_CHECK_ARRAYS_EQ(unmasked_prk, test->prk, test->prk_wordlen);
  }

  // Run the "expand" stage of HKDF.
  TRY(otcrypto_hkdf_expand(&prk, info, &okm));

  // Unmask the output key value and compare to the expected value.
  uint32_t *okm_share0;
  uint32_t *okm_share1;
  TRY(keyblob_to_shares(&okm, &okm_share0, &okm_share1));
  uint32_t unmasked_okm[keyblob_share_num_words(okm_config)];
  for (size_t i = 0; i < ARRAYSIZE(unmasked_okm); i++) {
    unmasked_okm[i] = okm_share0[i] ^ okm_share1[i];
  }
  TRY_CHECK_ARRAYS_EQ((unsigned char *)unmasked_okm, (unsigned char *)test->okm,
                      test->okm_bytelen);
  return OK_STATUS();
}

/**
 * Test case 1 from RFC 5869:
 *
 * Basic test case with SHA-256
 *
 * Hash = SHA-256
 * IKM  = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (22 octets)
 * salt = 0x000102030405060708090a0b0c (13 octets)
 * info = 0xf0f1f2f3f4f5f6f7f8f9 (10 octets)
 * L    = 42
 *
 * PRK  = 0x077709362c2e32df0ddc3f0dc47bba63
 *        90b6c73bb50f9c3122ec844ad7c2b3e5 (32 octets)
 * OKM  = 0x3cb25f25faacd57a90434f64d0362f2a
 *        2d2d0a90cf1a5a4c5db02d56ecc4c5bf
 *        34007208d5b887185865 (42 octets)
 */
static status_t rfc_test1(void) {
  uint32_t ikm_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x00000b0b,
  };
  uint8_t salt_data[] = {
      0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
      0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
  };
  uint8_t info_data[] = {
      0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9,
  };
  uint32_t prk_data[] = {
      0x36097707, 0xdf322e2c, 0x0d3fdc0d, 0x63ba7bc4,
      0x3bc7b690, 0x319c0fb5, 0x4a84ec22, 0xe5b3c2d7,
  };
  uint32_t okm_data[] = {
      0x255fb23c, 0x7ad5acfa, 0x644f4390, 0x2a2f36d0, 0x900a2d2d, 0x4c5a1acf,
      0x562db05d, 0xbfc5c4ec, 0x08720034, 0x1887b8d5, 0x00006558,
  };
  hkdf_test_vector_t test = {
      .hmac_key_mode = kOtcryptoKeyModeHmacSha256,
      .ikm = ikm_data,
      .ikm_bytelen = 22,
      .salt = salt_data,
      .salt_bytelen = sizeof(salt_data),
      .info = info_data,
      .info_bytelen = sizeof(info_data),
      .prk = prk_data,
      .prk_wordlen = ARRAYSIZE(prk_data),
      .okm = okm_data,
      .okm_bytelen = 42,
  };
  return run_test(&test);
}

/**
 * Test case 2 from RFC 5869:
 *
 * Test with SHA-256 and longer inputs/outputs
 *
 * Hash = SHA-256
 * IKM  = 0x000102030405060708090a0b0c0d0e0f
 *        101112131415161718191a1b1c1d1e1f
 *        202122232425262728292a2b2c2d2e2f
 *        303132333435363738393a3b3c3d3e3f
 *        404142434445464748494a4b4c4d4e4f (80 octets)
 * salt = 0x606162636465666768696a6b6c6d6e6f
 *        707172737475767778797a7b7c7d7e7f
 *        808182838485868788898a8b8c8d8e8f
 *        909192939495969798999a9b9c9d9e9f
 *        a0a1a2a3a4a5a6a7a8a9aaabacadaeaf (80 octets)
 * info = 0xb0b1b2b3b4b5b6b7b8b9babbbcbdbebf
 *        c0c1c2c3c4c5c6c7c8c9cacbcccdcecf
 *        d0d1d2d3d4d5d6d7d8d9dadbdcdddedf
 *        e0e1e2e3e4e5e6e7e8e9eaebecedeeef
 *        f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff (80 octets)
 * L    = 82
 *
 * PRK  = 0x06a6b88c5853361a06104c9ceb35b45c
 *        ef760014904671014a193f40c15fc244 (32 octets)
 * OKM  = 0xb11e398dc80327a1c8e7f78c596a4934
 *        4f012eda2d4efad8a050cc4c19afa97c
 *        59045a99cac7827271cb41c65e590e09
 *        da3275600c2f09b8367793a9aca3db71
 *        cc30c58179ec3e87c14c01d5c1f3434f
 *        1d87 (82 octets)
 */
static status_t rfc_test2(void) {
  uint32_t ikm_data[] = {
      0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110,
      0x17161514, 0x1b1a1918, 0x1f1e1d1c, 0x23222120, 0x27262524,
      0x2b2a2928, 0x2f2e2d2c, 0x33323130, 0x37363534, 0x3b3a3938,
      0x3f3e3d3c, 0x43424140, 0x47464544, 0x4b4a4948, 0x4f4e4d4c,
  };
  uint8_t salt_data[] = {
      0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b,
      0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,
      0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f, 0x80, 0x81, 0x82, 0x83,
      0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f,
      0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b,
      0x9c, 0x9d, 0x9e, 0x9f, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
      0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf,
  };
  uint8_t info_data[] = {
      0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xbb,
      0xbc, 0xbd, 0xbe, 0xbf, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7,
      0xc8, 0xc9, 0xca, 0xcb, 0xcc, 0xcd, 0xce, 0xcf, 0xd0, 0xd1, 0xd2, 0xd3,
      0xd4, 0xd5, 0xd6, 0xd7, 0xd8, 0xd9, 0xda, 0xdb, 0xdc, 0xdd, 0xde, 0xdf,
      0xe0, 0xe1, 0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea, 0xeb,
      0xec, 0xed, 0xee, 0xef, 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7,
      0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff,
  };
  uint32_t prk_data[] = {
      0x8cb8a606, 0x1a365358, 0x9c4c1006, 0x5cb435eb,
      0x140076ef, 0x01714690, 0x403f194a, 0x44c25fc1,
  };
  uint32_t okm_data[] = {
      0x8d391eb1, 0xa12703c8, 0x8cf7e7c8, 0x34496a59, 0xda2e014f, 0xd8fa4e2d,
      0x4ccc50a0, 0x7ca9af19, 0x995a0459, 0x7282c7ca, 0xc641cb71, 0x090e595e,
      0x607532da, 0xb8092f0c, 0xa9937736, 0x71dba3ac, 0x81c530cc, 0x873eec79,
      0xd5014cc1, 0x4f43f3c1, 0x0000871d,

  };
  hkdf_test_vector_t test = {
      .hmac_key_mode = kOtcryptoKeyModeHmacSha256,
      .ikm = ikm_data,
      .ikm_bytelen = 80,
      .salt = salt_data,
      .salt_bytelen = sizeof(salt_data),
      .info = info_data,
      .info_bytelen = sizeof(info_data),
      .prk = prk_data,
      .prk_wordlen = ARRAYSIZE(prk_data),
      .okm = okm_data,
      .okm_bytelen = 82,
  };
  return run_test(&test);
}

/**
 * Test case 3 from RFC 5869:
 *
 *
 * Test with SHA-256 and zero-length salt/info
 *
 * Hash = SHA-256
 * IKM  = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (22 octets)
 * salt = (0 octets)
 * info = (0 octets)
 * L    = 42
 *
 * PRK  = 0x19ef24a32c717b167f33a91d6f648bdf
 *        96596776afdb6377ac434c1c293ccb04 (32 octets)
 * OKM  = 0x8da4e775a563c18f715f802a063c5a31
 *        b8a11f5c5ee1879ec3454e5f3c738d2d
 *        9d201395faa4b61a96c8 (42 octets)
 */
static status_t rfc_test3(void) {
  uint32_t ikm_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x00000b0b,
  };
  uint32_t prk_data[] = {
      0xa324ef19, 0x167b712c, 0x1da9337f, 0xdf8b646f,
      0x76675996, 0x7763dbaf, 0x1c4c43ac, 0x04cb3c29,
  };
  uint32_t okm_data[] = {
      0x75e7a48d, 0x8fc163a5, 0x2a805f71, 0x315a3c06, 0x5c1fa1b8, 0x9e87e15e,
      0x5f4e45c3, 0x2d8d733c, 0x9513209d, 0x1ab6a4fa, 0x0000c896,
  };
  hkdf_test_vector_t test = {
      .hmac_key_mode = kOtcryptoKeyModeHmacSha256,
      .ikm = ikm_data,
      .ikm_bytelen = 22,
      .salt = NULL,
      .salt_bytelen = 0,
      .info = NULL,
      .info_bytelen = 0,
      .prk = prk_data,
      .prk_wordlen = ARRAYSIZE(prk_data),
      .okm = okm_data,
      .okm_bytelen = 42,
  };
  return run_test(&test);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Start the entropy complex.
  CHECK_STATUS_OK(entropy_complex_init());

  status_t test_result = OK_STATUS();
  EXECUTE_TEST(test_result, rfc_test1);
  EXECUTE_TEST(test_result, rfc_test2);
  EXECUTE_TEST(test_result, rfc_test3);
  return status_ok(test_result);
}
