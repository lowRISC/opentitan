// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/sha2/hkdf.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

/**
 * Represents a test for HKDF.
 */
typedef struct hkdf_test_vector {
  otcrypto_key_mode_t hmac_key_mode;
  uint32_t *ikm;
  size_t ikm_bytelen;
  uint8_t *salt;
  size_t salt_bytelen;
  uint8_t *info;
  size_t info_bytelen;
  uint32_t *prk;
  size_t prk_wordlen;
  uint32_t *okm;
  size_t okm_bytelen;
} hkdf_test_vector_t;

static const uint32_t kTestMask[] = {
    0x8cb847c3, 0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049,
    0xfd463b63, 0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345,
    0xa7ebc3e3, 0x04b2a1b9, 0x764a9630, 0x78b8f9c5, 0x3f2a1d8e, 0x8cb847c3,
    0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049, 0xfd463b63,
    0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345, 0xa7ebc3e3,
    0x04b2a1b9, 0x764a9630, 0x78b8f9c5, 0x3f2a1d8e,
};

static status_t run_test(hkdf_test_vector_t *test) {
  if (test->ikm_bytelen > sizeof(kTestMask)) {
    return OUT_OF_RANGE();
  }

  otcrypto_key_config_t ikm_config = {
      .version = otcrypto_lib_version(),
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
  ikm.checksum = otcrypto_integrity_blinded_checksum(&ikm);

  otcrypto_key_config_t prk_config = {
      .version = otcrypto_lib_version(),
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

  otcrypto_key_config_t okm_config = {
      .version = otcrypto_lib_version(),
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

  otcrypto_const_byte_buf_t salt = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, test->salt, test->salt_bytelen);
  otcrypto_const_byte_buf_t info = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, test->info, test->info_bytelen);

  // 1. Test two-stage otbn_hkdf_extract + otbn_hkdf_expand
  TRY(otbn_hkdf_extract(&ikm, &salt, &prk));
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

  TRY(otbn_hkdf_expand(&prk, &info, &okm));
  uint32_t *okm_share0;
  uint32_t *okm_share1;
  TRY(keyblob_to_shares(&okm, &okm_share0, &okm_share1));
  uint32_t unmasked_okm[keyblob_share_num_words(okm_config)];
  for (size_t i = 0; i < ARRAYSIZE(unmasked_okm); i++) {
    unmasked_okm[i] = okm_share0[i] ^ okm_share1[i];
  }
  TRY_CHECK_ARRAYS_EQ((unsigned char *)unmasked_okm, (unsigned char *)test->okm,
                      test->okm_bytelen);

  // 2. Test all-in-one otbn_hkdf
  memset(okm_keyblob, 0, sizeof(okm_keyblob));
  TRY(otbn_hkdf(&ikm, &salt, &info, &okm));
  TRY(keyblob_to_shares(&okm, &okm_share0, &okm_share1));
  for (size_t i = 0; i < ARRAYSIZE(unmasked_okm); i++) {
    unmasked_okm[i] = okm_share0[i] ^ okm_share1[i];
  }
  TRY_CHECK_ARRAYS_EQ((unsigned char *)unmasked_okm, (unsigned char *)test->okm,
                      test->okm_bytelen);

  return OK_STATUS();
}

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

static status_t run_negative_tests(void) {
  LOG_INFO("Running OTBN HKDF BAD_ARGS negative tests.");

  otcrypto_key_config_t valid_ikm_cfg = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeHmacSha256,
      .key_length = 22,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  otcrypto_key_config_t valid_prk_cfg = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeHmacSha256,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  otcrypto_key_config_t valid_okm_cfg = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeAesCtr,
      .key_length = 42,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t ikm_blob[keyblob_num_words(valid_ikm_cfg)];
  otcrypto_blinded_key_t valid_ikm = {.config = valid_ikm_cfg,
                                      .keyblob_length = sizeof(ikm_blob),
                                      .keyblob = ikm_blob};
  valid_ikm.checksum = otcrypto_integrity_blinded_checksum(&valid_ikm);

  uint32_t prk_blob[keyblob_num_words(valid_prk_cfg)];
  otcrypto_blinded_key_t valid_prk = {.config = valid_prk_cfg,
                                      .keyblob_length = sizeof(prk_blob),
                                      .keyblob = prk_blob};
  valid_prk.checksum = otcrypto_integrity_blinded_checksum(&valid_prk);

  uint32_t okm_blob[keyblob_num_words(valid_okm_cfg)];
  otcrypto_blinded_key_t valid_okm = {.config = valid_okm_cfg,
                                      .keyblob_length = sizeof(okm_blob),
                                      .keyblob = okm_blob};
  valid_okm.checksum = otcrypto_integrity_blinded_checksum(&valid_okm);

  uint8_t dummy_data[] = {0x01};
  otcrypto_const_byte_buf_t valid_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, dummy_data, 1);
  otcrypto_const_byte_buf_t null_data_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 1);

  CHECK(otbn_hkdf_extract(&valid_ikm, &valid_buf, NULL).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otbn_hkdf_extract(&valid_ikm, &null_data_buf, &valid_prk).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otbn_hkdf_expand(&valid_prk, &valid_buf, NULL).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otbn_hkdf_expand(&valid_prk, &null_data_buf, &valid_okm).value ==
        OTCRYPTO_BAD_ARGS.value);

  otcrypto_key_config_t huge_okm_cfg = valid_okm_cfg;
  huge_okm_cfg.key_length = 8161;
  uint32_t huge_blob[keyblob_num_words(huge_okm_cfg)];
  otcrypto_blinded_key_t huge_okm = {.config = huge_okm_cfg,
                                     .keyblob_length = sizeof(huge_blob),
                                     .keyblob = huge_blob};
  huge_okm.checksum = otcrypto_integrity_blinded_checksum(&huge_okm);
  CHECK(otbn_hkdf_expand(&valid_prk, &valid_buf, &huge_okm).value ==
        OTCRYPTO_BAD_ARGS.value);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  status_t test_result = OK_STATUS();
  EXECUTE_TEST(test_result, rfc_test1);
  EXECUTE_TEST(test_result, rfc_test2);
  EXECUTE_TEST(test_result, rfc_test3);
  EXECUTE_TEST(test_result, run_negative_tests);
  return status_ok(test_result);
}
