// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_datatypes.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/profile.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

enum {
  kRsa4096CofactorNumWords = kRsa4096NumWords / 2,
};

static otcrypto_key_mode_t kTestKeyMode = kOtcryptoKeyModeRsaSignPss;

// Note: The private key and valid signatures for this test were generated
// out-of-band using the PyCryptodome Python library.

static uint32_t kTestModulus4096[128] = {
    0xf7a07ea1, 0xfa092263, 0x14182978, 0x41e24e12, 0x87550aa3, 0x3933d0ed,
    0xe096c94a, 0x3ecf2209, 0x09ca3ada, 0xd3066faa, 0xf70529de, 0x781cf3d2,
    0x570102f7, 0xd195a437, 0xaf8fe43a, 0x68213835, 0xb96e9672, 0x8d75ecc8,
    0xebbdb19a, 0xf0e0a519, 0x68268698, 0x86e3a1f2, 0x12998595, 0x7da50fa6,
    0xe9b8283d, 0x91f8e1fb, 0xa087dd9a, 0x5d6d57e9, 0x689b004f, 0x1276394f,
    0xd9397c7e, 0xeeae49ab, 0x7b179941, 0xc501e72c, 0x25301db5, 0xbdc591ec,
    0x79847355, 0xb987ea2a, 0x4f8d444f, 0x24419141, 0x1c6f955f, 0x2e2702de,
    0x5658053f, 0x144225f6, 0xc2db7b06, 0xe608fe78, 0x158eaa5d, 0x1c12be2d,
    0xe429e4c5, 0xf8c03d15, 0x6679f8da, 0x8601c2fc, 0x2c8deed4, 0xb8768e59,
    0x298f7962, 0x07c41596, 0xc78c2e15, 0xaace20fb, 0xf702920e, 0x98900667,
    0x83e8e2d9, 0xc27ed454, 0x9290924a, 0x58563c03, 0xcea9a2ef, 0x3d22226c,
    0x3c6a2878, 0x9c8cfeb6, 0x4ff44ae2, 0x2503337b, 0x2239de35, 0x9f002e91,
    0xcd560937, 0x50ae2563, 0x8a7c79ca, 0x010ae7fa, 0xac18ebff, 0xda72cd67,
    0x25c68935, 0x6312379b, 0x272be99e, 0x18a7476d, 0x70068ac0, 0x33908617,
    0x52883554, 0xc8ec446b, 0xff57b8a8, 0xba74f31b, 0xf6f35996, 0x34f9217c,
    0xaf63e945, 0x7b5c3ea2, 0xaffce194, 0x2c573779, 0x66e82607, 0xcadcec25,
    0xa6965f20, 0x5c92af81, 0xb7292f8f, 0xab30f4a9, 0x5bfc9f02, 0xd09b6b84,
    0x5e1b1064, 0xce36c103, 0x99a55993, 0x6e81d761, 0xcb2654e5, 0xee973036,
    0x4f332f2f, 0x7a8bf3fe, 0x8b103b2d, 0x9fc47c03, 0x5199b516, 0x040bfae5,
    0x30e83971, 0x1dfffa01, 0x6a86db1a, 0x152eae07, 0x10d9fb28, 0xaf122d45,
    0x9c9a2bcc, 0xd94429d1, 0x305f19eb, 0xdb459c5f, 0x6739d717, 0xcf63816b,
    0x57685c09, 0xa310c635,
};
static uint32_t kTestPrivateExponent4096[128] = {
    0x1fe31691, 0x25f6d813, 0x75cc2529, 0xaaf1cb60, 0xa47c30bc, 0xa45f398f,
    0xafacc695, 0xbc16a051, 0xbf278612, 0xc6f02d81, 0x8bd0c4c1, 0xf0ee9e6e,
    0xcb095447, 0x46ce4bfd, 0xd8b6a640, 0x8d88234f, 0x748e78b0, 0xfbddd2c5,
    0x6c330f42, 0x1a3a60e3, 0xf2809130, 0xc3225097, 0xa9265d86, 0x2ab6c5f5,
    0x1b96240a, 0x73e24aba, 0x64cf12dc, 0x45f32323, 0xb414640d, 0x7c96b53b,
    0x041fd715, 0x1571feea, 0x5d5ca9c1, 0x31df9f42, 0x7a9bc11c, 0x19e05634,
    0x4e7005a0, 0xe45c8197, 0x70bef535, 0x457d341c, 0x62795a2f, 0x11e89309,
    0x3457f7d6, 0xa1145daa, 0xc5c7eebd, 0x6e6da36c, 0xe1f5036b, 0xbdd608a5,
    0x8e4ffcec, 0xc2288541, 0x865e0d45, 0x0650bbdc, 0x435f134f, 0x2c11d18e,
    0xf33ddf47, 0x68e3a51b, 0x2ef747f7, 0xec8fa351, 0xd08a85c4, 0x519490e7,
    0xb2519dc9, 0x79b3ebd9, 0xf2021036, 0x03d430cf, 0x763d767c, 0x84eaa067,
    0x6297be45, 0x08a0da44, 0x0a5048ad, 0xdb128be4, 0x5e9e4596, 0x779cc046,
    0x352751f9, 0xd9d34432, 0xd5e8c59e, 0xa1fc44f7, 0x0cc60b86, 0xfd82f822,
    0x6d5325e1, 0xaeaadb65, 0x0c2beae6, 0xf488676f, 0x170c93dd, 0x00f49f8d,
    0x8ce1cdbf, 0xb3911e0f, 0x4cdb65ac, 0x59b34b77, 0x53e5b90a, 0x9517ba98,
    0x1525cc15, 0xcc26533a, 0xd45a64b8, 0xd35abf28, 0xd76d6245, 0x40c95c96,
    0xd1e87955, 0x0f54777f, 0x0f6a4a1b, 0x31a6fa16, 0x6a37cef2, 0x46bf75ad,
    0x7ee76666, 0x7ca81da4, 0xea1d0bd8, 0x8c4d4d05, 0xc8245661, 0xa84e5bcb,
    0x0bb2e2d8, 0x205de561, 0x35ea2b31, 0xf406337f, 0x743322f9, 0x4260aa96,
    0x1d34f442, 0xb3f3e277, 0x1c1b4bc8, 0x32e5005f, 0x71cf55c3, 0xa10ca1df,
    0x04db4c31, 0xd95f7826, 0x7d983389, 0x533f04d8, 0xf649e192, 0x951fa2af,
    0x1c92d23d, 0x023b32c7,
};
static uint32_t kTestPrimeP4096[64] = {
    0x4870d969, 0x06e967b5, 0xfadc97df, 0x7c3b3453, 0xdffcf2f8, 0x9d09d957,
    0x56d3a74f, 0x43085647, 0x1ac600fe, 0x437c5697, 0x54a45de1, 0x8b0b1779,
    0xb33335c7, 0x0c0126a1, 0x858a83cb, 0xfd49c99c, 0x51e85099, 0x8245fca9,
    0x35436971, 0x39826655, 0xcea5c15e, 0x1850cb55, 0x59585e46, 0x9c58cf62,
    0x1b298fcf, 0xda6b8663, 0xeda1c38a, 0x55c2e95c, 0xbaaaa43b, 0xd45f73d1,
    0x6de1fc2c, 0x4d20e8bf, 0x67f1b4be, 0xae62d5b0, 0x6a7c4fb8, 0x1239739c,
    0xcf16c3ce, 0xd5354add, 0x0390b2b0, 0xe1711299, 0x69bfa912, 0xcc76a490,
    0x6b384c04, 0x6411848d, 0x39ba4a36, 0xc62dea49, 0x409cc47f, 0xdc207134,
    0xd9ecf0e3, 0x93cbe11f, 0xa2660eed, 0x85e8a8f3, 0xb141ab48, 0x1eba1436,
    0x09930996, 0x82750750, 0x249a5a1b, 0xed9f5c60, 0xb081f4bb, 0x298eb031,
    0x2944a33c, 0xfce8344b, 0x8e56540d, 0xc48a662d,
};
static uint32_t kTestPrimeQ4096[64] = {
    0x5de85c79, 0xd94a658c, 0x95bdc1e7, 0x4cc3c53d, 0x6e5e3cf6, 0xf48e793a,
    0xa3f7286c, 0x39c3ae9f, 0xa66db72e, 0x8b0e5c2e, 0x6cf9ca7a, 0xacf6a2fe,
    0xc4071767, 0x44cf48f5, 0x52a18ab5, 0x4a3e2d28, 0x8c3a9f7a, 0x0f3d2c59,
    0xd5199695, 0x64285417, 0xf1da7f86, 0xc431b634, 0x6f3cd233, 0x2bd2f222,
    0x9c505366, 0x9670476d, 0x5832c656, 0xc2521f9b, 0x44c92401, 0x2b9ec7a8,
    0x81ef7517, 0xaa05bf20, 0x881d14c2, 0x0442addb, 0x290b1903, 0x83502537,
    0x5b5454ed, 0x4d0cc409, 0x9985ae48, 0x89c31ec4, 0x568dc370, 0xc5ebc34d,
    0x0f2ff1bd, 0x25aa1a13, 0x3237183e, 0xda64dcd4, 0x80d4ac00, 0x51913e5d,
    0xe80a368b, 0x0a17ff28, 0x1c2001ad, 0xd3221d75, 0xfc858588, 0x6ba2768a,
    0xd4d06582, 0x2a4c45d7, 0x230fd27e, 0x0d98ffe5, 0x2b8006c0, 0x9f11c171,
    0xfbc642ea, 0xf14bac34, 0xa8167ee2, 0xd465cf16,
};

static status_t run_key_from_cofactor_4096(const uint32_t *cofactor) {
  otcrypto_const_word32_buf_t cofactor_share0 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, cofactor, kRsa4096CofactorNumWords);
  uint32_t cofactor_share1_data[kRsa4096CofactorNumWords] = {0};
  otcrypto_const_word32_buf_t cofactor_share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, cofactor_share1_data,
                        ARRAYSIZE(cofactor_share1_data));

  otcrypto_const_word32_buf_t modulus =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kTestModulus4096,
                        ARRAYSIZE(kTestModulus4096));

  otcrypto_key_config_t private_key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kTestKeyMode,
      .key_length = kOtcryptoRsa4096PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  size_t keyblob_words =
      ceil_div(kOtcryptoRsa4096PrivateKeyblobBytes, sizeof(uint32_t));
  uint32_t keyblob[keyblob_words];
  otcrypto_blinded_key_t private_key = {
      .config = private_key_config,
      .keyblob = keyblob,
      .keyblob_length = kOtcryptoRsa4096PrivateKeyblobBytes,
  };

  size_t public_key_words =
      ceil_div(kOtcryptoRsa4096PublicKeyBytes, sizeof(uint32_t));
  uint32_t public_key_data[public_key_words];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kTestKeyMode,
      .key = public_key_data,
      .key_length = kOtcryptoRsa4096PublicKeyBytes,
  };

  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize4096, &modulus,
                                         &cofactor_share0, &cofactor_share1,
                                         &public_key, &private_key));
  profile_end_and_print(t_start, "RSA-4096 keypair from cofactor");

  TRY_CHECK(private_key.keyblob_length == sizeof(rsa_4096_private_key_t));
  rsa_4096_private_key_t *sk = (rsa_4096_private_key_t *)private_key.keyblob;
  TRY_CHECK_ARRAYS_EQ(sk->d0.data, kTestPrivateExponent4096,
                      ARRAYSIZE(kTestPrivateExponent4096));

  TRY_CHECK_ARRAYS_EQ(sk->n.data, kTestModulus4096,
                      ARRAYSIZE(kTestModulus4096));
  TRY_CHECK(public_key.key_length == sizeof(rsa_4096_public_key_t));
  rsa_4096_public_key_t *pk = (rsa_4096_public_key_t *)public_key.key;
  TRY_CHECK_ARRAYS_EQ(pk->n.data, kTestModulus4096,
                      ARRAYSIZE(kTestModulus4096));
  return OK_STATUS();
}

status_t keypair_from_p_test(void) {
  return run_key_from_cofactor_4096(kTestPrimeP4096);
}
status_t keypair_from_q_test(void) {
  return run_key_from_cofactor_4096(kTestPrimeQ4096);
}

static status_t run_cofactor_negative_tests(void) {
  LOG_INFO("Running RSA-4096 cofactor negative tests");

  uint32_t mod_data[kRsa4096NumWords] = {0};
  otcrypto_const_word32_buf_t valid_mod = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, mod_data, kRsa4096NumWords);
  otcrypto_const_word32_buf_t bad_mod_null =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, NULL, kRsa4096NumWords);

  uint32_t cof_data[kRsa4096CofactorNumWords] = {0};
  otcrypto_const_word32_buf_t valid_cof = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, cof_data, kRsa4096CofactorNumWords);
  otcrypto_const_word32_buf_t bad_cof_null = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, NULL, kRsa4096CofactorNumWords);
  otcrypto_const_word32_buf_t bad_cof_len =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, cof_data, 16);

  uint32_t pub_data[kOtcryptoRsa4096PublicKeyBytes / 4] = {0};
  otcrypto_unblinded_key_t valid_pub = {
      .key_mode = kTestKeyMode,
      .key_length = kOtcryptoRsa4096PublicKeyBytes,
      .key = pub_data,
  };

  otcrypto_key_config_t priv_cfg = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kTestKeyMode,
      .key_length = kOtcryptoRsa4096PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t priv_blob[kOtcryptoRsa4096PrivateKeyblobBytes / 4] = {0};
  otcrypto_blinded_key_t valid_priv = {
      .config = priv_cfg,
      .keyblob_length = kOtcryptoRsa4096PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };

  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize4096, &bad_mod_null,
                                           &valid_cof, &valid_cof, &valid_pub,
                                           &valid_priv)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize4096, &valid_mod,
                                           &bad_cof_null, &valid_cof,
                                           &valid_pub, &valid_priv)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize4096, &valid_mod,
                                           &valid_cof, &valid_cof, NULL,
                                           &valid_priv)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize4096, &valid_mod,
                                           &valid_cof, &valid_cof, &valid_pub,
                                           NULL)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize4096, &valid_mod,
                                           &bad_cof_len, &valid_cof, &valid_pub,
                                           &valid_priv)
            .value != OTCRYPTO_OK.value);

  otcrypto_unblinded_key_t bad_pub_len = {
      .key_mode = kTestKeyMode,
      .key_length = 99,
      .key = pub_data,
  };
  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize4096, &valid_mod,
                                           &valid_cof, &valid_cof, &bad_pub_len,
                                           &valid_priv)
            .value != OTCRYPTO_OK.value);

  otcrypto_key_config_t bad_mode_cfg = priv_cfg;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeEcdsaP256;
  otcrypto_blinded_key_t bad_priv_mode = {
      .config = bad_mode_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };
  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize4096, &valid_mod,
                                           &valid_cof, &valid_cof, &valid_pub,
                                           &bad_priv_mode)
            .value != OTCRYPTO_OK.value);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t test_result = OK_STATUS();
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));
  EXECUTE_TEST(test_result, keypair_from_p_test);
  EXECUTE_TEST(test_result, keypair_from_q_test);
  EXECUTE_TEST(test_result, run_cofactor_negative_tests);
  return status_ok(test_result);
}
