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
  kRsa3072CofactorNumWords = kRsa3072NumWords / 2,
};

static otcrypto_key_mode_t kTestKeyMode = kOtcryptoKeyModeRsaSignPss;

// Note: The private key and valid signatures for this test were generated
// out-of-band using the PyCryptodome Python library.

static uint32_t kTestModulus3072[96] = {
    0xe0d8406d, 0xf9cc528a, 0xc058e374, 0xffb0f35a, 0x23813181, 0x2e68bca3,
    0xdcfd571d, 0x5f26e43d, 0xa09733b1, 0xb766ae35, 0xd4730a11, 0x7b39a82a,
    0x12e63818, 0xa930ae04, 0x8bf5cfb1, 0x15eb24f0, 0x5852bb25, 0xff526d80,
    0x96702fe0, 0xae8e4c79, 0x00cee970, 0xdf264bf7, 0x6d3ea677, 0x9c4c9634,
    0xeaa52ceb, 0xe592dc69, 0x5896fc72, 0x2ac67622, 0x63f511dc, 0xebaf0923,
    0xbcbcee8e, 0xe799cb96, 0x5cbe7854, 0x2f092062, 0x5d270e24, 0xe36d7da8,
    0x1e0d4836, 0xa36a9e2e, 0xd6b05a0a, 0x76746b8a, 0xc20d494a, 0xfc3cb4b2,
    0xff99e611, 0x190672ef, 0xb7424aa8, 0x6ccf9de8, 0xd18dd277, 0x85474413,
    0x9a01d7e0, 0x2b38d35e, 0x1ab4de1b, 0x592f5bd8, 0x97c76953, 0xc8f22cd2,
    0x3c487f7c, 0xdc549a06, 0x9a6bc581, 0x2fe0332b, 0x058ea037, 0x11fe1b6c,
    0x2a2cb1d4, 0x982f7a21, 0x5eb016b9, 0xf5871ca4, 0x0cf3811d, 0x8eddd222,
    0xf7bd8bbc, 0x488c092b, 0xec38f18f, 0xec55d465, 0xc0313b13, 0x1660850f,
    0x2f8378ae, 0x4c6052f8, 0x1fcbb229, 0x654e1547, 0x39eaa450, 0x3b6866eb,
    0x43fd5be1, 0x0de76882, 0x658a69e4, 0x3bbf6f23, 0x7fddd143, 0x51918d6d,
    0x197f819a, 0x2ec29ffb, 0x861284d6, 0x310c491a, 0x75f7be39, 0x79959d89,
    0x5efcd6d4, 0x01cd3a29, 0xee173182, 0x53b53b52, 0x442a3a76, 0xa1811ef4,
};
static uint32_t kTestPrivateExponent3072[96] = {
    0x75e558ad, 0xc45f89c0, 0xd7ccef4b, 0x96b43e00, 0xb34b25af, 0x1c228165,
    0x63f6a86b, 0xa362d791, 0x496b7cca, 0xefb32842, 0xadef5e35, 0xc107fde7,
    0x90ed172a, 0x44d9dbe6, 0xe8951aab, 0x61141b5a, 0xf413cdd2, 0xcc3b533a,
    0xd1068079, 0xdccbbf19, 0xf57379f3, 0x88e73a01, 0xbf6b656a, 0x8a487e22,
    0x3aaedc2b, 0xcebc9e0f, 0x57c7b620, 0x966ba7b6, 0x1ddaa1bd, 0x6e1084c7,
    0xe7b8e630, 0x82f4fff9, 0xd13a604e, 0xbdf8e065, 0x8d4852f4, 0xe12ede3a,
    0xe241d5ee, 0x39245c84, 0xbee25dc2, 0x8194a855, 0x70a6a6c3, 0x2b2a5b40,
    0xcacc8d4c, 0x259e5782, 0x2e52c6e2, 0xbe1f8ae9, 0x99d93dbd, 0xc73724de,
    0x02777895, 0xe9f85604, 0xdc7c53a1, 0xe55aca34, 0x8f73375d, 0x7e2162ec,
    0x8dce8c98, 0x5357a633, 0xb2b652f5, 0xf1a185cf, 0x1502d2d7, 0x6d2feec7,
    0x86969282, 0xf9779cf8, 0xa7257d33, 0xcacddab0, 0x6094d9ec, 0x2fafd3e9,
    0x2eda9983, 0xb6909c44, 0xe1858f4d, 0x09ddbaf6, 0x01300d50, 0xe2f4a51a,
    0x5f8aba77, 0x737a4eef, 0x244ef8a6, 0x6ef2092c, 0xb569cc58, 0x7060c803,
    0x0028cab0, 0xc3541dcb, 0x07e51913, 0xb534a4bc, 0xfa991da8, 0x721e978c,
    0xe64df7a0, 0x2b8e4db8, 0x39fbe736, 0x2c8cf9da, 0x19e0372c, 0xaa20bf70,
    0x267a1731, 0xebbcf4f3, 0x993b6541, 0x9e2f337d, 0xb84cab32, 0x3f55e8b2,
};
static uint32_t kTestPrimeP3072[48] = {
    0xf08020db, 0xe49816db, 0x349fd48c, 0x91cf0f04, 0xf2eb1a5f, 0xfa436447,
    0x9e574229, 0x9bcda88d, 0x9ab23dff, 0xb16e50a3, 0x7535a5bd, 0xd5f3b331,
    0x772a2c7c, 0x0e68b01a, 0xe23a976a, 0x4e82ad8c, 0x1dd6fadc, 0x180919c0,
    0x205b6398, 0x56f0f2da, 0x3bfa8d10, 0x01a4d865, 0x7c0ecb87, 0xd32d1d02,
    0xc247631c, 0x477b1f4d, 0x435ee2ad, 0xb8825efa, 0x6be6e6b5, 0xd8e4ee34,
    0x097dc8cc, 0xf8e55d17, 0x60fc4fe3, 0x5da976ab, 0x5df290bf, 0xccaf14be,
    0x0850f3ff, 0xe59a4277, 0xea84fafb, 0x02655a07, 0x7d981a26, 0xc24fe907,
    0xa60dbccc, 0xfc3127c0, 0xeefd515c, 0xcf079598, 0x3b5a8c5d, 0xbe219c4d,
};
static uint32_t kTestPrimeQ3072[48] = {
    0xfdd02257, 0xd43f4c58, 0x21e99d9d, 0xe710e3b3, 0x02388280, 0xabeacd01,
    0x3989d6e5, 0x36ed8235, 0x692cc8c5, 0xb9cf49b9, 0x38fd80a4, 0x8fe3e26e,
    0x54d9000b, 0x0f14c2ee, 0x4806d43b, 0xdb88a7b0, 0x1ebc3cd9, 0xa956f057,
    0x0078d926, 0x1dfef232, 0xbe54b0c5, 0x1d7edf5c, 0x057210cf, 0xfbfb61b2,
    0x22eabe60, 0xa4439e1d, 0x67092ab0, 0x6071a124, 0x7e3a7f6a, 0x832d34af,
    0x8266bdfe, 0x8fef0050, 0xd10152cb, 0x9d64800a, 0x2d200735, 0x08e41649,
    0x4c7669b4, 0xffb544be, 0x7b4db828, 0xd76f6631, 0x300eaca7, 0x91254750,
    0x049e7f76, 0xcb6130c2, 0x32363d67, 0x49365128, 0xb4d230e2, 0xd974a494,
};

static status_t run_key_from_cofactor_3072(const uint32_t *cofactor) {
  otcrypto_const_word32_buf_t cofactor_share0 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, cofactor, kRsa3072CofactorNumWords);
  uint32_t cofactor_share1_data[kRsa3072CofactorNumWords] = {0};
  otcrypto_const_word32_buf_t cofactor_share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, cofactor_share1_data,
                        ARRAYSIZE(cofactor_share1_data));

  otcrypto_const_word32_buf_t modulus =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kTestModulus3072,
                        ARRAYSIZE(kTestModulus3072));

  otcrypto_key_config_t private_key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kTestKeyMode,
      .key_length = kOtcryptoRsa3072PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  size_t keyblob_words =
      ceil_div(kOtcryptoRsa3072PrivateKeyblobBytes, sizeof(uint32_t));
  uint32_t keyblob[keyblob_words];
  otcrypto_blinded_key_t private_key = {
      .config = private_key_config,
      .keyblob = keyblob,
      .keyblob_length = kOtcryptoRsa3072PrivateKeyblobBytes,
  };

  size_t public_key_words =
      ceil_div(kOtcryptoRsa3072PublicKeyBytes, sizeof(uint32_t));
  uint32_t public_key_data[public_key_words];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kTestKeyMode,
      .key = public_key_data,
      .key_length = kOtcryptoRsa3072PublicKeyBytes,
  };

  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize3072, &modulus,
                                         &cofactor_share0, &cofactor_share1,
                                         &public_key, &private_key));
  profile_end_and_print(t_start, "RSA-3072 keypair from cofactor");

  TRY_CHECK(private_key.keyblob_length == sizeof(rsa_3072_private_key_t));
  rsa_3072_private_key_t *sk = (rsa_3072_private_key_t *)private_key.keyblob;
  TRY_CHECK_ARRAYS_EQ(sk->d0.data, kTestPrivateExponent3072,
                      ARRAYSIZE(kTestPrivateExponent3072));

  TRY_CHECK_ARRAYS_EQ(sk->n.data, kTestModulus3072,
                      ARRAYSIZE(kTestModulus3072));
  TRY_CHECK(public_key.key_length == sizeof(rsa_3072_public_key_t));
  rsa_3072_public_key_t *pk = (rsa_3072_public_key_t *)public_key.key;
  TRY_CHECK_ARRAYS_EQ(pk->n.data, kTestModulus3072,
                      ARRAYSIZE(kTestModulus3072));
  return OK_STATUS();
}

status_t keypair_from_p_test(void) {
  return run_key_from_cofactor_3072(kTestPrimeP3072);
}
status_t keypair_from_q_test(void) {
  return run_key_from_cofactor_3072(kTestPrimeQ3072);
}

static status_t run_cofactor_negative_tests(void) {
  LOG_INFO("Running RSA-3072 cofactor negative tests");

  uint32_t mod_data[kRsa3072NumWords] = {0};
  otcrypto_const_word32_buf_t valid_mod = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, mod_data, kRsa3072NumWords);
  otcrypto_const_word32_buf_t bad_mod_null =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, NULL, kRsa3072NumWords);

  uint32_t cof_data[kRsa3072CofactorNumWords] = {0};
  otcrypto_const_word32_buf_t valid_cof = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, cof_data, kRsa3072CofactorNumWords);
  otcrypto_const_word32_buf_t bad_cof_null = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, NULL, kRsa3072CofactorNumWords);
  otcrypto_const_word32_buf_t bad_cof_len =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, cof_data, 16);

  uint32_t pub_data[kOtcryptoRsa3072PublicKeyBytes / 4] = {0};
  otcrypto_unblinded_key_t valid_pub = {
      .key_mode = kTestKeyMode,
      .key_length = kOtcryptoRsa3072PublicKeyBytes,
      .key = pub_data,
  };

  otcrypto_key_config_t priv_cfg = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kTestKeyMode,
      .key_length = kOtcryptoRsa3072PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t priv_blob[kOtcryptoRsa3072PrivateKeyblobBytes / 4] = {0};
  otcrypto_blinded_key_t valid_priv = {
      .config = priv_cfg,
      .keyblob_length = kOtcryptoRsa3072PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };

  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize3072, &bad_mod_null,
                                           &valid_cof, &valid_cof, &valid_pub,
                                           &valid_priv)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize3072, &valid_mod,
                                           &bad_cof_null, &valid_cof,
                                           &valid_pub, &valid_priv)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize3072, &valid_mod,
                                           &valid_cof, &valid_cof, NULL,
                                           &valid_priv)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize3072, &valid_mod,
                                           &valid_cof, &valid_cof, &valid_pub,
                                           NULL)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize3072, &valid_mod,
                                           &bad_cof_len, &valid_cof, &valid_pub,
                                           &valid_priv)
            .value != OTCRYPTO_OK.value);

  otcrypto_unblinded_key_t bad_pub_len = {
      .key_mode = kTestKeyMode,
      .key_length = 99,
      .key = pub_data,
  };
  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize3072, &valid_mod,
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
  CHECK(otcrypto_rsa_keypair_from_cofactor(kOtcryptoRsaSize3072, &valid_mod,
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
