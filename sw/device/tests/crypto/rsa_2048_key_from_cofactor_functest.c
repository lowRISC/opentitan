// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_datatypes.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/profile.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module for status messages.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

enum {
  kRsa2048CofactorNumWords = kRsa2048NumWords / 2,
};

// Note: The private key and valid signatures for this test were generated
// out-of-band using the PyCryptodome Python library.

// Test RSA-2048 key pair.
static uint32_t kTestModulus[kRsa2048NumWords] = {
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
static uint32_t kTestPrivateExponent[kRsa2048NumWords] = {
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
static uint32_t kTestPublicExponent = 65537;

// Key mode for testing.
static otcrypto_key_mode_t kTestKeyMode = kOtcryptoKeyModeRsaSignPss;

// The prime cofactor p for the test private key.
static uint32_t kTestPrimeP[kRsa2048CofactorNumWords] = {
    0x69e8cdeb, 0xaab5698,  0x2adbf5a2, 0xc6f3fed7, 0x9b0f148c, 0x68a4b636,
    0xc3c8948c, 0x5ee5c048, 0xb20f9f30, 0xaced9c36, 0xe2a0f71f, 0xf57f3401,
    0x8fb749f8, 0x24f4b1f2, 0x2811dd24, 0xe45d624,  0x7e4fac27, 0x7049a420,
    0x4ea4172b, 0x1d4f1d2d, 0x15c1dd03, 0x733ce8c1, 0xe5415c61, 0xa3680f9a,
    0xa13ff562, 0xd12a0242, 0x3ef684a4, 0x5241db6e, 0x2e68b5f5, 0xaa3e5397,
    0x45e9606a, 0xb8505888,
};
// The prime cofactor q for the test private key.
static uint32_t kTestPrimeQ[kRsa2048CofactorNumWords] = {
    0xc69864d3, 0x6eca1793, 0xd985ff65, 0xa888cce8, 0xcadcabc5, 0x47d31ff8,
    0x2eae994a, 0xba8594d,  0x956889ed, 0x117f0b01, 0x30ace812, 0x89aa41b9,
    0x716c8c93, 0xb3e54154, 0x70020ae3, 0x3f3926af, 0x91ae5a18, 0xa058daef,
    0xd5a8a0ee, 0xff73e9fb, 0xda00591c, 0x69220aec, 0xe9ee684b, 0x12f4ea77,
    0xea538fb5, 0x505826e,  0xef416b24, 0x5c65d8d6, 0xce422bd4, 0x3f4f37ed,
    0xdd6aff12, 0xf6c55808,
};

/**
 * Helper function to run the key-from-cofactor routine.
 *
 * Packages input into cryptolib-style structs and calls
 * `otcrypto_rsa_private_key_from_public_and_cofactor` using the constant test
 * public key and the given cofactor. Ensures that the resulting private
 * exponent matches the test private exponent.
 *
 * @param cofactor Pointer to the cofactor data.
 * @return OK or error.
 */
static status_t run_key_from_cofactor(const uint32_t *cofactor) {
  // Create two shares for the cofactor (second share is all-zero).
  otcrypto_const_word32_buf_t cofactor_share0 = {
      .data = cofactor,
      .len = kRsa2048CofactorNumWords,
  };
  uint32_t cofactor_share1_data[kRsa2048CofactorNumWords] = {0};
  otcrypto_const_word32_buf_t cofactor_share1 = {
      .data = cofactor_share1_data,
      .len = ARRAYSIZE(cofactor_share1_data),
  };

  // Buffer for the modulus.
  otcrypto_const_word32_buf_t modulus = {
      .data = kTestModulus,
      .len = ARRAYSIZE(kTestModulus),
  };

  // Construct the private key buffer and configuration.
  otcrypto_key_config_t private_key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kTestKeyMode,
      .key_length = kOtcryptoRsa2048PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  size_t keyblob_words =
      ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes, sizeof(uint32_t));
  uint32_t keyblob[keyblob_words];
  otcrypto_blinded_key_t private_key = {
      .config = private_key_config,
      .keyblob = keyblob,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
  };

  // Construct the public key buffer.
  size_t public_key_words =
      ceil_div(kOtcryptoRsa2048PublicKeyBytes, sizeof(uint32_t));
  uint32_t public_key_data[public_key_words];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kTestKeyMode,
      .key = public_key_data,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
  };

  // Construct the RSA key pair using the cofactor.
  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_keypair_from_cofactor(
      kOtcryptoRsaSize2048, modulus, kTestPublicExponent, cofactor_share0,
      cofactor_share1, &public_key, &private_key));
  profile_end_and_print(t_start, "RSA keypair from cofactor");

  // Interpret the private key and ensure the private exponent matches the
  // expected value. Note: This depends on the internal representation of RSA
  // keyblobs, and will need to be updated if the representation changes.
  TRY_CHECK(private_key.keyblob_length == sizeof(rsa_2048_private_key_t));
  rsa_2048_private_key_t *sk = (rsa_2048_private_key_t *)private_key.keyblob;
  TRY_CHECK_ARRAYS_EQ(sk->d.data, kTestPrivateExponent,
                      ARRAYSIZE(kTestPrivateExponent));

  // Check the other values too, just to be safe.
  TRY_CHECK_ARRAYS_EQ(sk->n.data, kTestModulus, ARRAYSIZE(kTestModulus));
  TRY_CHECK(public_key.key_length == sizeof(rsa_2048_public_key_t));
  rsa_2048_public_key_t *pk = (rsa_2048_public_key_t *)public_key.key;
  TRY_CHECK_ARRAYS_EQ(pk->n.data, kTestModulus, ARRAYSIZE(kTestModulus));
  TRY_CHECK(pk->e == kTestPublicExponent);
  return OK_STATUS();
}

status_t keypair_from_p_test(void) {
  return run_key_from_cofactor(kTestPrimeP);
}

status_t keypair_from_q_test(void) {
  return run_key_from_cofactor(kTestPrimeQ);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t test_result = OK_STATUS();
  CHECK_STATUS_OK(entropy_complex_init());
  EXECUTE_TEST(test_result, keypair_from_p_test);
  EXECUTE_TEST(test_result, keypair_from_q_test);
  return status_ok(test_result);
}
