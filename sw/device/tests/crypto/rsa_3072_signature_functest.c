// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/profile.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module for status messages.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

enum {
  kSha512DigestWords = 512 / 32,
  kRsa3072NumBytes = 3072 / 8,
  kRsa3072NumWords = kRsa3072NumBytes / sizeof(uint32_t),
};

// Note: The private key and valid signatures for this test were generated
// out-of-band using the PyCryptodome Python library.

// Test RSA-3072 key pair:
// e = 65537
// n =
// 0xa60f30a231261907afe74287a90cc23b24ec935f7520180f833bf3261c9f5a53c6057b0be827fc8c8adb26e8a4b442f1075a427b065433ac5b973b2ccc4ee3b8e82d5c810922ea4653cdc14e46dcfa85141f23d07fdec0a90b53c50ad1a7e9984bed7f9edcbafdb26398c69c6b8cfc8e2cd843c33fc8e54284807eb9abca302946b16dd82f8c428bd446f2cbf9d614e637c377b39d0a8e494b2dab398094aee11cf0109bb82214b11988b5df0943554126d660d3ac776aa1ea044e20f7e63fafddecb80bde3a683d64a074ff3e1dfa99ab5c16575dfe37bc5bb1b180434ccc4853b671a05c36a62b22df77e1482def92e576ea64ebf8d88d91fcadfeabc571ebedd8bc920d15ec18e300d4747b8bc3e8e04eb5afd95d6ff662ec62aa54ce8e23dd1beacfdde93cc03d9bdfffd2412d3255bed6946258c90c5fcfd55f1e9c1ce3bcd26c2b1299c298f941f8992318ca24154da24dee956a867b1f16bd0241a25db9c19f8630ca11035b29ea9cddf894ca239b6fe8c2242ceb61422b395248e8eb
// d =
// 0x2e1fdefed60f0279cfa2b9288c4ca6709e277621d81b2383bf8c79d3b6b48e76e17469429be7eb6eb02d022831837e6a8b83c71e7bda0c864de47a43cdb605ebb8d5ccb16cb3bd85ee4622f0d69f0f98c24789ffa25ce17fb2cd40586a76acdc280ede59666f2c038e4583b933e873c81bedb018be115398bfcc1f26fc700b2393e6b99f884979bc742886cd206695e4824db1647af4d123cb95724f6507277210c31fa1d929e23c74deb3c1b1457a1b4029e0b83ad9ea8cf1bee362a5e8d6fc546a4e705e73b4c9f8f5486c3c4dcc1e3e812025483a0ef65efe857ea81331256f43345142b3cba4cdb00270c27647b3b8d1185826066b83374bb038098a4e152a95830d621c40e752fc2a22a7bd0a88f7a1e86ae8f2bd3bde3d37027fc735a1f8a09cd55ce7738204a3767a15ce0940fe49e5b63c7a23fa15dae580446884981753730bc0944ac3421f557a1f44a1927863c8051c7f4bd88a71c55225b096ecc52df173bf748b23b332bc608702a398f1624a49919be3408341fecaf3cc45d9

// Modulus (n) in little-endian form.
static uint32_t kTestModulus[kRsa3072NumWords] = {
    0x5248e8eb, 0x61422b39, 0xc2242ceb, 0x239b6fe8, 0xddf894ca, 0x5b29ea9c,
    0x30ca1103, 0xb9c19f86, 0x0241a25d, 0x7b1f16bd, 0xee956a86, 0x154da24d,
    0x2318ca24, 0xf941f899, 0x1299c298, 0xbcd26c2b, 0x1e9c1ce3, 0x5fcfd55f,
    0x6258c90c, 0x55bed694, 0xd2412d32, 0x3d9bdfff, 0xdde93cc0, 0xdd1beacf,
    0x54ce8e23, 0x62ec62aa, 0xd95d6ff6, 0xe04eb5af, 0x7b8bc3e8, 0xe300d474,
    0x0d15ec18, 0xedd8bc92, 0xabc571eb, 0x91fcadfe, 0xebf8d88d, 0xe576ea64,
    0x482def92, 0x22df77e1, 0x5c36a62b, 0x53b671a0, 0x434ccc48, 0x5bb1b180,
    0x5dfe37bc, 0xab5c1657, 0x3e1dfa99, 0x64a074ff, 0xde3a683d, 0xddecb80b,
    0xf7e63faf, 0xea044e20, 0xac776aa1, 0x26d660d3, 0x09435541, 0x1988b5df,
    0xb82214b1, 0x1cf0109b, 0x8094aee1, 0x4b2dab39, 0x9d0a8e49, 0x37c377b3,
    0xf9d614e6, 0xd446f2cb, 0x2f8c428b, 0x46b16dd8, 0xabca3029, 0x84807eb9,
    0x3fc8e542, 0x2cd843c3, 0x6b8cfc8e, 0x6398c69c, 0xdcbafdb2, 0x4bed7f9e,
    0xd1a7e998, 0x0b53c50a, 0x7fdec0a9, 0x141f23d0, 0x46dcfa85, 0x53cdc14e,
    0x0922ea46, 0xe82d5c81, 0xcc4ee3b8, 0x5b973b2c, 0x065433ac, 0x075a427b,
    0xa4b442f1, 0x8adb26e8, 0xe827fc8c, 0xc6057b0b, 0x1c9f5a53, 0x833bf326,
    0x7520180f, 0x24ec935f, 0xa90cc23b, 0xafe74287, 0x31261907, 0xa60f30a2,
};
static uint32_t kTestPrivateExponent[kRsa3072NumWords] = {
    0xf3cc45d9, 0x8341feca, 0x919be340, 0xf1624a49, 0x8702a398, 0xb332bc60,
    0xbf748b23, 0xc52df173, 0x25b096ec, 0x8a71c552, 0x1c7f4bd8, 0x7863c805,
    0x1f44a192, 0x421f557a, 0xc0944ac3, 0x1753730b, 0x44688498, 0x15dae580,
    0x3c7a23fa, 0xfe49e5b6, 0x15ce0940, 0x04a3767a, 0x5ce77382, 0xf8a09cd5,
    0x7fc735a1, 0xde3d3702, 0xe8f2bd3b, 0xf7a1e86a, 0xa7bd0a88, 0x52fc2a22,
    0x621c40e7, 0x2a95830d, 0x098a4e15, 0x374bb038, 0x26066b83, 0xb8d11858,
    0xc27647b3, 0xcdb00270, 0x42b3cba4, 0x6f433451, 0xa8133125, 0x5efe857e,
    0x483a0ef6, 0x3e812025, 0x3c4dcc1e, 0xf8f5486c, 0x5e73b4c9, 0x546a4e70,
    0xa5e8d6fc, 0xf1bee362, 0x3ad9ea8c, 0x4029e0b8, 0xb1457a1b, 0x74deb3c1,
    0xd929e23c, 0x10c31fa1, 0x65072772, 0xcb95724f, 0x7af4d123, 0x824db164,
    0x206695e4, 0x742886cd, 0x884979bc, 0x93e6b99f, 0xfc700b23, 0xbfcc1f26,
    0xbe115398, 0x1bedb018, 0x33e873c8, 0x8e4583b9, 0x666f2c03, 0x280ede59,
    0x6a76acdc, 0xb2cd4058, 0xa25ce17f, 0xc24789ff, 0xd69f0f98, 0xee4622f0,
    0x6cb3bd85, 0xb8d5ccb1, 0xcdb605eb, 0x4de47a43, 0x7bda0c86, 0x8b83c71e,
    0x31837e6a, 0xb02d0228, 0x9be7eb6e, 0xe1746942, 0xb6b48e76, 0xbf8c79d3,
    0xd81b2383, 0x9e277621, 0x8c4ca670, 0xcfa2b928, 0xd60f0279, 0x2e1fdefe,
};
static uint32_t kTestPublicExponent = 65537;

// Message data for testing.
static const unsigned char kTestMessage[] = "Test message.";
static const size_t kTestMessageLen = sizeof(kTestMessage) - 1;

// Valid signature of `kTestMessage` from the test private key, using PKCS#1
// v1.5 padding and SHA-512 as the hash function.
static const uint32_t kValidSignaturePkcs1v15[kRsa3072NumWords] = {
    0xb091ff65, 0xd1edc6a5, 0x574498d4, 0x2d6e34d9, 0xb96eb9fe, 0x48194af9,
    0x8973e3bd, 0x6f66bc1d, 0x55032373, 0x68d5ced7, 0x87998790, 0xe86f7eb1,
    0x0f07e31b, 0x2842ada5, 0x2af683ab, 0x55245677, 0x4ac777e8, 0x130aa2d6,
    0x0f7eebb5, 0x9dfa75db, 0x41bbe218, 0xf4f7a2d7, 0xff153220, 0x6e6cd5e8,
    0xa44fd6b5, 0xfe085392, 0x60e2b298, 0x1c5f74f4, 0x032e2d39, 0xd1c16723,
    0xa6ae5514, 0x357c60b7, 0x61a51bbc, 0x009391dd, 0x0142d92e, 0xd1593a14,
    0xbffd75c3, 0x55fdbde2, 0x40533d4b, 0xb423ded9, 0x83106eee, 0x0a6bd1cc,
    0x9c85a4cb, 0xfa1da7fe, 0x09b79f0c, 0x6ca08324, 0xa3182ce5, 0x9d9ee66d,
    0x94213c86, 0x9ac854b3, 0x8803ad55, 0xc3ad2e23, 0x7f11620c, 0x56032b2d,
    0xac4e36be, 0x553b2d2c, 0xc489cec1, 0x40846292, 0x9b4849fd, 0x0d63a0f4,
    0x27abfa17, 0xec055e10, 0x310e3ef2, 0x953a6701, 0xf844985e, 0x2944b2df,
    0x37c9097d, 0xcd40700e, 0x57759607, 0xdda27413, 0x77a65ad3, 0x8752df0c,
    0x50329618, 0x14b74fa7, 0xc9236c54, 0xb8f07265, 0x5b9efc20, 0x15f5f821,
    0xde9ca767, 0x34bf1a70, 0xca4d5d9c, 0x92725953, 0x998d1231, 0x73bd12aa,
    0xc222b65f, 0xde00db56, 0xc9e1aaff, 0xb2d32c27, 0x05b93bb4, 0x94b52732,
    0xbdc53790, 0x92e62a85, 0xc1cb4a8a, 0xff3fe179, 0x565f6d7f, 0x0f784c4a,
};

// Valid signature of `kTestMessage` from the test private key, using PSS
// padding and SHA-512 as the hash function.
static const uint32_t kValidSignaturePss[kRsa3072NumWords] = {
    0xff478de6, 0x9c32afcc, 0x606818a2, 0x10a3510f, 0x474819ee, 0x04be7c07,
    0xd8bd7511, 0xcf392927, 0x6883efcd, 0x15986843, 0x26e311b9, 0x27d718ac,
    0xc507b105, 0xfd519ef7, 0x1dd94e1e, 0x4bc8e633, 0x9c4acb4d, 0x21719940,
    0x7c7b6449, 0x998cd74f, 0xd33c1989, 0x5ef49d96, 0x63e111b0, 0xcca6d7f5,
    0x75c80acb, 0x07e8907d, 0x3e9d3fcd, 0x493a518e, 0x73aab881, 0xabdc13cc,
    0x81ed48f2, 0x12395425, 0x7957265f, 0xde23f84b, 0xa7a51962, 0xbceac204,
    0x1291a9bd, 0x72c83723, 0x9a110ca7, 0x46db7dcc, 0x8af37092, 0x27e9eacd,
    0xe37be422, 0xeded8b48, 0xdaa20d27, 0xb855507b, 0xe5d45f30, 0x15d6e2e4,
    0x795c88c2, 0xa7f130c7, 0x973ce990, 0x282625f7, 0x08f2ce39, 0xd8a2b491,
    0xea037444, 0x41efd30d, 0x44a69d6a, 0xf59709be, 0xc42b92df, 0x516ab280,
    0xe2f9c7b4, 0xcf3693a8, 0x9b28d5f3, 0x8cbda1ef, 0xa2a05f13, 0x344858e9,
    0xb8372f6a, 0x4bdc6efd, 0x90ecabab, 0xdb0589e8, 0x1d59f90f, 0x531cf1f2,
    0x486f3233, 0x6a946ee8, 0x302a6c49, 0x507dda2b, 0x21287d8f, 0x68ec5762,
    0x81df3cdb, 0x7f0a0851, 0x69f0e825, 0x3bba8632, 0x6a98b6fd, 0xf0bdd53d,
    0xc9d928a1, 0x6501fded, 0x0e4d8b0b, 0x11ffdc3a, 0xda6a6fa8, 0x567a7e65,
    0xe2f6c106, 0x4569d9c9, 0x3d69f35e, 0x6d1ebc67, 0x0f4ecb9a, 0x31628ec0,
};

/**
 * Helper function to run the RSA-3072 signing routine.
 *
 * Packages input into cryptolib-style structs and calls `otcrypto_rsa_sign`
 * using the constant test private key. Always uses SHA-512 as the hash
 * function.
 *
 * @param msg Message to sign.
 * @param msg_len Message length in bytes.
 * @param padding_mode RSA padding mode.
 * @param[out] sig Buffer for the generated RSA signature (3072 bits).
 * @return OK or error.
 */
static status_t run_rsa_3072_sign(const uint8_t *msg, size_t msg_len,
                                  rsa_padding_t padding_mode, uint32_t *sig) {
  key_mode_t key_mode;
  switch (padding_mode) {
    case kRsaPaddingPkcs:
      key_mode = kKeyModeRsaSignPkcs;
      break;
    case kRsaPaddingPss:
      key_mode = kKeyModeRsaSignPss;
      break;
    default:
      return INVALID_ARGUMENT();
  };

  crypto_key_config_t private_key_config = {
      .version = kCryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = kRsa3072NumBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kSecurityLevelLow,
  };

  rsa_private_key_t private_key = {
      .n = {.key_mode = key_mode,
            .key_length = sizeof(kTestModulus),
            .key = kTestModulus,
            .checksum = 0},
      .d = {.config = private_key_config,
            .keyblob = kTestPrivateExponent,
            .keyblob_length = sizeof(kTestPrivateExponent),
            .checksum = 0},
  };

  private_key.n.checksum = integrity_unblinded_checksum(&private_key.n);
  private_key.d.checksum = integrity_blinded_checksum(&private_key.d);

  // Hash the message.
  crypto_const_byte_buf_t msg_buf = {.data = msg, .len = msg_len};
  uint32_t msg_digest_data[kSha512DigestWords];
  hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
      .mode = kHashModeSha512,
  };
  TRY(otcrypto_hash(msg_buf, &msg_digest));

  crypto_word32_buf_t sig_buf = {
      .data = sig,
      .len = kRsa3072NumWords,
  };

  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_sign(&private_key, &msg_digest, padding_mode, &sig_buf));
  profile_end_and_print(t_start, "RSA signature generation");

  return OK_STATUS();
}

/**
 * Helper function to run the RSA-3072 verification routine.
 *
 * Packages input into cryptolib-style structs and calls `otcrypto_rsa_verify`
 * using the constant test public key. Always uses SHA-512 as the hash
 * function.
 *
 * @param msg Message to verify.
 * @param msg_len Message length in bytes.
 * @param sig Signature to verify
 * @param padding_mode RSA padding mode.
 * @param[out] verification_result Whether the signature passed verification.
 * @return OK or error.
 */
static status_t run_rsa_3072_verify(const uint8_t *msg, size_t msg_len,
                                    const uint32_t *sig,
                                    const rsa_padding_t padding_mode,
                                    hardened_bool_t *verification_result) {
  key_mode_t key_mode;
  switch (padding_mode) {
    case kRsaPaddingPkcs:
      key_mode = kKeyModeRsaSignPkcs;
      break;
    case kRsaPaddingPss:
      key_mode = kKeyModeRsaSignPss;
      break;
    default:
      return INVALID_ARGUMENT();
  };

  rsa_public_key_t public_key = {
      .n = {.key_mode = key_mode,
            .key_length = sizeof(kTestModulus),
            .key = kTestModulus,
            .checksum = 0},
      .e = {.key_mode = key_mode,
            .key_length = sizeof(kTestPublicExponent),
            .key = &kTestPublicExponent,
            .checksum = 0},
  };

  public_key.n.checksum = integrity_unblinded_checksum(&public_key.n);
  public_key.e.checksum = integrity_unblinded_checksum(&public_key.e);

  // Hash the message.
  crypto_const_byte_buf_t msg_buf = {.data = msg, .len = msg_len};
  uint32_t msg_digest_data[kSha512DigestWords];
  hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
      .mode = kHashModeSha512,
  };
  TRY(otcrypto_hash(msg_buf, &msg_digest));

  crypto_const_word32_buf_t sig_buf = {
      .data = sig,
      .len = kRsa3072NumWords,
  };

  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_verify(&public_key, &msg_digest, padding_mode, sig_buf,
                          verification_result));
  profile_end_and_print(t_start, "RSA verify");

  return OK_STATUS();
}

status_t pkcs1v15_sign_test(void) {
  // Generate a signature using PKCS#1 v1.5 padding and SHA-512 as the hash
  // function.
  uint32_t sig[kRsa3072NumWords];
  TRY(run_rsa_3072_sign(kTestMessage, kTestMessageLen, kRsaPaddingPkcs, sig));

  // Compare to the expected signature.
  TRY_CHECK_ARRAYS_EQ(sig, kValidSignaturePkcs1v15,
                      ARRAYSIZE(kValidSignaturePkcs1v15));
  return OK_STATUS();
}

status_t pkcs1v15_verify_valid_test(void) {
  // Try to verify a valid signature.
  hardened_bool_t verification_result;
  TRY(run_rsa_3072_verify(kTestMessage, kTestMessageLen,
                          kValidSignaturePkcs1v15, kRsaPaddingPkcs,
                          &verification_result));

  // Expect the signature to pass verification.
  TRY_CHECK(verification_result == kHardenedBoolTrue);
  return OK_STATUS();
}

status_t pkcs1v15_verify_invalid_test(void) {
  // Try to verify an invalid signature (wrong padding mode).
  hardened_bool_t verification_result;
  TRY(run_rsa_3072_verify(kTestMessage, kTestMessageLen, kValidSignaturePss,
                          kRsaPaddingPkcs, &verification_result));

  // Expect the signature to fail verification.
  TRY_CHECK(verification_result == kHardenedBoolFalse);
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t test_result = OK_STATUS();
  EXECUTE_TEST(test_result, pkcs1v15_sign_test);
  EXECUTE_TEST(test_result, pkcs1v15_verify_valid_test);
  EXECUTE_TEST(test_result, pkcs1v15_verify_invalid_test);
  return status_ok(test_result);
}
