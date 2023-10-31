// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
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
  kSha256DigestWords = 256 / 32,
  kRsa2048NumBytes = 2048 / 8,
  kRsa2048NumWords = kRsa2048NumBytes / sizeof(uint32_t),
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

// Message data for testing.
static const unsigned char kTestMessage[] = "Test message.";
static const size_t kTestMessageLen = sizeof(kTestMessage) - 1;

// Valid signature of `kTestMessage` from the test private key, using PKCS#1
// v1.5 padding and SHA-256 as the hash function.
static const uint32_t kValidSignaturePkcs1v15[kRsa2048NumWords] = {
    0xab66c6c7, 0x97effc0a, 0x9869cdba, 0x7b6c09fe, 0x2124d28f, 0x793084b3,
    0x4da24b72, 0x4f6c8659, 0x63e3a27b, 0xbbe8d120, 0x8789190f, 0x1722fe46,
    0x25573178, 0x3accbdb3, 0x1eb7ca00, 0xe8eb40aa, 0x1d3b21a8, 0x9997925e,
    0x1793f81d, 0x12728f54, 0x66e40608, 0x4b1057a0, 0xba433eb3, 0x702c73b2,
    0xa9391740, 0xf838710f, 0xf33cf109, 0x595cee1d, 0x07341be9, 0xcfce52b1,
    0x5b48ba7a, 0xf70e5a0e, 0xdbb98c42, 0x85fd6979, 0xcdb760fc, 0xd2e09553,
    0x70bba417, 0x04e52609, 0xc215420e, 0x2407242e, 0x4f19674b, 0x5d996a9d,
    0xf2fb1d05, 0x88e0fc14, 0xe1a38f0c, 0xd111935d, 0xd23bf5b3, 0xdcd7a882,
    0x0f242315, 0xd7247d51, 0xc247d6ec, 0xe2492739, 0x3dfb115c, 0x031aea7a,
    0xcdcb09c0, 0x29318ddb, 0xd0a10dd8, 0x3307018e, 0xe13c5616, 0x98d4db80,
    0x50692a42, 0x41e94a74, 0x0a6f79eb, 0x1c405c66,
};

// Valid signature of `kTestMessage` from the test private key, using PSS
// padding and SHA-256 as the hash function.
static const uint32_t kValidSignaturePss[kRsa2048NumWords] = {
    0x6203140a, 0xa860e759, 0x65ddb724, 0x2b4eedfa, 0xf11d5e65, 0xa6ab5601,
    0x14097f2e, 0x56f9dda5, 0xcb43ebcc, 0x7914036d, 0x83e99afd, 0x323187a7,
    0x6f239172, 0x0fc9f25a, 0xe83555a7, 0xd12997e2, 0x65dcd504, 0x99ebef85,
    0x4a5f2679, 0xedf106d8, 0x68c21486, 0xeb7edb37, 0x33e22631, 0xf23699ae,
    0x679b750e, 0xb5c09869, 0x72f7ccd0, 0xef503c8f, 0xa0225545, 0x86554913,
    0xbce86ec4, 0x75f846d2, 0xf16318a8, 0xbce00097, 0x170a418f, 0x558e2f9f,
    0xed555d51, 0x061b6074, 0x859c0bb6, 0xb2800a5a, 0x0180afd3, 0x41f0a2d6,
    0xc75b12ff, 0xaa6179f7, 0x63e71a9a, 0xbdbd759e, 0xe39d7372, 0xa579683f,
    0x8db987a5, 0x8bd0e702, 0x8b32ed36, 0x988e28ee, 0x21c3402d, 0x48490be0,
    0xcbfb2e91, 0x1ba04f77, 0x0ca06d1d, 0xcf2a8645, 0xed3f78e4, 0x4483da1d,
    0x2df279d7, 0xada9475e, 0x6ec0863d, 0x94eb575c,
};

/**
 * Helper function to run the RSA-2048 signing routine.
 *
 * Packages input into cryptolib-style structs and calls `otcrypto_rsa_sign`
 * using the constant test private key.
 *
 * @param msg Message to sign.
 * @param msg_len Message length in bytes.
 * @param padding_mode RSA padding mode.
 * @param hash_mode Hash function to use.
 * @param[out] sig Buffer for the generated RSA signature (2048 bits).
 * @return OK or error.
 */
static status_t run_rsa_2048_sign(const uint8_t *msg, size_t msg_len,
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
      .key_length = kRsa2048NumBytes,
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
  uint32_t msg_digest_data[kSha256DigestWords];
  hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
      .mode = kHashModeSha256,
  };
  TRY(otcrypto_hash(msg_buf, &msg_digest));

  crypto_word32_buf_t sig_buf = {
      .data = sig,
      .len = kRsa2048NumWords,
  };
  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_sign(&private_key, &msg_digest, padding_mode, &sig_buf));
  profile_end_and_print(t_start, "RSA signature generation");

  return OK_STATUS();
}

/**
 * Helper function to run the RSA-2048 verification routine.
 *
 * Packages input into cryptolib-style structs and calls `otcrypto_rsa_verify`
 * using the constant test public key. Always uses SHA-256 as the hash
 * function.
 *
 * @param msg Message to verify.
 * @param msg_len Message length in bytes.
 * @param sig Signature to verify
 * @param padding_mode RSA padding mode.
 * @param[out] verification_result Whether the signature passed verification.
 * @return OK or error.
 */
static status_t run_rsa_2048_verify(const uint8_t *msg, size_t msg_len,
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
  uint32_t msg_digest_data[kSha256DigestWords];
  hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
      .mode = kHashModeSha256,
  };
  TRY(otcrypto_hash(msg_buf, &msg_digest));

  crypto_const_word32_buf_t sig_buf = {
      .data = sig,
      .len = kRsa2048NumWords,
  };
  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_verify(&public_key, &msg_digest, padding_mode, sig_buf,
                          verification_result));
  profile_end_and_print(t_start, "RSA verify");

  return OK_STATUS();
}

status_t pkcs1v15_sign_test(void) {
  // Generate a signature using PKCS#1 v1.5 padding and SHA-256 as the hash
  // function.
  uint32_t sig[kRsa2048NumWords];
  TRY(run_rsa_2048_sign(kTestMessage, kTestMessageLen, kRsaPaddingPkcs, sig));

  // Compare to the expected signature.
  TRY_CHECK_ARRAYS_EQ(sig, kValidSignaturePkcs1v15,
                      ARRAYSIZE(kValidSignaturePkcs1v15));
  return OK_STATUS();
}

status_t pkcs1v15_verify_valid_test(void) {
  // Try to verify a valid signature.
  hardened_bool_t verification_result;
  TRY(run_rsa_2048_verify(kTestMessage, kTestMessageLen,
                          kValidSignaturePkcs1v15, kRsaPaddingPkcs,
                          &verification_result));

  // Expect the signature to pass verification.
  TRY_CHECK(verification_result == kHardenedBoolTrue);
  return OK_STATUS();
}

status_t pkcs1v15_verify_invalid_test(void) {
  // Try to verify an invalid signature (wrong padding mode).
  hardened_bool_t verification_result;
  TRY(run_rsa_2048_verify(kTestMessage, kTestMessageLen, kValidSignaturePss,
                          kRsaPaddingPkcs, &verification_result));

  // Expect the signature to fail verification.
  TRY_CHECK(verification_result == kHardenedBoolFalse);
  return OK_STATUS();
}

status_t pss_sign_test(void) {
  // PSS signatures are not deterministic, so we need to sign-then-verify.
  uint32_t sig[kRsa2048NumWords];
  TRY(run_rsa_2048_sign(kTestMessage, kTestMessageLen, kRsaPaddingPss, sig));

  // Try to verify the signature.
  hardened_bool_t verification_result;
  TRY(run_rsa_2048_verify(kTestMessage, kTestMessageLen, sig, kRsaPaddingPss,
                          &verification_result));

  // Expect the signature to pass verification.
  TRY_CHECK(verification_result == kHardenedBoolTrue);
  return OK_STATUS();
}

status_t pss_verify_valid_test(void) {
  // Try to verify a valid signature.
  hardened_bool_t verification_result;
  TRY(run_rsa_2048_verify(kTestMessage, kTestMessageLen, kValidSignaturePss,
                          kRsaPaddingPss, &verification_result));

  // Expect the signature to pass verification.
  TRY_CHECK(verification_result == kHardenedBoolTrue);
  return OK_STATUS();
}

status_t pss_verify_invalid_test(void) {
  // Try to verify an invalid signature (wrong padding mode).
  hardened_bool_t verification_result;
  TRY(run_rsa_2048_verify(kTestMessage, kTestMessageLen,
                          kValidSignaturePkcs1v15, kRsaPaddingPss,
                          &verification_result));

  // Expect the signature to fail verification.
  TRY_CHECK(verification_result == kHardenedBoolFalse);
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t test_result = OK_STATUS();
  CHECK_STATUS_OK(entropy_complex_init());
  EXECUTE_TEST(test_result, pkcs1v15_sign_test);
  EXECUTE_TEST(test_result, pkcs1v15_verify_valid_test);
  EXECUTE_TEST(test_result, pkcs1v15_verify_invalid_test);
  EXECUTE_TEST(test_result, pss_sign_test);
  EXECUTE_TEST(test_result, pss_verify_valid_test);
  EXECUTE_TEST(test_result, pss_verify_invalid_test);
  return status_ok(test_result);
}
