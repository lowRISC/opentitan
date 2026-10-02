// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/crypto/include/sha3.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/profile.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module for status messages.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

enum {
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
 * Helper function to compute a message digest for various hash modes.
 */
static status_t compute_digest(const otcrypto_const_byte_buf_t *msg,
                               otcrypto_hash_mode_t hash_mode,
                               otcrypto_hash_digest_t *digest) {
  digest->mode = hash_mode;
  switch (hash_mode) {
    case kOtcryptoHashModeSha256:
      digest->len = 256 / 32;
      return otcrypto_sha2_256(msg, digest);
    case kOtcryptoHashModeSha384:
      digest->len = 384 / 32;
      return otcrypto_sha2_384(msg, digest);
    case kOtcryptoHashModeSha512:
      digest->len = 512 / 32;
      return otcrypto_sha2_512(msg, digest);
    case kOtcryptoHashModeSha3_224:
      digest->len = 224 / 32;
      return otcrypto_sha3_224(msg, digest);
    case kOtcryptoHashModeSha3_256:
      digest->len = 256 / 32;
      return otcrypto_sha3_256(msg, digest);
    case kOtcryptoHashModeSha3_384:
      digest->len = 384 / 32;
      return otcrypto_sha3_384(msg, digest);
    case kOtcryptoHashModeSha3_512:
      digest->len = 512 / 32;
      return otcrypto_sha3_512(msg, digest);
    default:
      return INVALID_ARGUMENT();
  }
}

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
                                  otcrypto_rsa_padding_t padding_mode,
                                  otcrypto_hash_mode_t hash_mode,
                                  uint32_t *sig) {
  otcrypto_key_mode_t key_mode;
  switch (padding_mode) {
    case kOtcryptoRsaPaddingPkcs:
      key_mode = kOtcryptoKeyModeRsaSignPkcs;
      break;
    case kOtcryptoRsaPaddingPss:
      key_mode = kOtcryptoKeyModeRsaSignPss;
      break;
    default:
      return INVALID_ARGUMENT();
  };

  // Create two shares for the private exponent.
  otcrypto_const_word32_buf_t d_share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kTestPrivateExponent,
                        ARRAYSIZE(kTestPrivateExponent));
  uint32_t share1[ARRAYSIZE(kTestPrivateExponent)] = {0};
  otcrypto_const_word32_buf_t d_share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share1, ARRAYSIZE(share1));

  // Construct the private key.
  otcrypto_key_config_t private_key_config = {
      .version = otcrypto_lib_version(),
      .key_mode = key_mode,
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
  otcrypto_const_word32_buf_t modulus = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kTestModulus, ARRAYSIZE(kTestModulus));
  TRY(otcrypto_rsa_private_key_from_exponents(
      kOtcryptoRsaSize2048, &modulus, &d_share0, &d_share1, &private_key));

  // Hash the message dynamically.
  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg, msg_len);
  uint32_t msg_digest_data[512 / 32];  // Accommodates up to SHA-512
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
  };
  TRY(compute_digest(&msg_buf, hash_mode, &msg_digest));

  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, kRsa2048NumWords);
  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_sign(&private_key, msg_digest, padding_mode, &sig_buf));
  profile_end_and_print(t_start, "RSA signature generation");
  LOG_INFO("OTBN sign instruction count: 0x%08x", otbn_instruction_count_get());

  return OK_STATUS();
}

/**
 * Helper function to run the RSA-2048 verification routine.
 */
static status_t run_rsa_2048_verify(const uint8_t *msg, size_t msg_len,
                                    const uint32_t *sig,
                                    const otcrypto_rsa_padding_t padding_mode,
                                    otcrypto_hash_mode_t hash_mode,
                                    hardened_bool_t *verification_result) {
  otcrypto_key_mode_t key_mode;
  switch (padding_mode) {
    case kOtcryptoRsaPaddingPkcs:
      key_mode = kOtcryptoKeyModeRsaSignPkcs;
      break;
    case kOtcryptoRsaPaddingPss:
      key_mode = kOtcryptoKeyModeRsaSignPss;
      break;
    default:
      return INVALID_ARGUMENT();
  };

  // Construct the public key.
  otcrypto_const_word32_buf_t modulus = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kTestModulus, ARRAYSIZE(kTestModulus));
  uint32_t public_key_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes,
                                    sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = key_mode,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = public_key_data,
  };
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &modulus,
                                        &public_key));

  // Hash the message dynamically.
  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg, msg_len);
  uint32_t msg_digest_data[512 / 32];  // Accommodates up to SHA-512
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
  };
  TRY(compute_digest(&msg_buf, hash_mode, &msg_digest));

  otcrypto_const_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, kRsa2048NumWords);
  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_verify(&public_key, msg_digest, padding_mode, &sig_buf,
                          verification_result));
  profile_end_and_print(t_start, "RSA verify");
  LOG_INFO("OTBN verify instruction count: 0x%08x",
           otbn_instruction_count_get());

  return OK_STATUS();
}

status_t pkcs1v15_sign_test(void) {
  // Generate a signature using PKCS#1 v1.5 padding and SHA-256 as the hash
  // function.
  uint32_t sig[kRsa2048NumWords];
  // Note the added kOtcryptoHashModeSha256 parameter here
  TRY(run_rsa_2048_sign(kTestMessage, kTestMessageLen, kOtcryptoRsaPaddingPkcs,
                        kOtcryptoHashModeSha256, sig));

  // Compare to the expected signature.
  TRY_CHECK_ARRAYS_EQ(sig, kValidSignaturePkcs1v15,
                      ARRAYSIZE(kValidSignaturePkcs1v15));
  return OK_STATUS();
}

status_t pkcs1v15_verify_valid_test(void) {
  // Try to verify a valid signature.
  hardened_bool_t verification_result;
  TRY(run_rsa_2048_verify(kTestMessage, kTestMessageLen,
                          kValidSignaturePkcs1v15, kOtcryptoRsaPaddingPkcs,
                          kOtcryptoHashModeSha256, &verification_result));

  // Expect the signature to pass verification.
  TRY_CHECK(verification_result == kHardenedBoolTrue);

  // Also test otcrypto_rsa_hash_sign_verify and otcrypto_rsa_hash_verify.
  otcrypto_const_word32_buf_t modulus = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kTestModulus, ARRAYSIZE(kTestModulus));
  otcrypto_const_word32_buf_t d_share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kTestPrivateExponent,
                        ARRAYSIZE(kTestPrivateExponent));
  uint32_t share1[ARRAYSIZE(kTestPrivateExponent)] = {0};
  otcrypto_const_word32_buf_t d_share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share1, ARRAYSIZE(share1));
  uint32_t public_key_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes,
                                    sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = public_key_data,
  };
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &modulus,
                                        &public_key));
  otcrypto_key_config_t private_key_config = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa2048PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t
      keyblob[ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes, sizeof(uint32_t))];
  otcrypto_blinded_key_t private_key = {
      .config = private_key_config,
      .keyblob = keyblob,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
  };
  TRY(otcrypto_rsa_private_key_from_exponents(
      kOtcryptoRsaSize2048, &modulus, &d_share0, &d_share1, &private_key));

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kTestMessage, kTestMessageLen);
  uint32_t sig[kRsa2048NumWords];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, kRsa2048NumWords);
  TRY(otcrypto_rsa_hash_sign_verify(&private_key, &public_key,
                                    kOtcryptoHashModeSha256, &msg_buf,
                                    kOtcryptoRsaPaddingPkcs, &sig_buf));
  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, kRsa2048NumWords);
  verification_result = kHardenedBoolFalse;
  TRY(otcrypto_rsa_hash_verify(&public_key, kOtcryptoHashModeSha256, &msg_buf,
                               kOtcryptoRsaPaddingPkcs, &const_sig_buf,
                               &verification_result));
  TRY_CHECK(verification_result == kHardenedBoolTrue);

  return OK_STATUS();
}

status_t pkcs1v15_verify_invalid_test(void) {
  // Try to verify an invalid signature (wrong padding mode).
  hardened_bool_t verification_result;
  TRY(run_rsa_2048_verify(kTestMessage, kTestMessageLen, kValidSignaturePss,
                          kOtcryptoRsaPaddingPkcs, kOtcryptoHashModeSha256,
                          &verification_result));

  // Expect the signature to fail verification.
  TRY_CHECK(verification_result == kHardenedBoolFalse);
  return OK_STATUS();
}

status_t pss_verify_valid_test(void) {
  // Try to verify a valid signature.
  hardened_bool_t verification_result;
  TRY(run_rsa_2048_verify(kTestMessage, kTestMessageLen, kValidSignaturePss,
                          kOtcryptoRsaPaddingPss, kOtcryptoHashModeSha256,
                          &verification_result));

  // Expect the signature to pass verification.
  TRY_CHECK(verification_result == kHardenedBoolTrue);
  return OK_STATUS();
}

status_t pss_verify_invalid_test(void) {
  // Try to verify an invalid signature (wrong padding mode).
  hardened_bool_t verification_result;
  TRY(run_rsa_2048_verify(kTestMessage, kTestMessageLen,
                          kValidSignaturePkcs1v15, kOtcryptoRsaPaddingPss,
                          kOtcryptoHashModeSha256, &verification_result));

  // Expect the signature to fail verification.
  TRY_CHECK(verification_result == kHardenedBoolFalse);
  return OK_STATUS();
}

static status_t run_signature_negative_tests(void) {
  LOG_INFO("Running RSA signature negative tests");

  uint32_t pub_data[kOtcryptoRsa2048PublicKeyBytes / 4] = {0};
  otcrypto_unblinded_key_t valid_pub = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_data,
  };
  valid_pub.checksum = otcrypto_integrity_unblinded_checksum(&valid_pub);

  uint32_t priv_blob[kOtcryptoRsa2048PrivateKeyblobBytes / 4] = {0};
  otcrypto_blinded_key_t valid_priv = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeRsaSignPkcs,
              .key_length = kOtcryptoRsa2048PrivateKeyBytes,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };
  valid_priv.checksum = otcrypto_integrity_blinded_checksum(&valid_priv);

  uint32_t digest_data[256 / 32] = {0};
  otcrypto_hash_digest_t valid_digest = {.data = digest_data,
                                         .len = ARRAYSIZE(digest_data)};

  uint32_t sig_data[kRsa2048NumWords] = {0};
  otcrypto_word32_buf_t valid_sig =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig_data, kRsa2048NumWords);
  otcrypto_const_word32_buf_t valid_const_sig = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, sig_data, kRsa2048NumWords);

  hardened_bool_t verify_res;

  // Sign negative tests

  // Null pointers
  CHECK(
      otcrypto_rsa_sign(NULL, valid_digest, kOtcryptoRsaPaddingPkcs, &valid_sig)
          .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(
      otcrypto_rsa_sign_async_start(NULL, valid_digest, kOtcryptoRsaPaddingPkcs)
          .value != OTCRYPTO_OK.value);

  otcrypto_word32_buf_t bad_sig_null =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, NULL, kRsa2048NumWords);
  CHECK(otcrypto_rsa_sign(&valid_priv, valid_digest, kOtcryptoRsaPaddingPkcs,
                          &bad_sig_null)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_sign_async_finalize(&bad_sig_null).value !=
        OTCRYPTO_OK.value);

  // Corrupt checksum
  otcrypto_blinded_key_t bad_priv_chk = {
      .config = valid_priv.config,
      .keyblob_length = valid_priv.keyblob_length,
      .keyblob = priv_blob,
  };
  bad_priv_chk.checksum = valid_priv.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_rsa_sign(&bad_priv_chk, valid_digest, kOtcryptoRsaPaddingPkcs,
                          &valid_sig)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_sign_async_start(&bad_priv_chk, valid_digest,
                                      kOtcryptoRsaPaddingPkcs)
            .value != OTCRYPTO_OK.value);

  // Mismatched padding mode
  CHECK(otcrypto_rsa_sign(&valid_priv, valid_digest, kOtcryptoRsaPaddingPss,
                          &valid_sig)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_sign_async_start(&valid_priv, valid_digest,
                                      kOtcryptoRsaPaddingPss)
            .value != OTCRYPTO_OK.value);

  // Verify negative tests

  // Null pointers
  CHECK(otcrypto_rsa_verify(NULL, valid_digest, kOtcryptoRsaPaddingPkcs,
                            &valid_const_sig, &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_verify_async_start(NULL, &valid_const_sig).value !=
        OTCRYPTO_OK.value);

  CHECK(otcrypto_rsa_verify(&valid_pub, valid_digest, kOtcryptoRsaPaddingPkcs,
                            &valid_const_sig, NULL)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_verify_async_finalize(valid_digest,
                                           kOtcryptoRsaPaddingPkcs, NULL)
            .value != OTCRYPTO_OK.value);

  // Corrupt checksum
  otcrypto_unblinded_key_t bad_pub_chk = {
      .key_mode = valid_pub.key_mode,
      .key_length = valid_pub.key_length,
      .key = pub_data,
  };
  bad_pub_chk.checksum = valid_pub.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_rsa_verify(&bad_pub_chk, valid_digest, kOtcryptoRsaPaddingPkcs,
                            &valid_const_sig, &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_verify_async_start(&bad_pub_chk, &valid_const_sig).value !=
        OTCRYPTO_OK.value);

  // Bad signature length
  otcrypto_const_word32_buf_t bad_const_sig_len =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig_data, 99);
  CHECK(otcrypto_rsa_verify(&valid_pub, valid_digest, kOtcryptoRsaPaddingPkcs,
                            &bad_const_sig_len, &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_verify_async_start(&valid_pub, &bad_const_sig_len).value !=
        OTCRYPTO_OK.value);

  // Bad signature length in sign_async_finalize
  otcrypto_word32_buf_t bad_sig_len =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig_data, kRsa2048NumWords - 1);
  CHECK(otcrypto_rsa_sign_async_finalize(&bad_sig_len).value !=
        OTCRYPTO_OK.value);

  // Bad digest length for the specified hash mode
  // SHA-256 expects 8 words. Passing 7 triggers the digest_check length
  // failure.
  otcrypto_hash_digest_t bad_digest_len = {
      .data = digest_data, .len = 7, .mode = kOtcryptoHashModeSha256};
  CHECK(otcrypto_rsa_sign(&valid_priv, bad_digest_len, kOtcryptoRsaPaddingPkcs,
                          &valid_sig)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_verify(&valid_pub, bad_digest_len, kOtcryptoRsaPaddingPkcs,
                            &valid_const_sig, &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Unrecognized padding mode
  CHECK(otcrypto_rsa_sign(&valid_priv, valid_digest,
                          (otcrypto_rsa_padding_t)999, &valid_sig)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_verify(&valid_pub, valid_digest,
                            (otcrypto_rsa_padding_t)999, &valid_const_sig,
                            &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Unrecognized hash mode
  otcrypto_hash_digest_t bad_hash_mode = {
      .data = digest_data,
      .len = ARRAYSIZE(digest_data),
      .mode = (otcrypto_hash_mode_t)999  // Invalid mode
  };
  CHECK(otcrypto_rsa_sign(&valid_priv, bad_hash_mode, kOtcryptoRsaPaddingPkcs,
                          &valid_sig)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_verify(&valid_pub, bad_hash_mode, kOtcryptoRsaPaddingPkcs,
                            &valid_const_sig, &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Invalid custom public exponents (< 3 or even) must be rejected.
  const uint32_t kBadExps[] = {0, 1, 2, 4, 65536};
  for (size_t i = 0; i < ARRAYSIZE(kBadExps); i++) {
    CHECK(otcrypto_rsa_sign_exp(&valid_priv, kBadExps[i], valid_digest,
                                kOtcryptoRsaPaddingPkcs, &valid_sig)
              .value == OTCRYPTO_BAD_ARGS.value);
    CHECK(otcrypto_rsa_verify_exp(&valid_pub, kBadExps[i], valid_digest,
                                  kOtcryptoRsaPaddingPkcs, &valid_const_sig,
                                  &verify_res)
              .value == OTCRYPTO_BAD_ARGS.value);
  }

  return OTCRYPTO_OK;
}

status_t all_hashes_sign_verify_test(void) {
  static const otcrypto_hash_mode_t kHashModes[] = {
      kOtcryptoHashModeSha256,   kOtcryptoHashModeSha384,
      kOtcryptoHashModeSha512,   kOtcryptoHashModeSha3_224,
      kOtcryptoHashModeSha3_256, kOtcryptoHashModeSha3_384,
      kOtcryptoHashModeSha3_512,
  };

  for (size_t i = 0; i < ARRAYSIZE(kHashModes); i++) {
    otcrypto_hash_mode_t hash_mode = kHashModes[i];
    uint32_t sig[kRsa2048NumWords];
    hardened_bool_t verification_result;

    // Test PKCS#1 v1.5 dynamically
    TRY(run_rsa_2048_sign(kTestMessage, kTestMessageLen,
                          kOtcryptoRsaPaddingPkcs, hash_mode, sig));
    TRY(run_rsa_2048_verify(kTestMessage, kTestMessageLen, sig,
                            kOtcryptoRsaPaddingPkcs, hash_mode,
                            &verification_result));
    TRY_CHECK(verification_result == kHardenedBoolTrue);

    // Test PSS dynamically
    TRY(run_rsa_2048_sign(kTestMessage, kTestMessageLen, kOtcryptoRsaPaddingPss,
                          hash_mode, sig));
    TRY(run_rsa_2048_verify(kTestMessage, kTestMessageLen, sig,
                            kOtcryptoRsaPaddingPss, hash_mode,
                            &verification_result));
    TRY_CHECK(verification_result == kHardenedBoolTrue);
  }

  // Encrypt Finalize: Bad Ciphertext Length
  uint32_t fake_ct_data[kRsa2048NumWords];
  otcrypto_word32_buf_t bad_ct_len = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, fake_ct_data, 999);  // Unrecognized length
  CHECK(otcrypto_rsa_encrypt_async_finalize(&bad_ct_len).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Sign Finalize: Bad Signature Length
  uint32_t fake_sig_data[kRsa2048NumWords];
  otcrypto_word32_buf_t bad_sig_len = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, fake_sig_data, 999);  // Unrecognized length
  CHECK(otcrypto_rsa_sign_async_finalize(&bad_sig_len).value ==
        OTCRYPTO_BAD_ARGS.value);

  return OK_STATUS();
}

// Test RSA-2048 key pair with custom public exponent e = 3.
static uint32_t kTestModulusE3[kRsa2048NumWords] = {
    0x3a0edbcf, 0xdbb6892a, 0xbe90c222, 0xa72c285d, 0x442a16b4, 0x760b0a2f,
    0xdcbfb450, 0x87f255c1, 0x55a4aca1, 0xc5a78419, 0x9cda964c, 0x7a5e131e,
    0x1e7ddad0, 0xf5cf5e9f, 0x43b5f097, 0xdac45def, 0x3df1c0c9, 0xf0108b6a,
    0x469d21bb, 0x962b70ec, 0x55033d6d, 0xdc7e602a, 0x8a21c566, 0xdc13db70,
    0x600ffc41, 0x297437b6, 0x37669500, 0x5a74e28d, 0x35eb62b8, 0xf7a93cc3,
    0x7bdd0548, 0xc5495f72, 0x8f52bde4, 0x80749ff9, 0x842530bf, 0x7c23ab00,
    0x0d2f3e72, 0x5bcf274e, 0xe4bed76c, 0x427a05b5, 0x57db6b3c, 0x682aeb51,
    0x32f0c35b, 0xd9b88030, 0xb19e36bd, 0x61c74fd9, 0xd56fdcff, 0xb5da9c83,
    0x4fcca390, 0x32cb3c9d, 0xa304093b, 0x7fa58848, 0xae5e15d3, 0x3e664e3d,
    0x878c6185, 0xee24bac4, 0x2f5951b3, 0x0f4b3195, 0xb0907dd9, 0xf6da23ae,
    0xa5305c9a, 0xf84511d0, 0x1886fafa, 0xc8ddfbf6,
};
static uint32_t kTestPrivateExponentE3[kRsa2048NumWords] = {
    0x30cdc15b, 0x9e3723d1, 0x405c9c18, 0xcc7f2ce9, 0xfff765ce, 0xbda009e3,
    0x5469fcef, 0xe7d5445a, 0xa1d5390f, 0x88185187, 0x7ce90459, 0xdbe4926c,
    0x4b2a29e7, 0x04f1719c, 0x7a0e4566, 0xc66cdb68, 0x8c11582b, 0x7e439e05,
    0x4b022d93, 0x839788f4, 0x402247d6, 0x330b059c, 0xfe3900aa, 0x0fdd153d,
    0xb6c0d6ed, 0xeda75ca0, 0x04f5a5e6, 0xe2335e19, 0x891da36a, 0xbd5abfaf,
    0xe1f62b59, 0x0f7c25db, 0xed1205c1, 0xfc22907b, 0x87e218bf, 0x41d2890f,
    0x17ac192a, 0x2991e9eb, 0x44fe0687, 0x1949840d, 0x960e6819, 0x50bb7b7e,
    0x094d1d31, 0xa981b64f, 0xf5de01a8, 0xa5df407a, 0x7312e7aa, 0x340e61d5,
    0xdba15a4a, 0x6e253061, 0xc6e1178d, 0x41edbe4f, 0xd6bd086b, 0x01e411e2,
    0xe513c4e5, 0x7b9481c7, 0xd2e3ad24, 0x5d8dea3a, 0x2461782d, 0xd8ef566a,
    0x1c47489f, 0x3dd38c2d, 0x2f49e893, 0x06163df0,
};
static const uint32_t kValidSignaturePkcs1v15E3[kRsa2048NumWords] = {
    0x7f3ba00b, 0xacb1ab84, 0x31df157b, 0x94c84ff9, 0xf0adbd65, 0x16a35552,
    0x9795e371, 0x65b3ea80, 0x9c4fd319, 0xeed2720d, 0x9b13cf69, 0x4896558a,
    0xbfaf43f2, 0x20140b64, 0x199320e8, 0x5bc6ca71, 0xeeeef4fa, 0xebf4f0fe,
    0xd72b09b0, 0x718c8771, 0x6b26aa5a, 0x0bb39c67, 0xafaab727, 0x487c1806,
    0xe30fbeb2, 0x7825bbdc, 0xf9e0f750, 0x4e8ac5b9, 0x02ff705a, 0x367d9a31,
    0xe4196e3a, 0x9ebaae2c, 0xc3ecdfb8, 0x6dbcd8c2, 0x84911d14, 0xdfdab331,
    0x322d717b, 0x0fa9ff88, 0x936f2393, 0x32dc9e83, 0xc7decc8c, 0x44cfd107,
    0x3ea5f9eb, 0x95434bad, 0x2d4f82d6, 0x41443ba2, 0x0303050c, 0x3c7a0b2b,
    0x11a773f5, 0xfdb3f61f, 0x4cd40275, 0x203934a2, 0x81e3283b, 0xce324cdf,
    0x2aea365a, 0x799ee1db, 0x7ef68115, 0xbcd7d704, 0xbc1d42b4, 0x642e1cf6,
    0xdbeacbf8, 0x4317ed37, 0x79f68c6f, 0x58905761,
};

status_t custom_exp_sign_verify_test(void) {
  LOG_INFO("Running RSA custom-exponent (e=3, e=65537) signature tests");

  otcrypto_const_word32_buf_t modulus_e3 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kTestModulusE3, ARRAYSIZE(kTestModulusE3));
  otcrypto_const_word32_buf_t d_share0_e3 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kTestPrivateExponentE3,
                        ARRAYSIZE(kTestPrivateExponentE3));
  uint32_t share1_e3[ARRAYSIZE(kTestPrivateExponentE3)] = {0};
  otcrypto_const_word32_buf_t d_share1_e3 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1_e3, ARRAYSIZE(share1_e3));

  uint32_t public_key_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes,
                                    sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = public_key_data,
  };
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &modulus_e3,
                                        &public_key));

  otcrypto_key_config_t private_key_config = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
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
  TRY(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048, &modulus_e3,
                                              &d_share0_e3, &d_share1_e3,
                                              &private_key));

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kTestMessage, kTestMessageLen);
  uint32_t msg_digest_data[256 / 32];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
  };
  TRY(compute_digest(&msg_buf, kOtcryptoHashModeSha256, &msg_digest));

  uint32_t sig[kRsa2048NumWords];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, kRsa2048NumWords);

  // 1. Sign with the secret exponent d (passing the associated public exponent
  // e = 3 required for Ebeid-Lambert base blinding) and compare against the
  // known-answer signature.
  TRY(otcrypto_rsa_sign_exp(&private_key, 3, msg_digest,
                            kOtcryptoRsaPaddingPkcs, &sig_buf));
  LOG_INFO("OTBN sign_exp (e=3) instruction count: 0x%08x",
           otbn_instruction_count_get());
  TRY_CHECK_ARRAYS_EQ(sig, kValidSignaturePkcs1v15E3,
                      ARRAYSIZE(kValidSignaturePkcs1v15E3));

  // 2. Verify with public exponent e = 3.
  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, kRsa2048NumWords);
  hardened_bool_t verification_result = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify_exp(&public_key, 3, msg_digest,
                              kOtcryptoRsaPaddingPkcs, &const_sig_buf,
                              &verification_result));
  LOG_INFO("OTBN verify_exp (e=3) instruction count: 0x%08x",
           otbn_instruction_count_get());
  TRY_CHECK(verification_result == kHardenedBoolTrue);

  // 3. Verify with wrong exponent (e = 17) must fail verification.
  verification_result = kHardenedBoolTrue;
  TRY(otcrypto_rsa_verify_exp(&public_key, 17, msg_digest,
                              kOtcryptoRsaPaddingPkcs, &const_sig_buf,
                              &verification_result));
  TRY_CHECK(verification_result == kHardenedBoolFalse);

  // 4. Test PSS sign/verify with the key pair for e = 3.
  public_key.key_mode = kOtcryptoKeyModeRsaSignPss;
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);
  otcrypto_key_config_t private_key_pss_config = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeRsaSignPss,
      .key_length = kOtcryptoRsa2048PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  otcrypto_blinded_key_t private_key_pss = {
      .config = private_key_pss_config,
      .keyblob = keyblob,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
  };
  private_key_pss.checksum =
      otcrypto_integrity_blinded_checksum(&private_key_pss);
  otcrypto_word32_buf_t sig_buf3 =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, kRsa2048NumWords);
  TRY(otcrypto_rsa_sign_exp(&private_key_pss, 3, msg_digest,
                            kOtcryptoRsaPaddingPss, &sig_buf3));
  otcrypto_const_word32_buf_t const_sig_buf3 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, kRsa2048NumWords);
  verification_result = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify_exp(&public_key, 3, msg_digest,
                              kOtcryptoRsaPaddingPss, &const_sig_buf3,
                              &verification_result));
  TRY_CHECK(verification_result == kHardenedBoolTrue);

  // 5. Test sign_exp and verify_exp with e = 65537 against the standard KAT.
  otcrypto_const_word32_buf_t modulus_f4 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kTestModulus, ARRAYSIZE(kTestModulus));
  otcrypto_const_word32_buf_t d_share0_f4 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kTestPrivateExponent,
                        ARRAYSIZE(kTestPrivateExponent));
  public_key.key_mode = kOtcryptoKeyModeRsaSignPkcs;
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &modulus_f4,
                                        &public_key));
  TRY(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048, &modulus_f4,
                                              &d_share0_f4, &d_share1_e3,
                                              &private_key));
  TRY(otcrypto_rsa_sign_exp(&private_key, 65537, msg_digest,
                            kOtcryptoRsaPaddingPkcs, &sig_buf));
  TRY_CHECK_ARRAYS_EQ(sig, kValidSignaturePkcs1v15,
                      ARRAYSIZE(kValidSignaturePkcs1v15));
  verification_result = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify_exp(&public_key, 65537, msg_digest,
                              kOtcryptoRsaPaddingPkcs, &const_sig_buf,
                              &verification_result));
  TRY_CHECK(verification_result == kHardenedBoolTrue);

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t test_result = OK_STATUS();
  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));
  EXECUTE_TEST(test_result, pkcs1v15_sign_test);
  EXECUTE_TEST(test_result, pkcs1v15_verify_valid_test);
  EXECUTE_TEST(test_result, pkcs1v15_verify_invalid_test);
  EXECUTE_TEST(test_result, pss_verify_valid_test);
  EXECUTE_TEST(test_result, pss_verify_invalid_test);
  EXECUTE_TEST(test_result, all_hashes_sign_verify_test);
  EXECUTE_TEST(test_result, run_signature_negative_tests);
  EXECUTE_TEST(test_result, custom_exp_sign_verify_test);
  return status_ok(test_result);
}
