// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/profile.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module for status messages.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

enum {
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

// OAEP label for testing.
static const unsigned char kTestLabel[] = "Test label.";
static const size_t kTestLabelLen = sizeof(kTestLabel) - 1;

// Hash mode for testing (and digest length in bytes).
static const otcrypto_hash_mode_t kTestHashMode = kOtcryptoHashModeSha512;
static const size_t kTestHashModeDigestBytes = 512 / 8;

// Maximum plaintext length for OAEP (see IETF RFC 8017).
static const size_t kMaxPlaintextBytes =
    kRsa3072NumBytes - 2 * kTestHashModeDigestBytes - 2;

// Valid ciphertext for `kTestMessage` with the test private key, using OAEP
// encoding with `kTestLabel` and `kTestHashMode`.
static const uint32_t kValidCiphertext[kRsa3072NumWords] = {
    0x2b57a10f, 0x26bbfdb9, 0x22f881b6, 0x3ea3735c, 0xb97896d8, 0x5ca9f2b9,
    0xd70a4c1a, 0xaf1ead0d, 0xc4b0ae6d, 0x76ae6d9b, 0xcacf7b07, 0xb63f651f,
    0x9fc70de5, 0x5f85a0c0, 0xda3b7882, 0x6c539d54, 0xe5566273, 0xeb461031,
    0xb20242d6, 0x0cfcb276, 0x01b4e765, 0xe6ac1931, 0x82bf7c08, 0xb3aebe9c,
    0x37d2f9cd, 0x0fe684a5, 0x9db2afd2, 0xa99b45e5, 0x17a8aff7, 0x22c56bae,
    0x911f3c58, 0x645e7a67, 0x8833eaa5, 0x11e5d4f0, 0xafff8172, 0x40fc3c4c,
    0x0a261c85, 0x6d623878, 0x30115176, 0x2853df91, 0x2bd02f85, 0xb1958b8e,
    0x9288b3f9, 0x430f8ab2, 0x2556cf3a, 0xe485dbfb, 0xa644d055, 0xe0707828,
    0xbd2aef6b, 0xfeb784a2, 0xe5ebbf8b, 0xa5f8b0fa, 0xb24c0f7b, 0xbfad7a83,
    0x54903942, 0x56a20d38, 0xef1ad9a2, 0xbae1bc9b, 0x235c90c3, 0x3a9bd4ef,
    0x2606ef34, 0x643add05, 0x57bc256c, 0xa45749dd, 0x1784134c, 0x3f553100,
    0x46e3ae90, 0x44552576, 0x4feb281d, 0x4f83b747, 0xa890f513, 0x979afc28,
    0x2addc3f2, 0x45a1064e, 0x9e1ade54, 0x551bf540, 0x4337b81c, 0x24259077,
    0x6ba0c23c, 0xd6d81aab, 0xdf94cc28, 0x679ca168, 0xfc2b4700, 0x5018295b,
    0xb8bf3cce, 0x3afdd992, 0x478989db, 0xfd095c8b, 0xd75b556b, 0x4672dd8c,
    0x7b9dfe21, 0xb615edad, 0xf001b4d9, 0x9e6f9920, 0x58a92869, 0x15125194,
};

/**
 * Helper function to run the RSA-3072 encryption routine.
 *
 * Packages input into cryptolib-style structs and calls `otcrypto_rsa_encrypt`
 * using the constant test private key.
 *
 * @param msg Message to encrypt.
 * @param msg_len Message length in bytes.
 * @param label Label for OAEP padding.
 * @param label_len Label length in bytes.
 * @param[out] ciphertext Buffer for the generated ciphertext (3072 bits).
 * @return OK or error.
 */
static status_t run_rsa_3072_encrypt(const uint8_t *msg, size_t msg_len,
                                     const uint8_t *label, size_t label_len,
                                     uint32_t *ciphertext) {
  // Construct the public key.
  otcrypto_const_word32_buf_t modulus = {
      .data = kTestModulus,
      .len = ARRAYSIZE(kTestModulus),
  };
  uint32_t public_key_data[ceil_div(kOtcryptoRsa3072PublicKeyBytes,
                                    sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
      .key_length = kOtcryptoRsa3072PublicKeyBytes,
      .key = public_key_data,
  };
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize3072, modulus,
                                        kTestPublicExponent, &public_key));

  otcrypto_const_byte_buf_t msg_buf = {.data = msg, .len = msg_len};
  otcrypto_const_byte_buf_t label_buf = {.data = label, .len = label_len};
  otcrypto_word32_buf_t ciphertext_buf = {
      .data = ciphertext,
      .len = kRsa3072NumWords,
  };
  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_encrypt(&public_key, kTestHashMode, msg_buf, label_buf,
                           ciphertext_buf));
  profile_end_and_print(t_start, "RSA-3072 encryption");

  return OK_STATUS();
}

/**
 * Helper function to run the RSA-3072 decryption routine.
 *
 * Packages input into cryptolib-style structs and calls `otcrypto_rsa_encrypt`
 * using the constant test private key.
 *
 * The caller must allocate enough space at `msg` for the maximum message
 * length, `kMaxPlaintextBytes`. The actual message length is returned in
 * `msg_len`.
 *
 * @param label Label for OAEP padding.
 * @param label_len Label length in bytes.
 * @param ciphertext Ciphertext to decrypt (3072 bits).
 * @param[out] msg Decrypted message.
 * @param[out] msg_len Message length in bytes.
 * @return OK or error.
 */
static status_t run_rsa_3072_decrypt(const uint8_t *label, size_t label_len,
                                     const uint32_t *ciphertext, uint8_t *msg,
                                     size_t *msg_len) {
  // Create two shares for the private exponent (second share is all-zero).
  otcrypto_const_word32_buf_t d_share0 = {
      .data = kTestPrivateExponent,
      .len = ARRAYSIZE(kTestPrivateExponent),
  };
  uint32_t share1[ARRAYSIZE(kTestPrivateExponent)] = {0};
  otcrypto_const_word32_buf_t d_share1 = {
      .data = share1,
      .len = ARRAYSIZE(share1),
  };

  // Construct the private key.
  otcrypto_key_config_t private_key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
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
  otcrypto_const_word32_buf_t modulus = {
      .data = kTestModulus,
      .len = ARRAYSIZE(kTestModulus),
  };
  TRY(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize3072, modulus,
                                              kTestPublicExponent, d_share0,
                                              d_share1, &private_key));

  otcrypto_byte_buf_t plaintext_buf = {.data = msg, .len = kMaxPlaintextBytes};
  otcrypto_const_byte_buf_t label_buf = {.data = label, .len = label_len};
  otcrypto_const_word32_buf_t ciphertext_buf = {
      .data = ciphertext,
      .len = kRsa3072NumWords,
  };
  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_decrypt(&private_key, kTestHashMode, ciphertext_buf,
                           label_buf, plaintext_buf, msg_len));
  profile_end_and_print(t_start, "RSA-3072 decryption");

  return OK_STATUS();
}

status_t oaep_decrypt_valid_test(void) {
  // Decrypt the valid ciphertext.
  uint8_t actual_msg[kMaxPlaintextBytes];
  size_t actual_msg_len;
  TRY(run_rsa_3072_decrypt(kTestLabel, kTestLabelLen, kValidCiphertext,
                           actual_msg, &actual_msg_len));

  // Compare to the expected plaintext.
  TRY_CHECK(actual_msg_len == kTestMessageLen);
  TRY_CHECK_ARRAYS_EQ(actual_msg, kTestMessage, actual_msg_len);
  return OK_STATUS();
}

status_t oaep_encrypt_decrypt_test(void) {
  // Encrypt the message. Because OAEP is not deterministic, we cannot compare
  // to an exact expected value, but we can check that it successfully
  // decrypts.
  uint32_t ciphertext[kRsa3072NumWords];
  TRY(run_rsa_3072_encrypt(kTestMessage, kTestMessageLen, kTestLabel,
                           kTestLabelLen, ciphertext));

  // Decrypt the message.
  uint8_t actual_msg[kMaxPlaintextBytes];
  size_t actual_msg_len;
  TRY(run_rsa_3072_decrypt(kTestLabel, kTestLabelLen, ciphertext, actual_msg,
                           &actual_msg_len));

  // Compare to the original message.
  TRY_CHECK(actual_msg_len == kTestMessageLen);
  TRY_CHECK_ARRAYS_EQ(actual_msg, kTestMessage, actual_msg_len);
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t test_result = OK_STATUS();
  CHECK_STATUS_OK(entropy_complex_init());
  EXECUTE_TEST(test_result, oaep_decrypt_valid_test);
  EXECUTE_TEST(test_result, oaep_encrypt_decrypt_test);
  return status_ok(test_result);
}
