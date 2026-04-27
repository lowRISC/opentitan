// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
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

// OAEP label for testing.
static const unsigned char kTestLabel[] = "Test label.";
static const size_t kTestLabelLen = sizeof(kTestLabel) - 1;

// Hash mode for testing (and digest length in bytes).
static const otcrypto_hash_mode_t kTestHashMode = kOtcryptoHashModeSha256;
static const size_t kTestHashModeDigestBytes = 256 / 8;

// Maximum plaintext length for OAEP (see IETF RFC 8017).
static const size_t kMaxPlaintextBytes =
    kRsa2048NumBytes - 2 * kTestHashModeDigestBytes - 2;

// Valid ciphertext for `kTestMessage` with the test private key, using OAEP
// encoding with `kTestLabel` and `kTestHashMode`.
static const uint32_t kValidCiphertext[kRsa2048NumWords] = {
    0xfd4efa2a, 0x98502230, 0x8f40a23d, 0xf1bc68ec, 0x32c09a86, 0x31a34a7f,
    0x4cc36d4d, 0xebde83bb, 0xd8641f7e, 0xedc26ed4, 0x8cd83ce6, 0xca3e0696,
    0x5a425138, 0xd5d55a43, 0x4666b6eb, 0x7d031dee, 0xbc92a18d, 0xce7f14be,
    0x768d170,  0xa3b26259, 0x668cf732, 0x72b44d0e, 0xd9f35df1, 0x67e194af,
    0xf4a47c8a, 0x8c0be5ee, 0x3b132be9, 0x797cdeb,  0x5ac41ab2, 0x960bd1bb,
    0x4d5f9c16, 0x1b40df52, 0x1cc85cae, 0x897f104f, 0xa6d56f86, 0x13d59592,
    0x741b5a79, 0x15732dbb, 0xa792b600, 0x8a1a6ad8, 0x6192b34b, 0xd5516b1a,
    0xab6c8133, 0x4b820cb3, 0xdec5f9b5, 0x9d479d3a, 0xd8e8109c, 0xe9e79346,
    0x91e4c925, 0x730c258,  0x3ae71747, 0x50ab1e5e, 0x931bd40a, 0x351d2440,
    0xb5e9273d, 0xd07a5e7b, 0x84487ef2, 0xfa2c3eae, 0x60a289db, 0x533d9a42,
    0x3473ae8,  0x6b43b4a4, 0x4944f45f, 0x9588b044,
};

/**
 * Helper function to run the RSA-2048 encryption routine.
 *
 * Packages input into cryptolib-style structs and calls `otcrypto_rsa_encrypt`
 * using the constant test private key.
 *
 * @param msg Message to encrypt.
 * @param msg_len Message length in bytes.
 * @param label Label for OAEP padding.
 * @param label_len Label length in bytes.
 * @param[out] ciphertext Buffer for the generated ciphertext (2048 bits).
 * @return OK or error.
 */
static status_t run_rsa_2048_encrypt(const uint8_t *msg, size_t msg_len,
                                     const uint8_t *label, size_t label_len,
                                     uint32_t *ciphertext) {
  // Construct the public key.
  otcrypto_const_word32_buf_t modulus = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kTestModulus, ARRAYSIZE(kTestModulus));
  uint32_t public_key_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes,
                                    sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = public_key_data,
  };
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &modulus,
                                        &public_key));

  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg, msg_len);
  otcrypto_const_byte_buf_t label_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, label, label_len);
  otcrypto_word32_buf_t ciphertext_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ciphertext, kRsa2048NumWords);
  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_encrypt(&public_key, kTestHashMode, &msg_buf, &label_buf,
                           &ciphertext_buf));
  profile_end_and_print(t_start, "RSA-2048 encryption");

  return OK_STATUS();
}

/**
 * Helper function to run the RSA-2048 decryption routine.
 *
 * Packages input into cryptolib-style structs and calls `otcrypto_rsa_decrypt`
 * using the constant test private key.
 *
 * The caller must allocate enough space at `msg` for the maximum message
 * length, `kMaxPlaintextBytes`. The actual message length is returned in
 * `msg_len`.
 *
 * @param label Label for OAEP padding.
 * @param label_len Label length in bytes.
 * @param ciphertext Ciphertext to decrypt (2048 bits).
 * @param[out] msg Decrypted message.
 * @param[out] msg_len Message length in bytes.
 * @return OK or error.
 */
static status_t run_rsa_2048_decrypt(const uint8_t *label, size_t label_len,
                                     const uint32_t *ciphertext, uint8_t *msg,
                                     size_t *msg_len) {
  // Create two shares for the private exponent (second share is all-zero).
  otcrypto_const_word32_buf_t d_share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kTestPrivateExponent,
                        ARRAYSIZE(kTestPrivateExponent));
  uint32_t share1[ARRAYSIZE(kTestPrivateExponent)] = {0};
  otcrypto_const_word32_buf_t d_share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share1, ARRAYSIZE(share1));

  // Construct the private key.
  otcrypto_key_config_t private_key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
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

  otcrypto_byte_buf_t plaintext_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, msg, kMaxPlaintextBytes);
  otcrypto_const_byte_buf_t label_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, label, label_len);
  otcrypto_const_word32_buf_t ciphertext_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, ciphertext, kRsa2048NumWords);
  uint64_t t_start = profile_start();
  TRY(otcrypto_rsa_decrypt(&private_key, kTestHashMode, &ciphertext_buf,
                           &label_buf, &plaintext_buf, msg_len));
  profile_end_and_print(t_start, "RSA-2048 decryption");

  return OK_STATUS();
}

status_t oaep_decrypt_valid_test(void) {
  // Decrypt the valid ciphertext.
  uint8_t actual_msg[kMaxPlaintextBytes];
  size_t actual_msg_len;
  TRY(run_rsa_2048_decrypt(kTestLabel, kTestLabelLen, kValidCiphertext,
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
  uint32_t ciphertext[kRsa2048NumWords];
  TRY(run_rsa_2048_encrypt(kTestMessage, kTestMessageLen, kTestLabel,
                           kTestLabelLen, ciphertext));

  // Decrypt the message.
  uint8_t actual_msg[kMaxPlaintextBytes];
  size_t actual_msg_len;
  TRY(run_rsa_2048_decrypt(kTestLabel, kTestLabelLen, ciphertext, actual_msg,
                           &actual_msg_len));

  // Compare to the original message.
  TRY_CHECK(actual_msg_len == kTestMessageLen);
  TRY_CHECK_ARRAYS_EQ(actual_msg, kTestMessage, actual_msg_len);
  return OK_STATUS();
}

/**
 * Negative tests
 */
static status_t run_encrypt_negative_tests(void) {
  LOG_INFO("Running RSA encrypt/decrypt negative tests");

  // Base valid keys
  uint32_t pub_data[kOtcryptoRsa2048PublicKeyBytes / 4] = {0};
  otcrypto_unblinded_key_t valid_pub = {
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_data,
  };
  valid_pub.checksum = integrity_unblinded_checksum(&valid_pub);

  otcrypto_key_config_t priv_cfg = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
      .key_length = kOtcryptoRsa2048PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t priv_blob[kOtcryptoRsa2048PrivateKeyblobBytes / 4] = {0};
  otcrypto_blinded_key_t valid_priv = {
      .config = priv_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };
  valid_priv.checksum = integrity_blinded_checksum(&valid_priv);

  // Base valid/invalid buffers
  uint8_t msg_data[] = "test";
  otcrypto_const_byte_buf_t valid_msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg_data, 4);
  otcrypto_const_byte_buf_t bad_msg_null =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 4);

  uint32_t ct_data[kRsa2048NumWords] = {0};
  otcrypto_word32_buf_t valid_ct =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ct_data, kRsa2048NumWords);
  otcrypto_const_word32_buf_t valid_const_ct =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, ct_data, kRsa2048NumWords);
  otcrypto_word32_buf_t bad_ct_null =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, NULL, kRsa2048NumWords);

  uint8_t pt_data[256] = {0};
  otcrypto_byte_buf_t valid_pt =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, pt_data, sizeof(pt_data));
  size_t pt_len = 0;

  // Encrypt negative tests

  // Null pointers
  CHECK(otcrypto_rsa_encrypt(NULL, kTestHashMode, &valid_msg, &valid_msg,
                             &valid_ct)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_encrypt_async_start(NULL, kTestHashMode, &valid_msg,
                                         &valid_msg)
            .value != OTCRYPTO_OK.value);

  CHECK(otcrypto_rsa_encrypt(&valid_pub, kTestHashMode, &bad_msg_null,
                             &valid_msg, &valid_ct)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_encrypt_async_start(&valid_pub, kTestHashMode,
                                         &bad_msg_null, &valid_msg)
            .value != OTCRYPTO_OK.value);

  CHECK(otcrypto_rsa_encrypt(&valid_pub, kTestHashMode, &valid_msg,
                             &bad_msg_null, &valid_ct)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_encrypt_async_start(&valid_pub, kTestHashMode, &valid_msg,
                                         &bad_msg_null)
            .value != OTCRYPTO_OK.value);

  CHECK(otcrypto_rsa_encrypt(&valid_pub, kTestHashMode, &valid_msg, &valid_msg,
                             &bad_ct_null)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_encrypt_async_finalize(&bad_ct_null).value !=
        OTCRYPTO_OK.value);

  // Corrupt checksum
  otcrypto_unblinded_key_t bad_pub_chk = {
      .key_mode = valid_pub.key_mode,
      .key_length = valid_pub.key_length,
      .key = pub_data,
  };
  bad_pub_chk.checksum = valid_pub.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_rsa_encrypt(&bad_pub_chk, kTestHashMode, &valid_msg,
                             &valid_msg, &valid_ct)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_encrypt_async_start(&bad_pub_chk, kTestHashMode,
                                         &valid_msg, &valid_msg)
            .value != OTCRYPTO_OK.value);

  // Bad mode
  otcrypto_unblinded_key_t bad_pub_mode = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = valid_pub.key_length,
      .key = pub_data,
  };
  bad_pub_mode.checksum = integrity_unblinded_checksum(&bad_pub_mode);
  CHECK(otcrypto_rsa_encrypt(&bad_pub_mode, kTestHashMode, &valid_msg,
                             &valid_msg, &valid_ct)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_encrypt_async_start(&bad_pub_mode, kTestHashMode,
                                         &valid_msg, &valid_msg)
            .value != OTCRYPTO_OK.value);

  // Decrypt negative tests

  // Null pointers
  CHECK(otcrypto_rsa_decrypt(NULL, kTestHashMode, &valid_const_ct, &valid_msg,
                             &valid_pt, &pt_len)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_decrypt_async_start(NULL, &valid_const_ct).value !=
        OTCRYPTO_OK.value);

  otcrypto_const_word32_buf_t bad_const_ct_null =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, NULL, kRsa2048NumWords);
  CHECK(otcrypto_rsa_decrypt(&valid_priv, kTestHashMode, &bad_const_ct_null,
                             &valid_msg, &valid_pt, &pt_len)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(
      otcrypto_rsa_decrypt_async_start(&valid_priv, &bad_const_ct_null).value !=
      OTCRYPTO_OK.value);

  otcrypto_byte_buf_t bad_pt_null =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, NULL, 256);
  CHECK(otcrypto_rsa_decrypt(&valid_priv, kTestHashMode, &valid_const_ct,
                             &valid_msg, &bad_pt_null, &pt_len)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_decrypt_async_finalize(kTestHashMode, &valid_msg,
                                            &bad_pt_null, &pt_len)
            .value != OTCRYPTO_OK.value);

  CHECK(otcrypto_rsa_decrypt(&valid_priv, kTestHashMode, &valid_const_ct,
                             &valid_msg, &valid_pt, NULL)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_decrypt_async_finalize(kTestHashMode, &valid_msg,
                                            &valid_pt, NULL)
            .value != OTCRYPTO_OK.value);

  // Corrupt checksum
  otcrypto_blinded_key_t bad_priv_chk = {
      .config = priv_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };
  bad_priv_chk.checksum = valid_priv.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_rsa_decrypt(&bad_priv_chk, kTestHashMode, &valid_const_ct,
                             &valid_msg, &valid_pt, &pt_len)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(
      otcrypto_rsa_decrypt_async_start(&bad_priv_chk, &valid_const_ct).value !=
      OTCRYPTO_OK.value);

  // Bad mode
  otcrypto_key_config_t bad_priv_mode_cfg = priv_cfg;
  bad_priv_mode_cfg.key_mode = kOtcryptoKeyModeRsaSignPkcs;
  otcrypto_blinded_key_t bad_priv_mode = {
      .config = bad_priv_mode_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };
  bad_priv_mode.checksum = integrity_blinded_checksum(&bad_priv_mode);
  CHECK(otcrypto_rsa_decrypt(&bad_priv_mode, kTestHashMode, &valid_const_ct,
                             &valid_msg, &valid_pt, &pt_len)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(
      otcrypto_rsa_decrypt_async_start(&bad_priv_mode, &valid_const_ct).value !=
      OTCRYPTO_OK.value);

  // Bad ciphertext length in finalize
  otcrypto_word32_buf_t bad_ct_len =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ct_data, kRsa2048NumWords - 1);
  CHECK(otcrypto_rsa_encrypt_async_finalize(&bad_ct_len).value !=
        OTCRYPTO_OK.value);

  // Ciphertext larger than modulus (n) in decrypt_start
  // We fill a buffer with 0xFF to guarantee it is larger than the test modulus
  uint32_t large_ct_data[kRsa2048NumWords];
  memset(large_ct_data, 0xFF, sizeof(large_ct_data));
  otcrypto_const_word32_buf_t large_ct = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, large_ct_data, kRsa2048NumWords);
  CHECK(otcrypto_rsa_decrypt(&valid_priv, kTestHashMode, &large_ct, &valid_msg,
                             &valid_pt, &pt_len)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_decrypt_async_start(&valid_priv, &large_ct).value !=
        OTCRYPTO_OK.value);

  // Plaintext buffer too small for OAEP max message length in decrypt_finalize
  // kMaxPlaintextBytes for 2048 with SHA256 is ~190 bytes. 10 is definitely too
  // small.
  otcrypto_byte_buf_t small_pt =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, pt_data, 10);
  CHECK(otcrypto_rsa_decrypt(&valid_priv, kTestHashMode, &valid_const_ct,
                             &valid_msg, &small_pt, &pt_len)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_decrypt_async_finalize(kTestHashMode, &valid_msg,
                                            &small_pt, &pt_len)
            .value != OTCRYPTO_OK.value);

  // Unrecognized key length in rsa_size_from_public_key (via encrypt)
  otcrypto_unblinded_key_t pub_bad_size = {
      .key_mode = valid_pub.key_mode,
      .key_length = 257,  // Unrecognized length
      .key = pub_data,
  };
  pub_bad_size.checksum = integrity_unblinded_checksum(&pub_bad_size);
  CHECK(otcrypto_rsa_encrypt(&pub_bad_size, kTestHashMode, &valid_msg,
                             &valid_msg, &valid_ct)
            .value == OTCRYPTO_BAD_ARGS.value);

  return OTCRYPTO_OK;
}

static status_t run_public_key_construct_negative_tests(void) {
  LOG_INFO("Running RSA public key construct negative tests");

  uint32_t mod_data[kRsa2048NumWords] = {0};
  otcrypto_const_word32_buf_t valid_mod = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, mod_data, kRsa2048NumWords);
  otcrypto_const_word32_buf_t bad_mod_null =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, NULL, kRsa2048NumWords);
  otcrypto_const_word32_buf_t bad_mod_len = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, mod_data, kRsa2048NumWords - 1);

  uint32_t pub_data[kOtcryptoRsa2048PublicKeyBytes / 4] = {0};
  otcrypto_unblinded_key_t valid_pub = {
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_data,
  };

  otcrypto_unblinded_key_t bad_pub_null_key = {
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = NULL,
  };

  otcrypto_unblinded_key_t bad_pub_mode = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_data,
  };

  otcrypto_unblinded_key_t bad_pub_len = {
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
      .key_length = kOtcryptoRsa2048PublicKeyBytes - 1,
      .key = pub_data,
  };

  // Null pointers
  CHECK(
      otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, NULL, &valid_pub)
          .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &bad_mod_null,
                                          &valid_pub)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(
      otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &valid_mod, NULL)
          .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &valid_mod,
                                          &bad_pub_null_key)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Bad mode
  CHECK(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &valid_mod,
                                          &bad_pub_mode)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Mismatched lengths for 2048
  CHECK(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &bad_mod_len,
                                          &valid_pub)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &valid_mod,
                                          &bad_pub_len)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Mismatched size enum
  CHECK(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize3072, &valid_mod,
                                          &valid_pub)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize4096, &valid_mod,
                                          &valid_pub)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Invalid size enum
  CHECK(otcrypto_rsa_public_key_construct((otcrypto_rsa_size_t)999, &valid_mod,
                                          &valid_pub)
            .value == OTCRYPTO_BAD_ARGS.value);

  return OTCRYPTO_OK;
}

static status_t run_private_key_from_exponents_negative_tests(void) {
  LOG_INFO("Running RSA private key from exponents negative tests");

  // Allocate valid base buffers
  uint32_t mod_data[kRsa2048NumWords] = {0};
  uint32_t d0_data[kRsa2048NumWords] = {0};
  uint32_t d1_data[kRsa2048NumWords] = {0};

  otcrypto_const_word32_buf_t valid_mod = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, mod_data, kRsa2048NumWords);
  otcrypto_const_word32_buf_t valid_d0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, d0_data, kRsa2048NumWords);
  otcrypto_const_word32_buf_t valid_d1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, d1_data, kRsa2048NumWords);

  // Allocate invalid base buffers
  otcrypto_const_word32_buf_t bad_buf_null =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, NULL, kRsa2048NumWords);
  otcrypto_const_word32_buf_t bad_buf_len = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, d0_data, kRsa2048NumWords - 1);

  // Setup valid private key config
  uint32_t priv_blob[kOtcryptoRsa2048PrivateKeyblobBytes / 4] = {0};
  otcrypto_key_config_t valid_priv_cfg = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,  // valid RSA mode
      .key_length = kOtcryptoRsa2048PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  otcrypto_blinded_key_t valid_priv = {
      .config = valid_priv_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };

  // Setup invalid private key configs using initializer lists
  otcrypto_blinded_key_t bad_priv_null_blob = {
      .config = valid_priv_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = NULL,
  };

  otcrypto_key_config_t bad_mode_cfg = valid_priv_cfg;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeEcdsaP256;
  otcrypto_blinded_key_t bad_priv_mode = {
      .config = bad_mode_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };

  otcrypto_key_config_t bad_hw_cfg = valid_priv_cfg;
  bad_hw_cfg.hw_backed = kHardenedBoolTrue;
  otcrypto_blinded_key_t bad_priv_hw = {
      .config = bad_hw_cfg,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
      .keyblob = priv_blob,
  };

  otcrypto_blinded_key_t bad_priv_blob_len = {
      .config = valid_priv_cfg,
      .keyblob_length = 99,
      .keyblob = priv_blob,
  };

  // Null pointers
  CHECK(otcrypto_rsa_private_key_from_exponents(
            kOtcryptoRsaSize2048, NULL, &valid_d0, &valid_d1, &valid_priv)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048,
                                                &bad_buf_null, &valid_d0,
                                                &valid_d1, &valid_priv)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048,
                                                &valid_mod, &bad_buf_null,
                                                &valid_d1, &valid_priv)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048,
                                                &valid_mod, &valid_d0,
                                                &bad_buf_null, &valid_priv)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_private_key_from_exponents(
            kOtcryptoRsaSize2048, &valid_mod, &valid_d0, &valid_d1, NULL)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048,
                                                &valid_mod, &valid_d0,
                                                &valid_d1, &bad_priv_null_blob)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Mismatched share lengths vs modulus length
  CHECK(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048,
                                                &valid_mod, &bad_buf_len,
                                                &valid_d1, &valid_priv)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048,
                                                &valid_mod, &valid_d0,
                                                &bad_buf_len, &valid_priv)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Bad Mode
  CHECK(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048,
                                                &valid_mod, &valid_d0,
                                                &valid_d1, &bad_priv_mode)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Bad HW backed config
  CHECK(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048,
                                                &valid_mod, &valid_d0,
                                                &valid_d1, &bad_priv_hw)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Bad Blob length vs Config Length
  CHECK(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048,
                                                &valid_mod, &valid_d0,
                                                &valid_d1, &bad_priv_blob_len)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Mismatched size enum vs actual buffer sizes
  CHECK(otcrypto_rsa_private_key_from_exponents(
            kOtcryptoRsaSize3072, &valid_mod, &valid_d0, &valid_d1, &valid_priv)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Invalid size enum
  CHECK(otcrypto_rsa_private_key_from_exponents((otcrypto_rsa_size_t)999,
                                                &valid_mod, &valid_d0,
                                                &valid_d1, &valid_priv)
            .value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_const_word32_buf_t mod_bad_len = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, mod_data, kRsa2048NumWords - 1);
  CHECK(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048,
                                                &mod_bad_len, &valid_d0,
                                                &valid_d1, &valid_priv)
            .value == OTCRYPTO_BAD_ARGS.value);

  otcrypto_blinded_key_t priv_bad_blob_len = {
      .config = valid_priv_cfg,
      .keyblob_length = 999,  // Invalid length
      .keyblob = priv_blob,
  };
  CHECK(otcrypto_rsa_private_key_from_exponents(kOtcryptoRsaSize2048,
                                                &valid_mod, &valid_d0,
                                                &valid_d1, &priv_bad_blob_len)
            .value == OTCRYPTO_BAD_ARGS.value);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t test_result = OK_STATUS();
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));
  EXECUTE_TEST(test_result, oaep_decrypt_valid_test);
  EXECUTE_TEST(test_result, oaep_encrypt_decrypt_test);
  EXECUTE_TEST(test_result, run_encrypt_negative_tests);
  EXECUTE_TEST(test_result, run_public_key_construct_negative_tests);
  EXECUTE_TEST(test_result, run_private_key_from_exponents_negative_tests);
  return status_ok(test_result);
}
