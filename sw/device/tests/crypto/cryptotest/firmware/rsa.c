// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/rsa.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/crypto/include/sha3.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/rsa_commands.h"

enum {
  /**
   * Supported public exponent.
   */
  kCryptotestRsaSupportedE = 65537,
  /**
   * RSA padding modes.
   */
  kCryptotestRsaPaddingPkcs = 0,
  kCryptotestRsaPaddingPss = 1,
  kCryptotestRsaPaddingOaep = 2,
  /**
   * Number of words for different RSA modes.
   */
  kCryptotestRsa2048NumWords =
      kOtcryptoRsa2048PublicKeyBytes / sizeof(uint32_t),
  kCryptotestRsa3072NumWords =
      kOtcryptoRsa3072PublicKeyBytes / sizeof(uint32_t),
  kCryptotestRsa4096NumWords =
      kOtcryptoRsa4096PublicKeyBytes / sizeof(uint32_t),
  /**
   * Different hashing modes.
   */
  kCryptotestRsaSha256 = 0,
  kCryptotestRsaSha384 = 1,
  kCryptotestRsaSha512 = 2,
  kCryptotestRsaSha3_256 = 3,
  kCryptotestRsaSha3_384 = 4,
  kCryptotestRsaSha3_512 = 5,
};

// Use a constant Boolean mask to share the RSA private exponent.
static const uint32_t key_mask[kCryptotestRsa4096NumWords] = {
    0x49117c55, 0x5da90893, 0x7f7605cf, 0x2b8ce457, 0x83ba97e0, 0x8cdf64a7,
    0x095fe63f, 0xd5aeb2e7, 0xfa3cabf5, 0xda2c6831, 0x18e92bc7, 0xe080f607,
    0x7e408d8f, 0xf095c121, 0xd2fe1075, 0x640dff1e, 0x7668f40a, 0x8a3a5b26,
    0xbbe4f4a5, 0x0135c08b, 0x9ff44d24, 0x799337e7, 0x9b6c4ce2, 0x9ef4edbc,
    0xfc687575, 0x72a5760c, 0x2592e004, 0x4cb859bc, 0x56b01d66, 0x308c8fe2,
    0xaf732664, 0xa51c0ae4, 0x80ffabf9, 0xef7e5b7f, 0x25a3881b, 0xaa15776e,
    0x3d32daeb, 0x0943b0ca, 0x37930548, 0xde545f50, 0x8002d4c8, 0x386367d5,
    0x569c49a1, 0xce924104, 0x86b7cb14, 0x8e536f56, 0x357395c9, 0x5cee69e4,
    0x3c8402f5, 0xe2f591a2, 0x6ef6ce8c, 0xfe838ad6, 0xa49a06e1, 0x71a22040,
    0xe786bb12, 0x0f0c55a0, 0x225a950a, 0x07bea294, 0x7bab7dc3, 0x7fd18a41,
    0xb6fa362e, 0x3c330655, 0xf42818d6, 0xb0c83e5e, 0xe8481edf, 0x99e11696,
    0xeb3b519f, 0x749f1a0a, 0x6d7162d5, 0x26e7a305, 0xbecc9b33, 0x8d5f657f,
    0x00a403ee, 0xd9f22edf, 0x79719a78, 0xaef60ff3, 0x758c6bc7, 0x28e0fa7f,
    0x9159bd75, 0x90f08bbd, 0xc45630b9, 0x5a37bd38, 0x08aecf3b, 0x27028a44,
    0x0bb7585d, 0x22c6e52c, 0x27c89949, 0xfbb2f54d, 0x41dbbb3e, 0xe79d9d64,
    0xdfbcbdcc, 0xb3246072, 0xe95db29e, 0x0cfb72b9, 0x303f88b4, 0x836d9b61,
    0xbcdf64f5, 0xf0562416, 0xbb0ca3be, 0xfee47430, 0x4f2d94f8, 0x09669a14,
    0x439d35ec, 0xe8e40037, 0x9d44ad51, 0x2c848d6b, 0x3193294a, 0xe1e97c3d,
    0x7eb4adac, 0x82b0abac, 0xcb738ec9, 0x42cff388, 0x0b76d4b3, 0xa7072639,
    0x75b54d85, 0xcc6d84f4, 0xe547b299, 0xa0e7dd85, 0xe3cad5b6, 0x632fad4d,
    0xe6cae515, 0x063cb76b, 0xff9428aa, 0x5c69fc6a, 0xbb15f685, 0xeb951a27,
    0xcadc73ec, 0xd3770767};

status_t handle_rsa_encrypt(ujson_t *uj) {
  cryptotest_rsa_encrypt_t uj_input;
  TRY(ujson_deserialize_cryptotest_rsa_encrypt_t(uj, &uj_input));

  if (uj_input.padding != kCryptotestRsaPaddingOaep) {
    LOG_ERROR("Unsupported RSA padding: %d", uj_input.padding);
    return INVALID_ARGUMENT();
  }

  if (uj_input.e != kCryptotestRsaSupportedE) {
    LOG_ERROR("Unsupported RSA public exponent e: %d", uj_input.e);
    return INVALID_ARGUMENT();
  }

  size_t rsa_num_words;
  size_t public_key_bytes;
  otcrypto_rsa_size_t rsa_size;
  size_t n_bytes = uj_input.security_level / 8;
  switch (n_bytes) {
    case kOtcryptoRsa2048PublicKeyBytes:
      rsa_size = kOtcryptoRsaSize2048;
      rsa_num_words = kCryptotestRsa2048NumWords;
      public_key_bytes = kOtcryptoRsa2048PublicKeyBytes;
      break;
    case kOtcryptoRsa3072PublicKeyBytes:
      rsa_size = kOtcryptoRsaSize3072;
      rsa_num_words = kCryptotestRsa3072NumWords;
      public_key_bytes = kOtcryptoRsa3072PublicKeyBytes;
      break;
    case kOtcryptoRsa4096PublicKeyBytes:
      rsa_size = kOtcryptoRsaSize4096;
      rsa_num_words = kCryptotestRsa4096NumWords;
      public_key_bytes = kOtcryptoRsa4096PublicKeyBytes;
      break;
    default:
      LOG_ERROR("Unsupported RSA security_level: %d", uj_input.security_level);
      return INVALID_ARGUMENT();
  }

  otcrypto_hash_mode_t hash_mode;
  switch (uj_input.hashing) {
    case kCryptotestRsaSha256:
      hash_mode = kOtcryptoHashModeSha256;
      break;
    case kCryptotestRsaSha384:
      hash_mode = kOtcryptoHashModeSha384;
      break;
    case kCryptotestRsaSha512:
      hash_mode = kOtcryptoHashModeSha512;
      break;
    case kCryptotestRsaSha3_256:
      hash_mode = kOtcryptoHashModeSha3_256;
      break;
    case kCryptotestRsaSha3_384:
      hash_mode = kOtcryptoHashModeSha3_384;
      break;
    case kCryptotestRsaSha3_512:
      hash_mode = kOtcryptoHashModeSha3_512;
      break;
    default:
      LOG_ERROR("Unsupported RSA hash mode: %d", uj_input.hashing);
      return INVALID_ARGUMENT();
  }

  // Create the modulus N buffer.
  uint32_t n_buf[rsa_num_words];
  memset(n_buf, 0, sizeof(n_buf));
  memcpy(n_buf, uj_input.n, n_bytes);

  otcrypto_const_word32_buf_t modulus = {
      .data = n_buf,
      .len = rsa_num_words,
  };

  // Construct the public key.
  uint32_t public_key_data[ceil_div(public_key_bytes, sizeof(uint32_t))];

  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
      .key_length = public_key_bytes,
      .key = public_key_data,
  };

  TRY(otcrypto_rsa_public_key_construct(rsa_size, modulus, &public_key));

  // Create input message.
  uint8_t msg_buf[uj_input.plaintext_len];
  memset(msg_buf, 0, sizeof(msg_buf));
  memcpy(msg_buf, uj_input.plaintext, uj_input.plaintext_len);
  otcrypto_const_byte_buf_t input_message = {
      .len = uj_input.plaintext_len,
      .data = msg_buf,
  };

  // Create label.
  uint8_t label_buf[uj_input.label_len];
  memset(label_buf, 0, sizeof(label_buf));
  memcpy(label_buf, uj_input.label, uj_input.label_len);
  otcrypto_const_byte_buf_t label = {
      .data = label_buf,
      .len = uj_input.label_len,
  };

  // Output buffer.
  uint32_t ciphertext_buf[rsa_num_words];
  otcrypto_word32_buf_t ciphertext = {
      .data = ciphertext_buf,
      .len = rsa_num_words,
  };

  bool status_resp = true;
  otcrypto_status_t status = otcrypto_rsa_encrypt(
      &public_key, hash_mode, input_message, label, ciphertext);
  if (status.value != kOtcryptoStatusValueOk) {
    status_resp = false;
  }

  // Return ciphertext and the status back to host.
  cryptotest_rsa_encrypt_resp_t uj_output;
  memset(uj_output.ciphertext, 0, RSA_CMD_MAX_MESSAGE_BYTES);
  memcpy(uj_output.ciphertext, ciphertext_buf, n_bytes);
  uj_output.ciphertext_len = n_bytes;
  uj_output.result = status_resp;

  RESP_OK(ujson_serialize_cryptotest_rsa_encrypt_resp_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_rsa_decrypt(ujson_t *uj) {
  cryptotest_rsa_decrypt_t uj_input;
  TRY(ujson_deserialize_cryptotest_rsa_decrypt_t(uj, &uj_input));

  if (uj_input.padding != kCryptotestRsaPaddingOaep) {
    LOG_ERROR("Unsupported RSA padding: %d", uj_input.padding);
    return INVALID_ARGUMENT();
  }

  if (uj_input.e != kCryptotestRsaSupportedE) {
    LOG_ERROR("Unsupported RSA public exponent e: %d", uj_input.e);
    return INVALID_ARGUMENT();
  }

  size_t rsa_num_words;
  size_t private_key_bytes;
  size_t private_key_blob_bytes;
  otcrypto_rsa_size_t rsa_size;
  size_t n_bytes = uj_input.security_level / 8;
  switch (n_bytes) {
    case kOtcryptoRsa2048PublicKeyBytes:
      rsa_size = kOtcryptoRsaSize2048;
      rsa_num_words = kCryptotestRsa2048NumWords;
      private_key_bytes = kOtcryptoRsa2048PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa2048PrivateKeyblobBytes;
      break;
    case kOtcryptoRsa3072PublicKeyBytes:
      rsa_size = kOtcryptoRsaSize3072;
      rsa_num_words = kCryptotestRsa3072NumWords;
      private_key_bytes = kOtcryptoRsa3072PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa3072PrivateKeyblobBytes;
      break;
    case kOtcryptoRsa4096PublicKeyBytes:
      rsa_size = kOtcryptoRsaSize4096;
      rsa_num_words = kCryptotestRsa4096NumWords;
      private_key_bytes = kOtcryptoRsa4096PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa4096PrivateKeyblobBytes;
      break;
    default:
      LOG_ERROR("Unsupported RSA security_level: %d", uj_input.security_level);
      return INVALID_ARGUMENT();
  }

  otcrypto_hash_mode_t hash_mode;
  size_t hash_digest_bytes;
  switch (uj_input.hashing) {
    case kCryptotestRsaSha256:
      hash_mode = kOtcryptoHashModeSha256;
      hash_digest_bytes = 256 / 8;
      break;
    case kCryptotestRsaSha384:
      hash_mode = kOtcryptoHashModeSha384;
      hash_digest_bytes = 384 / 8;
      break;
    case kCryptotestRsaSha512:
      hash_mode = kOtcryptoHashModeSha512;
      hash_digest_bytes = 512 / 8;
      break;
    case kCryptotestRsaSha3_256:
      hash_mode = kOtcryptoHashModeSha3_256;
      hash_digest_bytes = 256 / 8;
      break;
    case kCryptotestRsaSha3_384:
      hash_mode = kOtcryptoHashModeSha3_384;
      hash_digest_bytes = 384 / 8;
      break;
    case kCryptotestRsaSha3_512:
      hash_mode = kOtcryptoHashModeSha3_512;
      hash_digest_bytes = 512 / 8;
      break;
    default:
      LOG_ERROR("Unsupported RSA hash mode: %d", uj_input.hashing);
      return INVALID_ARGUMENT();
  }

  // Create the modulus N buffer.
  uint32_t n_buf[rsa_num_words];
  memset(n_buf, 0, sizeof(n_buf));
  memcpy(n_buf, uj_input.n, n_bytes);

  otcrypto_const_word32_buf_t modulus = {
      .data = n_buf,
      .len = rsa_num_words,
  };

  // Create two shares for the private exponent (second share is all-zero).
  uint32_t d_buf[rsa_num_words];
  memset(d_buf, 0, sizeof(d_buf));
  memcpy(d_buf, uj_input.d, n_bytes);
  for (size_t i = 0; i < rsa_num_words; i++) {
    d_buf[i] ^= key_mask[i];
  }
  otcrypto_const_word32_buf_t d_share0 = {
      .data = d_buf,
      .len = rsa_num_words,
  };

  uint32_t share1[rsa_num_words];
  for (size_t i = 0; i < rsa_num_words; i++) {
    share1[i] = key_mask[i];
  }
  otcrypto_const_word32_buf_t d_share1 = {
      .data = share1,
      .len = rsa_num_words,
  };

  // Construct the private key.
  otcrypto_key_config_t private_key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
      .key_length = private_key_bytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  size_t keyblob_words = ceil_div(private_key_blob_bytes, sizeof(uint32_t));
  uint32_t keyblob[keyblob_words];
  otcrypto_blinded_key_t private_key = {
      .config = private_key_config,
      .keyblob = keyblob,
      .keyblob_length = private_key_blob_bytes,
  };

  TRY(otcrypto_rsa_private_key_from_exponents(rsa_size, modulus, d_share0,
                                              d_share1, &private_key));

  size_t ciphertext_num_words =
      ceil_div(uj_input.ciphertext_len, sizeof(uint32_t));
  uint32_t ciphertext_buf[ciphertext_num_words];
  memset(ciphertext_buf, 0, sizeof(ciphertext_buf));
  memcpy(ciphertext_buf, uj_input.ciphertext, uj_input.ciphertext_len);

  otcrypto_const_word32_buf_t ciphertext = {
      .len = ciphertext_num_words,
      .data = ciphertext_buf,
  };

  // Create label.
  uint8_t label_buf[uj_input.label_len];
  memset(label_buf, 0, sizeof(label_buf));
  memcpy(label_buf, uj_input.label, uj_input.label_len);
  otcrypto_const_byte_buf_t label = {
      .data = label_buf,
      .len = uj_input.label_len,
  };

  // Create output buffer for the plaintext.
  // Maximum plaintext length for OAEP (see IETF RFC 8017).
  size_t kMaxPlaintextBytes = n_bytes - 2 * hash_digest_bytes - 2;
  uint8_t plaintext_buf[kMaxPlaintextBytes];
  otcrypto_byte_buf_t plaintext = {
      .data = plaintext_buf,
      .len = kMaxPlaintextBytes,
  };

  size_t msg_len = 0;
  bool status_resp = true;
  otcrypto_status_t status = otcrypto_rsa_decrypt(
      &private_key, hash_mode, ciphertext, label, plaintext, &msg_len);
  if (status.value != kOtcryptoStatusValueOk) {
    status_resp = false;
  }

  // Return plaintext and the status back to host.
  cryptotest_rsa_decrypt_resp_t uj_output;
  memset(uj_output.plaintext, 0, RSA_CMD_MAX_MESSAGE_BYTES);
  memcpy(uj_output.plaintext, plaintext_buf, msg_len);
  uj_output.plaintext_len = msg_len;
  uj_output.result = status_resp;

  RESP_OK(ujson_serialize_cryptotest_rsa_decrypt_resp_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_rsa_verify(ujson_t *uj) {
  cryptotest_rsa_verify_t uj_input;
  TRY(ujson_deserialize_cryptotest_rsa_verify_t(uj, &uj_input));

  if (uj_input.e != kCryptotestRsaSupportedE) {
    LOG_ERROR("Unsupported RSA public exponent e: %d", uj_input.e);
    return INVALID_ARGUMENT();
  }

  size_t rsa_num_words;
  size_t n_bytes = uj_input.security_level / 8;
  otcrypto_rsa_size_t rsa_size;
  switch (n_bytes) {
    case kOtcryptoRsa2048PublicKeyBytes:
      rsa_size = kOtcryptoRsaSize2048;
      rsa_num_words = kCryptotestRsa2048NumWords;
      break;
    case kOtcryptoRsa3072PublicKeyBytes:
      rsa_size = kOtcryptoRsaSize3072;
      rsa_num_words = kCryptotestRsa3072NumWords;
      break;
    case kOtcryptoRsa4096PublicKeyBytes:
      rsa_size = kOtcryptoRsaSize4096;
      rsa_num_words = kCryptotestRsa4096NumWords;
      break;
    default:
      LOG_ERROR("Unsupported RSA security_level: %d", uj_input.security_level);
      return INVALID_ARGUMENT();
  }

  otcrypto_hash_mode_t hash_mode;
  size_t hash_digest_words;
  switch (uj_input.hashing) {
    case kCryptotestRsaSha256:
      hash_mode = kOtcryptoHashModeSha256;
      hash_digest_words = 256 / 32;
      break;
    case kCryptotestRsaSha384:
      hash_mode = kOtcryptoHashModeSha384;
      hash_digest_words = 384 / 32;
      break;
    case kCryptotestRsaSha512:
      hash_mode = kOtcryptoHashModeSha512;
      hash_digest_words = 512 / 32;
      break;
    case kCryptotestRsaSha3_256:
      hash_mode = kOtcryptoHashModeSha3_256;
      hash_digest_words = 256 / 32;
      break;
    case kCryptotestRsaSha3_384:
      hash_mode = kOtcryptoHashModeSha3_384;
      hash_digest_words = 384 / 32;
      break;
    case kCryptotestRsaSha3_512:
      hash_mode = kOtcryptoHashModeSha3_512;
      hash_digest_words = 512 / 32;
      break;
    default:
      LOG_ERROR("Unsupported RSA hash mode: %d", uj_input.hashing);
      return INVALID_ARGUMENT();
  }

  otcrypto_key_mode_t key_mode;
  otcrypto_rsa_padding_t padding_mode;
  switch (uj_input.padding) {
    case kCryptotestRsaPaddingPkcs:
      padding_mode = kOtcryptoRsaPaddingPkcs;
      key_mode = kOtcryptoKeyModeRsaSignPkcs;
      break;
    case kCryptotestRsaPaddingPss:
      padding_mode = kOtcryptoRsaPaddingPss;
      key_mode = kOtcryptoKeyModeRsaSignPss;
      break;
    default:
      LOG_ERROR("Unsupported RSA padding mode: %d", uj_input.padding);
      return INVALID_ARGUMENT();
  };

  // Create the modulus N buffer.
  uint32_t n_buf[rsa_num_words];
  memset(n_buf, 0, sizeof(n_buf));
  memcpy(n_buf, uj_input.n, n_bytes);

  otcrypto_const_word32_buf_t modulus = {
      .data = n_buf,
      .len = rsa_num_words,
  };

  // Create the public key.
  uint32_t public_key_data[rsa_num_words];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = key_mode,
      .key_length = n_bytes,
      .key = public_key_data,
  };
  TRY(otcrypto_rsa_public_key_construct(rsa_size, modulus, &public_key));

  // Create the signature buffer.
  size_t sig_num_words = ceil_div(uj_input.sig_len, sizeof(uint32_t));
  uint32_t sig_buf[sig_num_words];
  memset(sig_buf, 0, sizeof(sig_buf));
  memcpy(sig_buf, uj_input.sig, sizeof(sig_buf));

  otcrypto_const_word32_buf_t sig = {
      .data = sig_buf,
      .len = sig_num_words,
  };

  // Copy the message into the buffer.
  uint8_t msg[uj_input.msg_len];
  memcpy(msg, uj_input.msg, uj_input.msg_len);
  otcrypto_const_byte_buf_t msg_buf = {
      .len = uj_input.msg_len,
      .data = msg,
  };

  // Buffer to store the digest.
  uint32_t msg_digest_data[hash_digest_words];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
      .mode = hash_mode,
  };

  // Hash the message.
  switch (hash_mode) {
    case kOtcryptoHashModeSha256:
      TRY(otcrypto_sha2_256(msg_buf, &msg_digest));
      break;
    case kOtcryptoHashModeSha384:
      TRY(otcrypto_sha2_384(msg_buf, &msg_digest));
      break;
    case kOtcryptoHashModeSha512:
      TRY(otcrypto_sha2_512(msg_buf, &msg_digest));
      break;
    case kOtcryptoHashModeSha3_256:
      TRY(otcrypto_sha3_256(msg_buf, &msg_digest));
      break;
    case kOtcryptoHashModeSha3_384:
      TRY(otcrypto_sha3_384(msg_buf, &msg_digest));
      break;
    case kOtcryptoHashModeSha3_512:
      TRY(otcrypto_sha3_512(msg_buf, &msg_digest));
      break;
    default:
      LOG_ERROR("Unsupported RSA hash mode: %d", uj_input.hashing);
      return INVALID_ARGUMENT();
  }

  hardened_bool_t verification_result;
  otcrypto_status_t status = otcrypto_rsa_verify(
      &public_key, msg_digest, padding_mode, sig, &verification_result);

  // Return verification result back to host.
  cryptotest_rsa_verify_resp_t uj_output;
  uj_output.result = true;

  if ((status.value != kOtcryptoStatusValueOk) ||
      (verification_result != kHardenedBoolTrue)) {
    uj_output.result = false;
  }

  RESP_OK(ujson_serialize_cryptotest_rsa_verify_resp_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_rsa(ujson_t *uj) {
  rsa_subcommand_t cmd;
  TRY(ujson_deserialize_rsa_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kRsaSubcommandRsaEncrypt:
      return handle_rsa_encrypt(uj);
    case kRsaSubcommandRsaDecrypt:
      return handle_rsa_decrypt(uj);
    case kRsaSubcommandRsaVerify:
      return handle_rsa_verify(uj);
    default:
      LOG_ERROR("Unrecognized RSA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
