// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/rsa.h"

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
  kCryptotestRsaShake128 = 6,
  kCryptotestRsaShake256 = 7,
};

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
    case kCryptotestRsaShake128:
      hash_mode = kOtcryptoHashXofModeShake128;
      hash_digest_words = 128 / 32;
      break;
    case kCryptotestRsaShake256:
      hash_mode = kOtcryptoHashXofModeShake256;
      hash_digest_words = 256 / 32;
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
  uint32_t sig_buf[rsa_num_words];
  memset(sig_buf, 0, sizeof(sig_buf));
  memcpy(sig_buf, uj_input.sig, uj_input.sig_len);

  otcrypto_const_word32_buf_t sig = {
      .data = sig_buf,
      .len = rsa_num_words,
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
    case kOtcryptoHashXofModeShake128:
      TRY(otcrypto_shake128(msg_buf, &msg_digest));
      break;
    case kOtcryptoHashXofModeShake256:
      TRY(otcrypto_shake256(msg_buf, &msg_digest));
      break;
    default:
      LOG_ERROR("Unsupported RSA hash mode: %d", uj_input.hashing);
      return INVALID_ARGUMENT();
  }

  hardened_bool_t verification_result;
  TRY(otcrypto_rsa_verify(&public_key, msg_digest, padding_mode, sig,
                          &verification_result));

  // Return verification result back to host.
  cryptotest_rsa_verify_resp_t uj_output;

  uj_output.result = true;
  if (verification_result != kHardenedBoolTrue) {
    uj_output.result = false;
  }

  RESP_OK(ujson_serialize_cryptotest_rsa_verify_resp_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_rsa(ujson_t *uj) {
  rsa_subcommand_t cmd;
  TRY(ujson_deserialize_rsa_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kRsaSubcommandRsaVerify:
      return handle_rsa_verify(uj);
      break;
    default:
      LOG_ERROR("Unrecognized RSA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
