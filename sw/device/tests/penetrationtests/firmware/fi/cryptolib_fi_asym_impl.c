// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/cryptolib_fi_asym_impl.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/tests/penetrationtests/firmware/lib/cryptolib_asym.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_fi_asym_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// OAEP label for testing.
static const unsigned char kTestLabel[] = "Test label.";
static const size_t kTestLabelLen = sizeof(kTestLabel) - 1;

status_t cryptolib_fi_rsa_enc_impl(cryptolib_fi_asym_rsa_enc_in_t uj_input,
                                   cryptolib_fi_asym_rsa_enc_out_t *uj_output) {
  size_t public_key_bytes;
  size_t private_key_bytes;
  size_t private_key_blob_bytes;
  size_t num_words;
  size_t num_bytes;
  otcrypto_rsa_size_t rsa_size;
  switch (uj_input.mode) {
    case kPentestRsa2048:
      public_key_bytes = kOtcryptoRsa2048PublicKeyBytes;
      private_key_bytes = kOtcryptoRsa2048PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa2048PrivateKeyblobBytes;
      num_words = kPentestRsa2048NumWords;
      num_bytes = kPentestRsa2048NumBytes;
      rsa_size = kOtcryptoRsaSize2048;
      break;
    case kPentestRsa3072:
      public_key_bytes = kOtcryptoRsa3072PublicKeyBytes;
      private_key_bytes = kOtcryptoRsa3072PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa3072PrivateKeyblobBytes;
      num_words = kPentestRsa3072NumWords;
      num_bytes = kPentestRsa3072NumBytes;
      rsa_size = kOtcryptoRsaSize3072;
      break;
    case kPentestRsa4096:
      public_key_bytes = kOtcryptoRsa4096PublicKeyBytes;
      private_key_bytes = kOtcryptoRsa4096PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa4096PrivateKeyblobBytes;
      num_words = kPentestRsa4096NumWords;
      num_bytes = kPentestRsa4096NumBytes;
      rsa_size = kOtcryptoRsaSize4096;
      break;
    default:
      LOG_ERROR("Unsupported RSA mode: %d", uj_input.mode);
      return INVALID_ARGUMENT();
  }

  // Sanity check inputs.
  TRY_CHECK(num_bytes == uj_input.n_len);

  otcrypto_hash_mode_t hash_mode;
  size_t hash_digest_bytes;
  switch (uj_input.hashing) {
    case kPentestRsaHashmodeSha256:
      hash_mode = kOtcryptoHashModeSha256;
      hash_digest_bytes = kPentestSha256DigestBytes;
      break;
    case kPentestRsaHashmodeSha384:
      hash_mode = kOtcryptoHashModeSha384;
      hash_digest_bytes = kPentestSha384DigestBytes;
      break;
    case kPentestRsaHashmodeSha512:
      hash_mode = kOtcryptoHashModeSha512;
      hash_digest_bytes = kPentestSha512DigestBytes;
      break;
    default:
      LOG_ERROR("Unsupported RSA hash mode: %d", uj_input.hashing);
      return INVALID_ARGUMENT();
  }

  if (uj_input.padding != 0) {
    LOG_ERROR("Only padding = 0 (OAEP) is supported.");
    return INVALID_ARGUMENT();
  }

  // Create the modulus N buffer.
  uint32_t n_buf[kPentestRsaMaxNWords];
  memset(n_buf, 0, sizeof(n_buf));
  memcpy(n_buf, uj_input.n, num_bytes);

  otcrypto_const_word32_buf_t modulus =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, n_buf, num_words);

  // Create label.
  otcrypto_const_byte_buf_t label_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kTestLabel, kTestLabelLen);

  if (uj_input.op_enc) {
    // Encryption.
    uint32_t public_key_data[ceil_div(public_key_bytes, sizeof(uint32_t))];

    // Construct the public key.
    otcrypto_unblinded_key_t public_key = {
        .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
        .key_length = public_key_bytes,
        .key = public_key_data,
    };
    TRY(otcrypto_rsa_public_key_construct(rsa_size, &modulus, &public_key));

    // Create input message.
    uint8_t msg_buf[num_words];
    memcpy(msg_buf, uj_input.data, uj_input.data_len);
    otcrypto_const_byte_buf_t input_message = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, msg_buf, uj_input.data_len);

    // Output buffer.
    uint32_t ciphertext_buf[kPentestRsaMaxMsgWords];
    otcrypto_word32_buf_t ciphertext =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ciphertext_buf, num_words);

    // Trigger window.
    if (uj_input.trigger & kPentestTrigger1) {
      pentest_set_trigger_high();
    }
    otcrypto_status_t status_out = otcrypto_rsa_encrypt(
        &public_key, hash_mode, &input_message, &label_buf, &ciphertext);
    if (uj_input.trigger & kPentestTrigger1) {
      pentest_set_trigger_low();
    }

    // Return data back to host.
    uj_output->data_len = num_bytes;
    uj_output->cfg = 0;
    uj_output->status = (size_t)status_out.value;
    memset(uj_output->data, 0, RSA_CMD_MAX_MESSAGE_BYTES);
    memcpy(uj_output->data, ciphertext_buf, uj_output->data_len);
    // Return received n and d back to host.
    uj_output->n_len = uj_input.n_len;
    memset(uj_output->n, 0, RSA_CMD_MAX_N_BYTES);
    memcpy(uj_output->n, uj_input.n, uj_input.n_len);
    memset(uj_output->d, 0, RSA_CMD_MAX_N_BYTES);
    memcpy(uj_output->d, uj_input.d, uj_input.n_len);
  } else {
    // Decryption.

    // Create two shares for the private exponent (second share is all-zero).
    uint32_t d_buf[kPentestRsaMaxDWords];
    memset(d_buf, 0, sizeof(d_buf));
    memcpy(d_buf, uj_input.d, num_bytes);

    otcrypto_const_word32_buf_t d_share0 =
        OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, d_buf, num_words);
    uint32_t share1[kPentestRsaMaxDWords] = {0};
    otcrypto_const_word32_buf_t d_share1 =
        OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share1, num_words);

    // Construct the private key.
    otcrypto_key_config_t private_key_config = {
        .version = kOtcryptoLibVersion1,
        .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
        .key_length = private_key_bytes,
        .hw_backed = kHardenedBoolFalse,
        .security_level = kOtcryptoKeySecurityLevelHigh,
    };
    size_t keyblob_words = ceil_div(private_key_blob_bytes, sizeof(uint32_t));
    uint32_t keyblob[keyblob_words];
    otcrypto_blinded_key_t private_key = {
        .config = private_key_config,
        .keyblob = keyblob,
        .keyblob_length = private_key_blob_bytes,
    };

    // Trigger window.
    if (uj_input.trigger & kPentestTrigger1) {
      pentest_set_trigger_high();
    }
    TRY(otcrypto_rsa_private_key_from_exponents(rsa_size, &modulus, &d_share0,
                                                &d_share1, &private_key));
    if (uj_input.trigger & kPentestTrigger1) {
      pentest_set_trigger_low();
    }

    uint32_t ciphertext_buf[num_words];
    memset(ciphertext_buf, 0, sizeof(ciphertext_buf));
    memcpy(ciphertext_buf, uj_input.data, uj_input.data_len);

    otcrypto_const_word32_buf_t ciphertext = OTCRYPTO_MAKE_BUF(
        otcrypto_const_word32_buf_t, ciphertext_buf, num_words);

    // Create output buffer for the plaintext.
    size_t kMaxPlaintextBytes = num_bytes - 2 * hash_digest_bytes - 2;
    uint8_t plaintext_buf[kMaxPlaintextBytes];
    otcrypto_byte_buf_t plaintext = OTCRYPTO_MAKE_BUF(
        otcrypto_byte_buf_t, plaintext_buf, kMaxPlaintextBytes);

    size_t msg_len;
    // Trigger window.
    if (uj_input.trigger & kPentestTrigger2) {
      pentest_set_trigger_high();
    }
    TRY(otcrypto_rsa_decrypt(&private_key, hash_mode, &ciphertext, &label_buf,
                             &plaintext, &msg_len));
    if (uj_input.trigger & kPentestTrigger2) {
      pentest_set_trigger_low();
    }

    // Return data back to host.
    uj_output->data_len = msg_len;
    uj_output->cfg = 0;
    memset(uj_output->data, 0, RSA_CMD_MAX_MESSAGE_BYTES);
    memcpy(uj_output->data, plaintext_buf, msg_len);
    // Return received n and d back to host.
    uj_output->n_len = uj_input.n_len;
    memset(uj_output->n, 0, RSA_CMD_MAX_N_BYTES);
    memcpy(uj_output->n, uj_input.n, uj_input.n_len);
    memset(uj_output->d, 0, RSA_CMD_MAX_N_BYTES);
    memcpy(uj_output->d, uj_input.d, uj_input.n_len);
  }

  return OK_STATUS();
}

status_t cryptolib_fi_rsa_sign_impl(
    cryptolib_fi_asym_rsa_sign_in_t uj_input,
    cryptolib_fi_asym_rsa_sign_out_t *uj_output) {
  size_t private_key_bytes;
  size_t private_key_blob_bytes;
  size_t num_words;
  otcrypto_rsa_size_t rsa_size;
  switch (uj_input.n_len) {
    case kPentestRsa2048NumBytes:
      private_key_bytes = kOtcryptoRsa2048PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa2048PrivateKeyblobBytes;
      num_words = kPentestRsa2048NumWords;
      rsa_size = kOtcryptoRsaSize2048;
      break;
    case kPentestRsa3072NumBytes:
      private_key_bytes = kOtcryptoRsa3072PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa3072PrivateKeyblobBytes;
      num_words = kPentestRsa3072NumWords;
      rsa_size = kOtcryptoRsaSize3072;
      break;
    case kPentestRsa4096NumBytes:
      private_key_bytes = kOtcryptoRsa4096PrivateKeyBytes;
      private_key_blob_bytes = kOtcryptoRsa4096PrivateKeyblobBytes;
      num_words = kPentestRsa4096NumWords;
      rsa_size = kOtcryptoRsaSize4096;
      break;
    default:
      LOG_ERROR("Unsupported RSA mode: %d", uj_input.n_len);
      return INVALID_ARGUMENT();
  }

  otcrypto_key_mode_t key_mode;
  otcrypto_rsa_padding_t padding_mode;
  switch (uj_input.padding) {
    case kPentestRsaPaddingPkcs:
      padding_mode = kOtcryptoRsaPaddingPkcs;
      key_mode = kOtcryptoKeyModeRsaSignPkcs;
      break;
    case kPentestRsaPaddingPss:
      padding_mode = kOtcryptoRsaPaddingPss;
      key_mode = kOtcryptoKeyModeRsaSignPss;
      break;
    default:
      LOG_ERROR("Unsupported RSA padding mode: %d", uj_input.padding);
      return INVALID_ARGUMENT();
  };

  otcrypto_hash_mode_t hash_mode;
  size_t hash_digest_words;
  switch (uj_input.hashing) {
    case kPentestRsaHashmodeSha256:
      hash_mode = kOtcryptoHashModeSha256;
      hash_digest_words = kPentestSha256DigestWords;
      break;
    case kPentestRsaHashmodeSha384:
      hash_mode = kOtcryptoHashModeSha384;
      hash_digest_words = kPentestSha384DigestWords;
      break;
    case kPentestRsaHashmodeSha512:
      hash_mode = kOtcryptoHashModeSha512;
      hash_digest_words = kPentestSha512DigestWords;
      break;
    default:
      LOG_ERROR("Unsupported RSA hash mode: %d", uj_input.hashing);
      return INVALID_ARGUMENT();
  }
  // Create two shares for the private exponent (second share is all-zero).
  uint32_t d_buf[kPentestRsaMaxDWords];
  memset(d_buf, 0, sizeof(d_buf));
  memcpy(d_buf, uj_input.d, uj_input.n_len);

  otcrypto_const_word32_buf_t d_share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, d_buf, num_words);
  uint32_t share1[kPentestRsaMaxDWords] = {0};
  otcrypto_const_word32_buf_t d_share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share1, num_words);

  // Construct the private key.
  otcrypto_key_config_t private_key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = private_key_bytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelHigh,
  };
  size_t keyblob_words = ceil_div(private_key_blob_bytes, sizeof(uint32_t));
  uint32_t keyblob[keyblob_words];
  otcrypto_blinded_key_t private_key = {
      .config = private_key_config,
      .keyblob = keyblob,
      .keyblob_length = private_key_blob_bytes,
  };

  // Create the modulus N buffer.
  uint32_t n_buf[kPentestRsaMaxNWords];
  memset(n_buf, 0, sizeof(n_buf));
  memcpy(n_buf, uj_input.n, uj_input.n_len);

  otcrypto_const_word32_buf_t modulus =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, n_buf, num_words);

  // Trigger window.
  if (uj_input.trigger & kPentestTrigger1) {
    pentest_set_trigger_high();
  }
  TRY(otcrypto_rsa_private_key_from_exponents(rsa_size, &modulus, &d_share0,
                                              &d_share1, &private_key));
  if (uj_input.trigger & kPentestTrigger1) {
    pentest_set_trigger_low();
  }

  // Copy the message into the buffer.
  uint8_t msg[uj_input.data_len];
  memcpy(msg, uj_input.data, uj_input.data_len);
  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg, uj_input.data_len);

  // Buffer to store the digest.
  uint32_t msg_digest_data[hash_digest_words];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
      .mode = hash_mode,
  };
  // Trigger window.
  if (uj_input.trigger & kPentestTrigger2) {
    pentest_set_trigger_high();
  }
  // Hash the message.
  if (hash_mode == kOtcryptoHashModeSha256) {
    TRY(otcrypto_sha2_256(&msg_buf, &msg_digest));
  } else if (hash_mode == kOtcryptoHashModeSha384) {
    TRY(otcrypto_sha2_384(&msg_buf, &msg_digest));
  } else {
    TRY(otcrypto_sha2_512(&msg_buf, &msg_digest));
  }
  if (uj_input.trigger & kPentestTrigger2) {
    pentest_set_trigger_low();
  }

  uint32_t sig[kPentestRsaMaxMsgWords];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, num_words);

  // Trigger window.
  if (uj_input.trigger & kPentestTrigger3) {
    pentest_set_trigger_high();
  }
  TRY(otcrypto_rsa_sign(&private_key, msg_digest, padding_mode, &sig_buf));
  // Trigger window.
  if (uj_input.trigger & kPentestTrigger3) {
    pentest_set_trigger_low();
  }

  // Return data back to host.
  uj_output->sig_len = uj_input.n_len;
  uj_output->cfg = 0;
  memset(uj_output->sig, 0, RSA_CMD_MAX_SIGNATURE_BYTES);
  memcpy(uj_output->sig, sig, uj_output->sig_len);
  // Return received n and d back to host.
  uj_output->n_len = uj_input.n_len;
  memset(uj_output->n, 0, RSA_CMD_MAX_N_BYTES);
  memcpy(uj_output->n, uj_input.n, uj_input.n_len);
  memset(uj_output->d, 0, RSA_CMD_MAX_N_BYTES);
  memcpy(uj_output->d, uj_input.d, uj_input.n_len);

  return OK_STATUS();
}

status_t cryptolib_fi_rsa_verify_impl(
    cryptolib_fi_asym_rsa_verify_in_t uj_input,
    cryptolib_fi_asym_rsa_verify_out_t *uj_output) {
  size_t public_key_bytes;
  size_t num_words;
  otcrypto_rsa_size_t rsa_size;
  switch (uj_input.n_len) {
    case kPentestRsa2048NumBytes:
      public_key_bytes = kOtcryptoRsa2048PublicKeyBytes;
      num_words = kPentestRsa2048NumWords;
      rsa_size = kOtcryptoRsaSize2048;
      break;
    case kPentestRsa3072NumBytes:
      public_key_bytes = kOtcryptoRsa3072PublicKeyBytes;
      num_words = kPentestRsa3072NumWords;
      rsa_size = kOtcryptoRsaSize3072;
      break;
    case kPentestRsa4096NumBytes:
      public_key_bytes = kOtcryptoRsa4096PublicKeyBytes;
      num_words = kPentestRsa4096NumWords;
      rsa_size = kOtcryptoRsaSize4096;
      break;
    default:
      LOG_ERROR("Unsupported RSA mode: %d", uj_input.n_len);
      return INVALID_ARGUMENT();
  }

  otcrypto_hash_mode_t hash_mode;
  size_t hash_digest_words;
  switch (uj_input.hashing) {
    case kPentestRsaHashmodeSha256:
      hash_mode = kOtcryptoHashModeSha256;
      hash_digest_words = kPentestSha256DigestWords;
      break;
    case kPentestRsaHashmodeSha384:
      hash_mode = kOtcryptoHashModeSha384;
      hash_digest_words = kPentestSha384DigestWords;
      break;
    case kPentestRsaHashmodeSha512:
      hash_mode = kOtcryptoHashModeSha512;
      hash_digest_words = kPentestSha512DigestWords;
      break;
    default:
      LOG_ERROR("Unsupported RSA hash mode: %d", uj_input.hashing);
      return INVALID_ARGUMENT();
  }

  otcrypto_key_mode_t key_mode;
  otcrypto_rsa_padding_t padding_mode;
  switch (uj_input.padding) {
    case kPentestRsaPaddingPkcs:
      padding_mode = kOtcryptoRsaPaddingPkcs;
      key_mode = kOtcryptoKeyModeRsaSignPkcs;
      break;
    case kPentestRsaPaddingPss:
      padding_mode = kOtcryptoRsaPaddingPss;
      key_mode = kOtcryptoKeyModeRsaSignPss;
      break;
    default:
      LOG_ERROR("Unsupported RSA padding mode: %d", uj_input.padding);
      return INVALID_ARGUMENT();
  };

  // Create the modulus N buffer.
  uint32_t n_buf[kPentestRsaMaxNWords];
  memset(n_buf, 0, sizeof(n_buf));
  memcpy(n_buf, uj_input.n, uj_input.n_len);

  otcrypto_const_word32_buf_t modulus =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, n_buf, num_words);

  // Create the public key.
  uint32_t public_key_data[ceil_div(public_key_bytes, sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = key_mode,
      .key_length = public_key_bytes,
      .key = public_key_data,
  };
  // Trigger window.
  if (uj_input.trigger & kPentestTrigger1) {
    pentest_set_trigger_high();
  }
  TRY(otcrypto_rsa_public_key_construct(rsa_size, &modulus, &public_key));
  // Trigger window.
  if (uj_input.trigger & kPentestTrigger1) {
    pentest_set_trigger_low();
  }

  // Create the signature buffer.
  uint32_t sig_buf[num_words];
  memset(sig_buf, 0, sizeof(sig_buf));
  memcpy(sig_buf, uj_input.sig, uj_input.sig_len);

  otcrypto_const_word32_buf_t sig =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig_buf, num_words);

  // Copy the message into the buffer.
  uint8_t msg[uj_input.data_len];
  memcpy(msg, uj_input.data, uj_input.data_len);
  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg, uj_input.data_len);

  // Buffer to store the digest.
  uint32_t msg_digest_data[hash_digest_words];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
      .mode = hash_mode,
  };

  // Trigger window.
  if (uj_input.trigger & kPentestTrigger2) {
    pentest_set_trigger_high();
  }
  // Hash the message.
  if (hash_mode == kOtcryptoHashModeSha256) {
    TRY(otcrypto_sha2_256(&msg_buf, &msg_digest));
  } else if (hash_mode == kOtcryptoHashModeSha384) {
    TRY(otcrypto_sha2_384(&msg_buf, &msg_digest));
  } else {
    TRY(otcrypto_sha2_512(&msg_buf, &msg_digest));
  }
  if (uj_input.trigger & kPentestTrigger2) {
    pentest_set_trigger_low();
  }

  hardened_bool_t verification_result;
  // Trigger window.
  if (uj_input.trigger & kPentestTrigger3) {
    pentest_set_trigger_high();
  }
  TRY(otcrypto_rsa_verify(&public_key, msg_digest, padding_mode, &sig,
                          &verification_result));
  if (uj_input.trigger & kPentestTrigger3) {
    pentest_set_trigger_low();
  }

  // Return data back to host.
  uj_output->result = true;
  if (verification_result != kHardenedBoolTrue) {
    uj_output->result = false;
  }
  uj_output->cfg = 0;

  return OK_STATUS();
}

status_t cryptolib_fi_p256_ecdh_impl(
    cryptolib_fi_asym_p256_ecdh_in_t uj_input,
    cryptolib_fi_asym_p256_ecdh_out_t *uj_output) {
  // Construct the private key object.
  uint32_t private_keyblob[kPentestP256MaskedPrivateKeyWords * 2];
  otcrypto_blinded_key_t private_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeEcdhP256,
              .key_length = kPentestP256Bytes,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelHigh,
          },
      .keyblob_length = sizeof(private_keyblob),
      .keyblob = private_keyblob,
  };

  uint32_t share0[kPentestP256MaskedPrivateKeyWords] = {0};
  uint32_t share1[kPentestP256MaskedPrivateKeyWords] = {0};
  memcpy(share0, uj_input.private_key, P256_CMD_BYTES);

  otcrypto_const_word32_buf_t share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share0, kPentestP256MaskedPrivateKeyWords);
  otcrypto_const_word32_buf_t share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1, kPentestP256MaskedPrivateKeyWords);

  TRY(otcrypto_ecc_p256_private_key_import(share0_buf, share1_buf,
                                           &private_key));

  // Construct the public key object.
  uint32_t public_key_buf[kPentestP256Words * 2];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP256,
      .key_length = sizeof(public_key_buf),
      .key = public_key_buf,
  };

  uint32_t pub_x[kPentestP256Words] = {0};
  uint32_t pub_y[kPentestP256Words] = {0};
  memcpy(pub_x, uj_input.public_x, P256_CMD_BYTES);
  memcpy(pub_y, uj_input.public_y, P256_CMD_BYTES);

  otcrypto_const_word32_buf_t x_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pub_x, kPentestP256Words);
  otcrypto_const_word32_buf_t y_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pub_y, kPentestP256Words);

  TRY(otcrypto_ecc_p256_public_key_import(x_buf, y_buf, &public_key));

  // Create a destination for the shared secret.
  uint32_t shared_secretblob[kPentestP256Words * 2];
  memset(shared_secretblob, 0, sizeof(shared_secretblob));
  otcrypto_blinded_key_t shared_secret = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = kPentestP256Bytes,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelHigh,
          },
      .keyblob_length = sizeof(shared_secretblob),
      .keyblob = shared_secretblob,
  };

  pentest_set_trigger_high();
  TRY(otcrypto_ecdh_p256(&private_key, &public_key, &shared_secret));
  pentest_set_trigger_low();

  uint32_t ss_share0[kPentestP256Words];
  uint32_t ss_share1[kPentestP256Words];
  otcrypto_word32_buf_t ss_share0_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ss_share0, ARRAYSIZE(ss_share0));
  otcrypto_word32_buf_t ss_share1_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ss_share1, ARRAYSIZE(ss_share1));
  uint32_t ss[kPentestP256Words];
  TRY(otcrypto_export_blinded_key(&shared_secret, &ss_share0_buf,
                                  &ss_share1_buf));
  for (size_t i = 0; i < kPentestP256Words; i++) {
    ss[i] = ss_share0[i] ^ ss_share1[i];
  }

  // Return data back to host.
  uj_output->cfg = 0;
  memset(uj_output->shared_key, 0, P256_CMD_BYTES);
  memcpy(uj_output->shared_key, ss, P256_CMD_BYTES);

  return OK_STATUS();
}

status_t cryptolib_fi_p256_sign_impl(
    cryptolib_fi_asym_p256_sign_in_t uj_input,
    cryptolib_fi_asym_p256_sign_out_t *uj_output) {
  static const otcrypto_key_config_t kP256PrivateKeyConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = kPentestP256Bytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelHigh,
  };

  // Create the private key.
  uint32_t private_keyblob[kPentestP256MaskedPrivateKeyWords * 2];
  otcrypto_blinded_key_t private_key = {
      .config = kP256PrivateKeyConfig,
      .keyblob_length = sizeof(private_keyblob),
      .keyblob = private_keyblob,
  };

  uint32_t share0[kPentestP256MaskedPrivateKeyWords] = {0};
  uint32_t share1[kPentestP256MaskedPrivateKeyWords] = {0};
  memcpy(share0, uj_input.scalar, P256_CMD_BYTES);

  otcrypto_const_word32_buf_t share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share0, kPentestP256MaskedPrivateKeyWords);
  otcrypto_const_word32_buf_t share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1, kPentestP256MaskedPrivateKeyWords);

  TRY(otcrypto_ecc_p256_private_key_import(share0_buf, share1_buf,
                                           &private_key));

  // Create the public key.
  uint32_t public_key_buf[kPentestP256Words * 2];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(public_key_buf),
      .key = public_key_buf,
  };

  uint32_t pub_x[kPentestP256Words] = {0};
  uint32_t pub_y[kPentestP256Words] = {0};
  memcpy(pub_x, uj_input.pubx, P256_CMD_BYTES);
  memcpy(pub_y, uj_input.puby, P256_CMD_BYTES);

  otcrypto_const_word32_buf_t x_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pub_x, kPentestP256Words);
  otcrypto_const_word32_buf_t y_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pub_y, kPentestP256Words);

  TRY(otcrypto_ecc_p256_public_key_import(x_buf, y_buf, &public_key));

  // Create a key pair if requested.
  // This will overwrite the private and public key above.
  if (uj_input.cfg == 1) {
    // Trigger window 0.
    if (uj_input.trigger == 0) {
      pentest_set_trigger_high();
    }
    TRY(otcrypto_ecdsa_p256_keygen(&private_key, &public_key));
    pentest_set_trigger_low();
    if (uj_input.trigger == 0) {
      pentest_set_trigger_low();
    }
  }

  // Set up the message buffer.
  uint32_t message_buf[kPentestP256Words];
  memset(message_buf, 0, sizeof(message_buf));
  memcpy(message_buf, uj_input.message, P256_CMD_BYTES);

  const otcrypto_hash_digest_t message_digest = {
      .mode = kOtcryptoHashModeSha256,
      .len = kPentestP256Words,
      .data = (uint32_t *)message_buf,
  };

  // Set up the signature buffer.
  uint32_t sig[kPentestP256Words * 2] = {0};
  otcrypto_word32_buf_t signature_mut =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));

  // Trigger window 1.
  if (uj_input.trigger == 1) {
    pentest_set_trigger_high();
  }
  // Sign the message.
  TRY(otcrypto_ecdsa_p256_sign_verify(&private_key, &public_key, message_digest,
                                      &signature_mut));
  if (uj_input.trigger == 1) {
    pentest_set_trigger_low();
  }

  // Return data back to host.
  uj_output->cfg = 0;
  memset(uj_output->r, 0, P256_CMD_BYTES);
  memset(uj_output->s, 0, P256_CMD_BYTES);

  uint8_t *sig_bytes = (uint8_t *)signature_mut.data;
  memcpy(uj_output->r, sig_bytes, P256_CMD_BYTES);
  memcpy(uj_output->s, sig_bytes + P256_CMD_BYTES, P256_CMD_BYTES);

  // Return the public key.
  uint32_t out_pub_x[kPentestP256Words];
  uint32_t out_pub_y[kPentestP256Words];
  otcrypto_word32_buf_t out_x_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, out_pub_x, kPentestP256Words);
  otcrypto_word32_buf_t out_y_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, out_pub_y, kPentestP256Words);

  TRY(otcrypto_ecc_p256_public_key_export(&public_key, &out_x_buf, &out_y_buf));

  memcpy(uj_output->pubx, out_pub_x, P256_CMD_BYTES);
  memcpy(uj_output->puby, out_pub_y, P256_CMD_BYTES);

  return OK_STATUS();
}

status_t cryptolib_fi_p256_verify_impl(
    cryptolib_fi_asym_p256_verify_in_t uj_input,
    cryptolib_fi_asym_p256_verify_out_t *uj_output) {
  // Set up the message buffer.
  uint32_t message_buf[kPentestP256Words];
  memset(message_buf, 0, sizeof(message_buf));
  memcpy(message_buf, uj_input.message, P256_CMD_BYTES);

  const otcrypto_hash_digest_t message_digest = {
      .mode = kOtcryptoHashModeSha256,
      .len = kPentestP256Words,
      .data = (uint32_t *)message_buf,
  };

  // Setup the public key buffer.
  uint32_t public_key_buf[kPentestP256Words * 2];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(public_key_buf),
      .key = public_key_buf,
  };

  uint32_t pub_x[kPentestP256Words] = {0};
  uint32_t pub_y[kPentestP256Words] = {0};
  memcpy(pub_x, uj_input.pubx, P256_CMD_BYTES);
  memcpy(pub_y, uj_input.puby, P256_CMD_BYTES);

  otcrypto_const_word32_buf_t x_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pub_x, kPentestP256Words);
  otcrypto_const_word32_buf_t y_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pub_y, kPentestP256Words);

  TRY(otcrypto_ecc_p256_public_key_import(x_buf, y_buf, &public_key));

  // Setup the signature buffer.
  uint32_t signature_data[kPentestP256Words * 2] = {0};
  memcpy((uint8_t *)signature_data, uj_input.r, P256_CMD_BYTES);
  memcpy((uint8_t *)signature_data + P256_CMD_BYTES, uj_input.s,
         P256_CMD_BYTES);

  otcrypto_const_word32_buf_t signature = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, signature_data, kPentestP256Words * 2);

  hardened_bool_t verification_result = kHardenedBoolFalse;

  pentest_set_trigger_high();
  TRY(otcrypto_ecdsa_p256_verify(&public_key, message_digest, &signature,
                                 &verification_result));
  pentest_set_trigger_low();

  // Return data back to host.
  uj_output->result = true;
  if (verification_result != kHardenedBoolTrue) {
    uj_output->result = false;
  }
  uj_output->cfg = 0;

  return OK_STATUS();
}

status_t cryptolib_fi_p384_ecdh_impl(
    cryptolib_fi_asym_p384_ecdh_in_t uj_input,
    cryptolib_fi_asym_p384_ecdh_out_t *uj_output) {
  // Construct the private key object.
  uint32_t private_keyblob[kPentestP384MaskedPrivateKeyWords * 2];
  otcrypto_blinded_key_t private_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeEcdhP384,
              .key_length = kPentestP384Bytes,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelHigh,
          },
      .keyblob_length = sizeof(private_keyblob),
      .keyblob = private_keyblob,
  };

  uint32_t share0[kPentestP384MaskedPrivateKeyWords] = {0};
  uint32_t share1[kPentestP384MaskedPrivateKeyWords] = {0};
  memcpy(share0, uj_input.private_key, P384_CMD_BYTES);

  otcrypto_const_word32_buf_t share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share0, kPentestP384MaskedPrivateKeyWords);
  otcrypto_const_word32_buf_t share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1, kPentestP384MaskedPrivateKeyWords);

  TRY(otcrypto_ecc_p384_private_key_import(share0_buf, share1_buf,
                                           &private_key));

  // Construct the public key object.
  uint32_t public_key_buf[kPentestP384Words * 2];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = sizeof(public_key_buf),
      .key = public_key_buf,
  };

  uint32_t pub_x[kPentestP384Words] = {0};
  uint32_t pub_y[kPentestP384Words] = {0};
  memcpy(pub_x, uj_input.public_x, P384_CMD_BYTES);
  memcpy(pub_y, uj_input.public_y, P384_CMD_BYTES);

  otcrypto_const_word32_buf_t x_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pub_x, kPentestP384Words);
  otcrypto_const_word32_buf_t y_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pub_y, kPentestP384Words);

  TRY(otcrypto_ecc_p384_public_key_import(x_buf, y_buf, &public_key));

  // Create a destination for the shared secret.
  uint32_t shared_secretblob[kPentestP384Words * 2];
  memset(shared_secretblob, 0, sizeof(shared_secretblob));
  otcrypto_blinded_key_t shared_secret = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = kPentestP384Bytes,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelHigh,
          },
      .keyblob_length = sizeof(shared_secretblob),
      .keyblob = shared_secretblob,
  };

  pentest_set_trigger_high();
  TRY(otcrypto_ecdh_p384(&private_key, &public_key, &shared_secret));
  pentest_set_trigger_low();

  uint32_t ss_share0[kPentestP384Words];
  uint32_t ss_share1[kPentestP384Words];
  otcrypto_word32_buf_t ss_share0_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ss_share0, ARRAYSIZE(ss_share0));
  otcrypto_word32_buf_t ss_share1_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ss_share1, ARRAYSIZE(ss_share1));
  uint32_t ss[kPentestP384Words];
  TRY(otcrypto_export_blinded_key(&shared_secret, &ss_share0_buf,
                                  &ss_share1_buf));
  for (size_t i = 0; i < kPentestP384Words; i++) {
    ss[i] = ss_share0[i] ^ ss_share1[i];
  }

  // Return data back to host.
  uj_output->cfg = 0;
  memset(uj_output->shared_key, 0, P384_CMD_BYTES);
  memcpy(uj_output->shared_key, ss, P384_CMD_BYTES);

  return OK_STATUS();
}

status_t cryptolib_fi_p384_sign_impl(
    cryptolib_fi_asym_p384_sign_in_t uj_input,
    cryptolib_fi_asym_p384_sign_out_t *uj_output) {
  static const otcrypto_key_config_t kP384PrivateKeyConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = kPentestP384Bytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelHigh,
  };

  // Create the private key.
  uint32_t private_keyblob[kPentestP384MaskedPrivateKeyWords * 2];
  otcrypto_blinded_key_t private_key = {
      .config = kP384PrivateKeyConfig,
      .keyblob_length = sizeof(private_keyblob),
      .keyblob = private_keyblob,
  };

  uint32_t share0[kPentestP384MaskedPrivateKeyWords] = {0};
  uint32_t share1[kPentestP384MaskedPrivateKeyWords] = {0};
  memcpy(share0, uj_input.scalar, P384_CMD_BYTES);

  otcrypto_const_word32_buf_t share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share0, kPentestP384MaskedPrivateKeyWords);
  otcrypto_const_word32_buf_t share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1, kPentestP384MaskedPrivateKeyWords);

  TRY(otcrypto_ecc_p384_private_key_import(share0_buf, share1_buf,
                                           &private_key));

  // Create the public key.
  uint32_t public_key_buf[kPentestP384Words * 2];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(public_key_buf),
      .key = public_key_buf,
  };

  uint32_t pub_x[kPentestP384Words] = {0};
  uint32_t pub_y[kPentestP384Words] = {0};
  memcpy(pub_x, uj_input.pubx, P384_CMD_BYTES);
  memcpy(pub_y, uj_input.puby, P384_CMD_BYTES);

  otcrypto_const_word32_buf_t x_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pub_x, kPentestP384Words);
  otcrypto_const_word32_buf_t y_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pub_y, kPentestP384Words);

  TRY(otcrypto_ecc_p384_public_key_import(x_buf, y_buf, &public_key));

  // Create a key pair if requested.
  // This will overwrite the private and public key above.
  if (uj_input.cfg == 1) {
    // Trigger window 0.
    if (uj_input.trigger == 0) {
      pentest_set_trigger_high();
    }
    TRY(otcrypto_ecdsa_p384_keygen(&private_key, &public_key));
    pentest_set_trigger_low();
    if (uj_input.trigger == 0) {
      pentest_set_trigger_low();
    }
  }

  // Set up the message buffer.
  uint32_t message_buf[kPentestP384Words];
  memset(message_buf, 0, sizeof(message_buf));
  memcpy(message_buf, uj_input.message, P384_CMD_BYTES);

  const otcrypto_hash_digest_t message_digest = {
      .mode = kOtcryptoHashModeSha384,
      .len = kPentestP384Words,
      .data = (uint32_t *)message_buf,
  };

  // Set up the signature buffer.
  uint32_t sig[kPentestP384Words * 2] = {0};
  otcrypto_word32_buf_t signature_mut =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));

  // Trigger window 1.
  if (uj_input.trigger == 1) {
    pentest_set_trigger_high();
  }
  TRY(otcrypto_ecdsa_p384_sign_verify(&private_key, &public_key, message_digest,
                                      &signature_mut));
  if (uj_input.trigger == 1) {
    pentest_set_trigger_low();
  }

  // Return data back to host.
  uj_output->cfg = 0;
  memset(uj_output->r, 0, P384_CMD_BYTES);
  memset(uj_output->s, 0, P384_CMD_BYTES);

  uint8_t *sig_bytes = (uint8_t *)signature_mut.data;
  memcpy(uj_output->r, sig_bytes, P384_CMD_BYTES);
  memcpy(uj_output->s, sig_bytes + P384_CMD_BYTES, P384_CMD_BYTES);

  // Return the public key.
  uint32_t out_pub_x[kPentestP384Words];
  uint32_t out_pub_y[kPentestP384Words];
  otcrypto_word32_buf_t out_x_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, out_pub_x, kPentestP384Words);
  otcrypto_word32_buf_t out_y_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, out_pub_y, kPentestP384Words);

  TRY(otcrypto_ecc_p384_public_key_export(&public_key, &out_x_buf, &out_y_buf));

  memcpy(uj_output->pubx, out_pub_x, P384_CMD_BYTES);
  memcpy(uj_output->puby, out_pub_y, P384_CMD_BYTES);

  return OK_STATUS();
}

status_t cryptolib_fi_p384_verify_impl(
    cryptolib_fi_asym_p384_verify_in_t uj_input,
    cryptolib_fi_asym_p384_verify_out_t *uj_output) {
  // Set up the message buffer.
  uint32_t message_buf[kPentestP384Words];
  memset(message_buf, 0, sizeof(message_buf));
  memcpy(message_buf, uj_input.message, P384_CMD_BYTES);

  const otcrypto_hash_digest_t message_digest = {
      .mode = kOtcryptoHashModeSha384,
      .len = kPentestP384Words,
      .data = (uint32_t *)message_buf,
  };

  // Setup the public key buffer.
  uint32_t public_key_buf[kPentestP384Words * 2];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(public_key_buf),
      .key = public_key_buf,
  };

  uint32_t pub_x[kPentestP384Words] = {0};
  uint32_t pub_y[kPentestP384Words] = {0};
  memcpy(pub_x, uj_input.pubx, P384_CMD_BYTES);
  memcpy(pub_y, uj_input.puby, P384_CMD_BYTES);

  otcrypto_const_word32_buf_t x_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pub_x, kPentestP384Words);
  otcrypto_const_word32_buf_t y_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pub_y, kPentestP384Words);

  TRY(otcrypto_ecc_p384_public_key_import(x_buf, y_buf, &public_key));

  // Setup the signature buffer.
  uint32_t signature_data[kPentestP384Words * 2] = {0};
  memcpy((uint8_t *)signature_data, uj_input.r, P384_CMD_BYTES);
  memcpy((uint8_t *)signature_data + P384_CMD_BYTES, uj_input.s,
         P384_CMD_BYTES);

  otcrypto_const_word32_buf_t signature = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, signature_data, kPentestP384Words * 2);

  hardened_bool_t verification_result = kHardenedBoolFalse;

  pentest_set_trigger_high();
  TRY(otcrypto_ecdsa_p384_verify(&public_key, message_digest, &signature,
                                 &verification_result));
  pentest_set_trigger_low();

  // Return data back to host.
  uj_output->result = true;
  if (verification_result != kHardenedBoolTrue) {
    uj_output->result = false;
  }
  uj_output->cfg = 0;

  return OK_STATUS();
}

status_t cryptolib_fi_ed25519_sign_impl(
    cryptolib_fi_asym_ed25519_sign_in_t uj_input,
    cryptolib_fi_asym_ed25519_sign_out_t *uj_output) {
  // Set up the private key with the input scalar as seed (share0 = scalar,
  // share1 = 0). Each share is kPentestEd25519MaskedPrivateKeyWords wide
  // (seed bytes + 8 redundant ECC arithmetic extension bytes).
  uint32_t private_keyblob[kPentestEd25519MaskedPrivateKeyWords * 2];
  memset(private_keyblob, 0, sizeof(private_keyblob));
  memcpy(private_keyblob, uj_input.scalar, ED25519_CMD_SCALAR_BYTES);
  otcrypto_blinded_key_t private_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeEd25519,
              .key_length = ED25519_CMD_SCALAR_BYTES,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(private_keyblob),
      .keyblob = private_keyblob,
  };
  private_key.checksum = integrity_blinded_checksum(&private_key);

  // Derive the public key (required by sign_verify).
  uint32_t public_key_data[ED25519_CMD_SCALAR_BYTES / sizeof(uint32_t)];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = ED25519_CMD_SCALAR_BYTES,
      .key = public_key_data,
  };

  // Trigger window 0: Keygen.
  if (uj_input.trigger == 0) {
    pentest_set_trigger_high();
  }
  TRY(otcrypto_ed25519_public_key_from_private(&private_key, &public_key));
  if (uj_input.trigger == 0) {
    pentest_set_trigger_low();
  }

  // Set up the input message.
  otcrypto_const_byte_buf_t input_message = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, uj_input.message, uj_input.message_len);

  // Set up the signature buffer.
  uint32_t signature_data[ED25519_CMD_SIG_BYTES / sizeof(uint32_t)];
  otcrypto_word32_buf_t signature =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, signature_data,
                        ED25519_CMD_SIG_BYTES / sizeof(uint32_t));

  // Trigger window 1: FI-hardened sign-and-verify.
  if (uj_input.trigger == 1) {
    pentest_set_trigger_high();
  }
  TRY(otcrypto_ed25519_sign_verify(&private_key, &public_key, &input_message,
                                   kOtcryptoEddsaSignModeEddsa, &signature));
  if (uj_input.trigger == 1) {
    pentest_set_trigger_low();
  }

  // Return signature: R component (first 32 bytes) in r, S (next 32) in s.
  uj_output->cfg = 0;
  memset(uj_output->r, 0, ED25519_CMD_SIG_BYTES);
  memset(uj_output->s, 0, ED25519_CMD_SIG_BYTES);
  memcpy(uj_output->r, (uint8_t *)signature_data, ED25519_CMD_SIG_BYTES / 2);
  memcpy(uj_output->s, (uint8_t *)signature_data + ED25519_CMD_SIG_BYTES / 2,
         ED25519_CMD_SIG_BYTES / 2);

  // Return the derived public key in pubx; puby is unused for Ed25519.
  memset(uj_output->pubx, 0, ED25519_CMD_SCALAR_BYTES);
  memset(uj_output->puby, 0, ED25519_CMD_SCALAR_BYTES);
  memcpy(uj_output->pubx, public_key_data, ED25519_CMD_SCALAR_BYTES);

  return OK_STATUS();
}

status_t cryptolib_fi_ed25519_verify_impl(
    cryptolib_fi_asym_ed25519_verify_in_t uj_input,
    cryptolib_fi_asym_ed25519_verify_out_t *uj_output) {
  // Reconstruct the 32-byte public key from pubx (puby unused for Ed25519).
  uint32_t public_key_data[ED25519_CMD_SCALAR_BYTES / sizeof(uint32_t)];
  memset(public_key_data, 0, sizeof(public_key_data));
  memcpy(public_key_data, uj_input.pubx, ED25519_CMD_SCALAR_BYTES);

  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = ED25519_CMD_SCALAR_BYTES,
      .key = public_key_data,
  };
  public_key.checksum = integrity_unblinded_checksum(&public_key);

  // Reconstruct the 64-byte signature from r[0..31] and s[0..31].
  uint32_t signature_data[ED25519_CMD_SIG_BYTES / sizeof(uint32_t)];
  memset(signature_data, 0, sizeof(signature_data));
  memcpy((uint8_t *)signature_data, uj_input.r, ED25519_CMD_SIG_BYTES / 2);
  memcpy((uint8_t *)signature_data + ED25519_CMD_SIG_BYTES / 2, uj_input.s,
         ED25519_CMD_SIG_BYTES / 2);

  otcrypto_const_word32_buf_t signature =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, signature_data,
                        ED25519_CMD_SIG_BYTES / sizeof(uint32_t));

  // Set up the input message.
  otcrypto_const_byte_buf_t input_message = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, uj_input.message, uj_input.message_len);

  hardened_bool_t verification_result = kHardenedBoolFalse;

  pentest_set_trigger_high();
  TRY(otcrypto_ed25519_verify(&public_key, &input_message,
                              kOtcryptoEddsaSignModeEddsa, &signature,
                              &verification_result));
  pentest_set_trigger_low();

  // Return data back to host.
  uj_output->result = true;
  if (verification_result != kHardenedBoolTrue) {
    uj_output->result = false;
  }
  uj_output->cfg = 0;

  return OK_STATUS();
}

status_t cryptolib_fi_x25519_base_mul_impl(
    cryptolib_fi_asym_x25519_base_mul_in_t uj_input,
    cryptolib_fi_asym_x25519_base_mul_out_t *uj_output) {
  // Use the Ed25519 masked size since both use the exact same 256-bit curve
  uint32_t private_keyblob[kPentestEd25519MaskedPrivateKeyWords * 2];
  memset(private_keyblob, 0, sizeof(private_keyblob));
  memcpy(private_keyblob, uj_input.scalar, X25519_CMD_BYTES);

  otcrypto_blinded_key_t private_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeX25519,
              .key_length = X25519_CMD_BYTES,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(private_keyblob),
      .keyblob = private_keyblob,
  };
  private_key.checksum = integrity_blinded_checksum(&private_key);

  // Construct public key
  uint32_t public_key_buf[X25519_CMD_BYTES / sizeof(uint32_t)];
  memset(public_key_buf, 0, sizeof(public_key_buf));
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = X25519_CMD_BYTES,
      .key = public_key_buf,
  };

  // FI Trigger window
  if (uj_input.trigger) {
    pentest_set_trigger_high();
  }
  TRY(otcrypto_x25519_keygen(&private_key, &public_key));
  if (uj_input.trigger) {
    pentest_set_trigger_low();
  }

  uj_output->cfg = 0;
  memset(uj_output->x, 0, X25519_CMD_BYTES);
  memset(uj_output->y, 0, X25519_CMD_BYTES);  // X25519 has no Y coordinate
  memcpy(uj_output->x, public_key.key, X25519_CMD_BYTES);

  return OK_STATUS();
}

status_t cryptolib_fi_x25519_ecdh_impl(
    cryptolib_fi_asym_x25519_ecdh_in_t uj_input,
    cryptolib_fi_asym_x25519_ecdh_out_t *uj_output) {
  // Use the Ed25519 masked size since both use the exact same 256-bit curve
  uint32_t private_keyblob[kPentestEd25519MaskedPrivateKeyWords * 2];
  memset(private_keyblob, 0, sizeof(private_keyblob));
  memcpy(private_keyblob, uj_input.private_key, X25519_CMD_BYTES);

  otcrypto_blinded_key_t private_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeX25519,
              .key_length = X25519_CMD_BYTES,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(private_keyblob),
      .keyblob = private_keyblob,
  };
  private_key.checksum = integrity_blinded_checksum(&private_key);

  uint32_t public_key_buf[X25519_CMD_BYTES / sizeof(uint32_t)];
  memset(public_key_buf, 0, sizeof(public_key_buf));
  memcpy(public_key_buf, uj_input.public_x, X25519_CMD_BYTES);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = X25519_CMD_BYTES,
      .key = public_key_buf,
  };
  public_key.checksum = integrity_unblinded_checksum(&public_key);

  uint32_t shared_secretblob[16];
  memset(shared_secretblob, 0, sizeof(shared_secretblob));
  otcrypto_blinded_key_t shared_secret = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = X25519_CMD_BYTES,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(shared_secretblob),
      .keyblob = shared_secretblob,
  };

  // FI Trigger window
  if (uj_input.trigger) {
    pentest_set_trigger_high();
  }
  TRY(otcrypto_x25519(&private_key, &public_key, &shared_secret));
  if (uj_input.trigger) {
    pentest_set_trigger_low();
  }

  uint32_t ss_share0[8];
  uint32_t ss_share1[8];
  otcrypto_word32_buf_t ss_share0_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ss_share0, 8);
  otcrypto_word32_buf_t ss_share1_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ss_share1, 8);

  TRY(otcrypto_export_blinded_key(&shared_secret, &ss_share0_buf,
                                  &ss_share1_buf));

  uint32_t ss_unmasked[8];
  TRY(hardened_add(ss_share0, ss_share1, 8, ss_unmasked));

  uj_output->cfg = 0;
  memset(uj_output->shared_key, 0, X25519_CMD_BYTES);
  memcpy(uj_output->shared_key, ss_unmasked, X25519_CMD_BYTES);

  return OK_STATUS();
}

status_t cryptolib_fi_x25519_point_mul_impl(
    cryptolib_fi_asym_x25519_point_mul_in_t uj_input,
    cryptolib_fi_asym_x25519_point_mul_out_t *uj_output) {
  // Point multiplication in X25519 is equivalent to ECDH
  // where Bob's scalar is used as the base point.
  cryptolib_fi_asym_x25519_ecdh_in_t ecdh_in;
  memcpy(ecdh_in.private_key, uj_input.scalar_alice, X25519_CMD_BYTES);
  memcpy(ecdh_in.public_x, uj_input.scalar_bob, X25519_CMD_BYTES);
  memset(ecdh_in.public_y, 0, X25519_CMD_BYTES);  // Ignored
  ecdh_in.cfg = uj_input.cfg;
  ecdh_in.trigger = uj_input.trigger;

  cryptolib_fi_asym_x25519_ecdh_out_t ecdh_out;
  TRY(cryptolib_fi_x25519_ecdh_impl(ecdh_in, &ecdh_out));

  memcpy(uj_output->x, ecdh_out.shared_key, X25519_CMD_BYTES);
  memset(uj_output->y, 0, X25519_CMD_BYTES);
  uj_output->cfg = ecdh_out.cfg;

  return OK_STATUS();
}
