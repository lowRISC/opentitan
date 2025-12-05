// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/cryptolib_fi_asym_impl.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/ecc/p256.h"
#include "sw/device/lib/crypto/impl/ecc/p384.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/tests/penetrationtests/firmware/lib/cryptolib_asym.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/cryptolib_fi_asym_commands.h"

#define MODULE_ID MAKE_MODULE_ID('f', 'a', 'i')

// Markers in the dis file to be able to trace certain functions
#define PENTEST_MARKER_LABEL(name) asm volatile(#name ":" ::: "memory")

// OAEP label for testing.
static const unsigned char kTestLabel[] = "Test label.";
static const size_t kTestLabelLen = sizeof(kTestLabel) - 1;

// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

status_t cryptolib_fi_rsa_enc_impl(cryptolib_fi_asym_rsa_enc_in_t uj_input,
                                   cryptolib_fi_asym_rsa_enc_out_t *uj_output) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

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

  otcrypto_const_word32_buf_t modulus = {
      .data = n_buf,
      .len = num_words,
  };

  // Create label.
  otcrypto_const_byte_buf_t label_buf = {.data = kTestLabel,
                                         .len = kTestLabelLen};

  if (uj_input.op_enc) {
    // Encryption.
    uint32_t public_key_data[ceil_div(public_key_bytes, sizeof(uint32_t))];

    // Construct the public key.
    otcrypto_unblinded_key_t public_key = {
        .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
        .key_length = public_key_bytes,
        .key = public_key_data,
    };
    HARDENED_TRY(
        otcrypto_rsa_public_key_construct(rsa_size, modulus, &public_key));

    // Create input message.
    uint8_t msg_buf[num_words];
    memcpy(msg_buf, uj_input.data, uj_input.data_len);
    otcrypto_const_byte_buf_t input_message = {
        .len = uj_input.data_len,
        .data = msg_buf,
    };

    // Output buffer.
    uint32_t ciphertext_buf[kPentestRsaMaxMsgWords];
    otcrypto_word32_buf_t ciphertext = {
        .data = ciphertext_buf,
        .len = num_words,
    };

    // Trigger window.
    if (uj_input.trigger & kPentestTrigger1) {
      pentest_set_trigger_high();
    }
    otcrypto_status_t status_out = otcrypto_rsa_encrypt(
        &public_key, hash_mode, input_message, label_buf, ciphertext);
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

    otcrypto_const_word32_buf_t d_share0 = {
        .data = d_buf,
        .len = num_words,
    };
    uint32_t share1[kPentestRsaMaxDWords] = {0};
    otcrypto_const_word32_buf_t d_share1 = {
        .data = share1,
        .len = num_words,
    };

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
    HARDENED_TRY(otcrypto_rsa_private_key_from_exponents(
        rsa_size, modulus, d_share0, d_share1, &private_key));
    if (uj_input.trigger & kPentestTrigger1) {
      pentest_set_trigger_low();
    }

    uint32_t ciphertext_buf[num_words];
    memset(ciphertext_buf, 0, sizeof(ciphertext_buf));
    memcpy(ciphertext_buf, uj_input.data, uj_input.data_len);

    otcrypto_const_word32_buf_t ciphertext = {
        .len = num_words,
        .data = ciphertext_buf,
    };

    // Create output buffer for the plaintext.
    size_t kMaxPlaintextBytes = num_bytes - 2 * hash_digest_bytes - 2;
    uint8_t plaintext_buf[kMaxPlaintextBytes];
    otcrypto_byte_buf_t plaintext = {
        .data = plaintext_buf,
        .len = kMaxPlaintextBytes,
    };

    size_t msg_len;
    // Trigger window.
    if (uj_input.trigger & kPentestTrigger2) {
      pentest_set_trigger_high();
    }
    HARDENED_TRY(otcrypto_rsa_decrypt(&private_key, hash_mode, ciphertext,
                                      label_buf, plaintext, &msg_len));
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

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output->err_status = codes;
  memcpy(uj_output->alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output->loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output->ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));

  return OK_STATUS();
}

status_t cryptolib_fi_rsa_sign_impl(
    cryptolib_fi_asym_rsa_sign_in_t uj_input,
    cryptolib_fi_asym_rsa_sign_out_t *uj_output) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

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

  otcrypto_const_word32_buf_t d_share0 = {
      .data = d_buf,
      .len = num_words,
  };
  uint32_t share1[kPentestRsaMaxDWords] = {0};
  otcrypto_const_word32_buf_t d_share1 = {
      .data = share1,
      .len = num_words,
  };

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

  otcrypto_const_word32_buf_t modulus = {
      .data = n_buf,
      .len = num_words,
  };

  // Trigger window.
  if (uj_input.trigger & kPentestTrigger1) {
    pentest_set_trigger_high();
  }
  HARDENED_TRY(otcrypto_rsa_private_key_from_exponents(
      rsa_size, modulus, d_share0, d_share1, &private_key));
  if (uj_input.trigger & kPentestTrigger1) {
    pentest_set_trigger_low();
  }

  // Copy the message into the buffer.
  uint8_t msg[uj_input.data_len];
  memcpy(msg, uj_input.data, uj_input.data_len);
  otcrypto_const_byte_buf_t msg_buf = {
      .len = uj_input.data_len,
      .data = msg,
  };

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
    HARDENED_TRY(otcrypto_sha2_256(msg_buf, &msg_digest));
  } else if (hash_mode == kOtcryptoHashModeSha384) {
    HARDENED_TRY(otcrypto_sha2_384(msg_buf, &msg_digest));
  } else {
    HARDENED_TRY(otcrypto_sha2_512(msg_buf, &msg_digest));
  }
  if (uj_input.trigger & kPentestTrigger2) {
    pentest_set_trigger_low();
  }

  uint32_t sig[kPentestRsaMaxMsgWords];
  otcrypto_word32_buf_t sig_buf = {
      .data = sig,
      .len = num_words,
  };

  // Trigger window.
  if (uj_input.trigger & kPentestTrigger3) {
    PENTEST_MARKER_LABEL(PENTEST_MARKER_RSA_SIGN_START);
    pentest_set_trigger_high();
  }
  HARDENED_TRY(
      otcrypto_rsa_sign(&private_key, msg_digest, padding_mode, sig_buf));
  // Trigger window.
  if (uj_input.trigger & kPentestTrigger3) {
    pentest_set_trigger_low();
    PENTEST_MARKER_LABEL(PENTEST_MARKER_RSA_SIGN_END);
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

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output->err_status = codes;
  memcpy(uj_output->alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output->loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output->ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));

  return OK_STATUS();
}

status_t cryptolib_fi_rsa_verify_impl(
    cryptolib_fi_asym_rsa_verify_in_t uj_input,
    cryptolib_fi_asym_rsa_verify_out_t *uj_output) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

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

  otcrypto_const_word32_buf_t modulus = {
      .data = n_buf,
      .len = num_words,
  };

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
  HARDENED_TRY(
      otcrypto_rsa_public_key_construct(rsa_size, modulus, &public_key));
  // Trigger window.
  if (uj_input.trigger & kPentestTrigger1) {
    pentest_set_trigger_low();
  }

  // Create the signature buffer.
  uint32_t sig_buf[num_words];
  memset(sig_buf, 0, sizeof(sig_buf));
  memcpy(sig_buf, uj_input.sig, uj_input.sig_len);

  otcrypto_const_word32_buf_t sig = {
      .data = sig_buf,
      .len = num_words,
  };

  // Copy the message into the buffer.
  uint8_t msg[uj_input.data_len];
  memcpy(msg, uj_input.data, uj_input.data_len);
  otcrypto_const_byte_buf_t msg_buf = {
      .len = uj_input.data_len,
      .data = msg,
  };

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
    HARDENED_TRY(otcrypto_sha2_256(msg_buf, &msg_digest));
  } else if (hash_mode == kOtcryptoHashModeSha384) {
    HARDENED_TRY(otcrypto_sha2_384(msg_buf, &msg_digest));
  } else {
    HARDENED_TRY(otcrypto_sha2_512(msg_buf, &msg_digest));
  }
  if (uj_input.trigger & kPentestTrigger2) {
    pentest_set_trigger_low();
  }

  hardened_bool_t verification_result;
  // Trigger window.
  if (uj_input.trigger & kPentestTrigger3) {
    PENTEST_MARKER_LABEL(PENTEST_MARKER_RSA_VERIFY_START);
    pentest_set_trigger_high();
  }
  HARDENED_TRY(otcrypto_rsa_verify(&public_key, msg_digest, padding_mode, sig,
                                   &verification_result));
  if (uj_input.trigger & kPentestTrigger3) {
    pentest_set_trigger_low();
    PENTEST_MARKER_LABEL(PENTEST_MARKER_RSA_VERIFY_END);
  }

  // Return data back to host.
  uj_output->result = true;
  if (verification_result != kHardenedBoolTrue) {
    uj_output->result = false;
  }
  uj_output->cfg = 0;

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output->err_status = codes;
  memcpy(uj_output->alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output->loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output->ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));

  return OK_STATUS();
}

status_t cryptolib_fi_p256_ecdh_impl(
    cryptolib_fi_asym_p256_ecdh_in_t uj_input,
    cryptolib_fi_asym_p256_ecdh_out_t *uj_output) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Construct the private key object.
  uint32_t private_keyblob[kPentestP256MaskedPrivateKeyWords * 2];
  memset(private_keyblob, 0, sizeof(private_keyblob));
  memcpy(private_keyblob, uj_input.private_key, P256_CMD_BYTES);
  memcpy(private_keyblob + kPentestP256MaskedPrivateKeyWords, 0,
         P256_CMD_BYTES);
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
      .checksum = 0,
  };
  private_key.checksum = integrity_blinded_checksum(&private_key);

  // Construct the public key object.
  uint32_t public_key_buf[kPentestP256Words * 2];
  memset(public_key_buf, 0, sizeof(public_key_buf));
  memcpy(public_key_buf, uj_input.public_x, P256_CMD_BYTES);
  memcpy(public_key_buf + kPentestP256Words, uj_input.public_y, P256_CMD_BYTES);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP256,
      .key_length = sizeof(public_key_buf),
      .key = public_key_buf,
  };
  public_key.checksum = integrity_unblinded_checksum(&public_key);

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

  PENTEST_MARKER_LABEL(PENTEST_MARKER_P256_ECDH_START);
  pentest_set_trigger_high();
  HARDENED_TRY(otcrypto_ecdh_p256(&private_key, &public_key, &shared_secret));
  pentest_set_trigger_low();
  PENTEST_MARKER_LABEL(PENTEST_MARKER_P256_ECDH_END);

  uint32_t share0[kPentestP256Words];
  uint32_t share1[kPentestP256Words];
  uint32_t ss[kPentestP256Words];
  HARDENED_TRY(otcrypto_export_blinded_key(
      &shared_secret,
      (otcrypto_word32_buf_t){.data = share0, .len = ARRAYSIZE(share0)},
      (otcrypto_word32_buf_t){.data = share1, .len = ARRAYSIZE(share1)}));
  for (size_t i = 0; i < kPentestP256Words; i++) {
    ss[i] = share0[i] ^ share1[i];
  }

  // Return data back to host.
  uj_output->cfg = 0;
  memset(uj_output->shared_key, 0, P256_CMD_BYTES);
  memcpy(uj_output->shared_key, ss, P256_CMD_BYTES);

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output->err_status = codes;
  memcpy(uj_output->alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output->loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output->ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));

  return OK_STATUS();
}

status_t cryptolib_fi_p256_sign_impl(
    cryptolib_fi_asym_p256_sign_in_t uj_input,
    cryptolib_fi_asym_p256_sign_out_t *uj_output) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  static const otcrypto_key_config_t kP256PrivateKeyConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = kPentestP256Bytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelHigh,
  };

  // Create the private key.
  p256_masked_scalar_t private_key_masked;
  otcrypto_blinded_key_t private_key = {
      .config = kP256PrivateKeyConfig,
      .keyblob_length = kP256MaskedScalarTotalShareBytes,
      .keyblob = (uint32_t *)&private_key_masked,
  };
  memset(private_key_masked.share0, 0, kP256MaskedScalarShareBytes);
  memcpy(private_key_masked.share0, uj_input.scalar, kP256ScalarBytes);
  memset(private_key_masked.share1, 0, kP256MaskedScalarShareBytes);
  private_key.checksum = integrity_blinded_checksum(&private_key);

  // Create the public key.
  p256_point_t pub_p256;
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(p256_point_t),
      .key = (uint32_t *)&pub_p256,
  };
  memset(pub_p256.x, 0, kP256CoordBytes);
  memcpy(pub_p256.x, uj_input.pubx, P256_CMD_BYTES);
  memset(pub_p256.y, 0, kP256CoordBytes);
  memcpy(pub_p256.y, uj_input.puby, P256_CMD_BYTES);
  public_key.checksum = integrity_unblinded_checksum(&public_key);

  // Create a key pair if requested.
  // This will overwrite the private and public key above.
  if (uj_input.cfg == 1) {
    // Trigger window 0.
    if (uj_input.trigger == 0) {
      pentest_set_trigger_high();
    }
    HARDENED_TRY(otcrypto_ecdsa_p256_keygen(&private_key, &public_key));
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
  otcrypto_word32_buf_t signature_mut = {
      .data = sig,
      .len = ARRAYSIZE(sig),
  };

  // Trigger window 1.
  if (uj_input.trigger == 1) {
    PENTEST_MARKER_LABEL(PENTEST_MARKER_P256_SIGN_START);
    pentest_set_trigger_high();
  }
  // Sign the message.
  HARDENED_TRY(otcrypto_ecdsa_p256_sign_verify(&private_key, &public_key,
                                               message_digest, signature_mut));
  if (uj_input.trigger == 1) {
    pentest_set_trigger_low();
    PENTEST_MARKER_LABEL(PENTEST_MARKER_P256_SIGN_END);
  }

  // Return data back to host.
  uj_output->cfg = 0;
  memset(uj_output->r, 0, P256_CMD_BYTES);
  memset(uj_output->s, 0, P256_CMD_BYTES);
  p256_ecdsa_signature_t *signature_p256 =
      (p256_ecdsa_signature_t *)signature_mut.data;
  memcpy(uj_output->r, signature_p256->r, kP256ScalarBytes);
  memcpy(uj_output->s, signature_p256->s, kP256ScalarBytes);

  // Return the public key.
  p256_point_t *pub = (p256_point_t *)public_key.key;
  memcpy(uj_output->pubx, pub->x, P256_CMD_BYTES);
  memcpy(uj_output->puby, pub->y, P256_CMD_BYTES);

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output->err_status = codes;
  memcpy(uj_output->alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output->loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output->ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));

  return OK_STATUS();
}

status_t cryptolib_fi_p256_verify_impl(
    cryptolib_fi_asym_p256_verify_in_t uj_input,
    cryptolib_fi_asym_p256_verify_out_t *uj_output) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

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
  p256_point_t pub_p256;
  memcpy(pub_p256.x, uj_input.pubx, P256_CMD_BYTES);
  memcpy(pub_p256.y, uj_input.puby, P256_CMD_BYTES);

  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(p256_point_t),
      .key = (uint32_t *)&pub_p256,
  };
  public_key.checksum = integrity_unblinded_checksum(&public_key);

  // Setup the signature buffer.
  p256_ecdsa_signature_t signature_p256;
  memcpy(signature_p256.r, uj_input.r, P256_CMD_BYTES);
  memcpy(signature_p256.s, uj_input.s, P256_CMD_BYTES);

  otcrypto_const_word32_buf_t signature = {
      .len = kPentestP256Words * 2,
      .data = (uint32_t *)&signature_p256,
  };

  hardened_bool_t verification_result = kHardenedBoolFalse;

  PENTEST_MARKER_LABEL(PENTEST_MARKER_P256_VERIFY_START);
  pentest_set_trigger_high();
  HARDENED_TRY(otcrypto_ecdsa_p256_verify(&public_key, message_digest,
                                          signature, &verification_result));
  pentest_set_trigger_low();
  PENTEST_MARKER_LABEL(PENTEST_MARKER_P256_VERIFY_END);

  // Return data back to host.
  uj_output->result = true;
  if (verification_result != kHardenedBoolTrue) {
    uj_output->result = false;
  }
  uj_output->cfg = 0;

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output->err_status = codes;
  memcpy(uj_output->alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output->loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output->ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));

  return OK_STATUS();
}

status_t cryptolib_fi_p384_ecdh_impl(
    cryptolib_fi_asym_p384_ecdh_in_t uj_input,
    cryptolib_fi_asym_p384_ecdh_out_t *uj_output) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Construct the private key object.
  uint32_t private_keyblob[kPentestP384MaskedPrivateKeyWords * 2];
  memset(private_keyblob, 0, sizeof(private_keyblob));
  memcpy(private_keyblob, uj_input.private_key, P384_CMD_BYTES);
  memcpy(private_keyblob + kPentestP384MaskedPrivateKeyWords, 0,
         P384_CMD_BYTES);
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
      .checksum = 0,
  };
  private_key.checksum = integrity_blinded_checksum(&private_key);

  // Construct the public key object.
  uint32_t public_key_buf[kPentestP384Words * 2];
  memset(public_key_buf, 0, sizeof(public_key_buf));
  memcpy(public_key_buf, uj_input.public_x, P384_CMD_BYTES);
  memcpy(public_key_buf + kPentestP384Words, uj_input.public_y, P384_CMD_BYTES);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = sizeof(public_key_buf),
      .key = public_key_buf,
  };
  public_key.checksum = integrity_unblinded_checksum(&public_key);

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

  PENTEST_MARKER_LABEL(PENTEST_MARKER_P384_ECDH_START);
  pentest_set_trigger_high();
  HARDENED_TRY(otcrypto_ecdh_p384(&private_key, &public_key, &shared_secret));
  pentest_set_trigger_low();
  PENTEST_MARKER_LABEL(PENTEST_MARKER_P384_ECDH_END);

  uint32_t share0[kPentestP384Words];
  uint32_t share1[kPentestP384Words];
  uint32_t ss[kPentestP384Words];
  HARDENED_TRY(otcrypto_export_blinded_key(
      &shared_secret,
      (otcrypto_word32_buf_t){.data = share0, .len = ARRAYSIZE(share0)},
      (otcrypto_word32_buf_t){.data = share1, .len = ARRAYSIZE(share1)}));
  for (size_t i = 0; i < kPentestP384Words; i++) {
    ss[i] = share0[i] ^ share1[i];
  }

  // Return data back to host.
  uj_output->cfg = 0;
  memset(uj_output->shared_key, 0, P384_CMD_BYTES);
  memcpy(uj_output->shared_key, ss, P384_CMD_BYTES);

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output->err_status = codes;
  memcpy(uj_output->alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output->loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output->ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));

  return OK_STATUS();
}

status_t cryptolib_fi_p384_sign_impl(
    cryptolib_fi_asym_p384_sign_in_t uj_input,
    cryptolib_fi_asym_p384_sign_out_t *uj_output) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  static const otcrypto_key_config_t kP384PrivateKeyConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = kPentestP384Bytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelHigh,
  };

  // Create the private key.
  p384_masked_scalar_t private_key_masked;
  otcrypto_blinded_key_t private_key = {
      .config = kP384PrivateKeyConfig,
      .keyblob_length = kP384MaskedScalarTotalShareBytes,
      .keyblob = (uint32_t *)&private_key_masked,
  };
  memset(private_key_masked.share0, 0, kP384MaskedScalarShareBytes);
  memcpy(private_key_masked.share0, uj_input.scalar, kP384ScalarBytes);
  memset(private_key_masked.share1, 0, kP384MaskedScalarShareBytes);
  private_key.checksum = integrity_blinded_checksum(&private_key);

  // Create the public key.
  p384_point_t pub_p384;
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(p384_point_t),
      .key = (uint32_t *)&pub_p384,
  };
  memset(pub_p384.x, 0, kP384CoordBytes);
  memcpy(pub_p384.x, uj_input.pubx, P384_CMD_BYTES);
  memset(pub_p384.y, 0, kP384CoordBytes);
  memcpy(pub_p384.y, uj_input.puby, P384_CMD_BYTES);
  public_key.checksum = integrity_unblinded_checksum(&public_key);

  // Create a key pair if requested.
  // This will overwrite the private and public key above.
  if (uj_input.cfg == 1) {
    // Trigger window 0.
    if (uj_input.trigger == 0) {
      pentest_set_trigger_high();
    }
    HARDENED_TRY(otcrypto_ecdsa_p384_keygen(&private_key, &public_key));
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
  otcrypto_word32_buf_t signature_mut = {
      .data = sig,
      .len = ARRAYSIZE(sig),
  };

  // Trigger window 1.
  if (uj_input.trigger == 1) {
    PENTEST_MARKER_LABEL(PENTEST_MARKER_P384_SIGN_START);
    pentest_set_trigger_high();
  }
  HARDENED_TRY(otcrypto_ecdsa_p384_sign_verify(&private_key, &public_key,
                                               message_digest, signature_mut));
  if (uj_input.trigger == 1) {
    pentest_set_trigger_low();
    PENTEST_MARKER_LABEL(PENTEST_MARKER_P384_SIGN_END);
  }

  // Return data back to host.
  uj_output->cfg = 0;
  memset(uj_output->r, 0, P384_CMD_BYTES);
  memset(uj_output->s, 0, P384_CMD_BYTES);
  p384_ecdsa_signature_t *signature_p384 =
      (p384_ecdsa_signature_t *)signature_mut.data;
  memcpy(uj_output->r, signature_p384->r, kP384ScalarBytes);
  memcpy(uj_output->s, signature_p384->s, kP384ScalarBytes);

  // Return the public key.
  p384_point_t *pub = (p384_point_t *)public_key.key;
  memcpy(uj_output->pubx, pub->x, P384_CMD_BYTES);
  memcpy(uj_output->puby, pub->y, P384_CMD_BYTES);

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output->err_status = codes;
  memcpy(uj_output->alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output->loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output->ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));

  return OK_STATUS();
}

status_t cryptolib_fi_p384_verify_impl(
    cryptolib_fi_asym_p384_verify_in_t uj_input,
    cryptolib_fi_asym_p384_verify_out_t *uj_output) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();
  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

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
  p384_point_t pub_p384;
  memcpy(pub_p384.x, uj_input.pubx, P384_CMD_BYTES);
  memcpy(pub_p384.y, uj_input.puby, P384_CMD_BYTES);

  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(p384_point_t),
      .key = (uint32_t *)&pub_p384,
  };
  public_key.checksum = integrity_unblinded_checksum(&public_key);

  // Setup the signature buffer.
  p384_ecdsa_signature_t signature_p384;
  memcpy(signature_p384.r, uj_input.r, P384_CMD_BYTES);
  memcpy(signature_p384.s, uj_input.s, P384_CMD_BYTES);

  otcrypto_const_word32_buf_t signature = {
      .len = kPentestP384Words * 2,
      .data = (uint32_t *)&signature_p384,
  };

  hardened_bool_t verification_result = kHardenedBoolFalse;

  PENTEST_MARKER_LABEL(PENTEST_MARKER_P384_VERIFY_START);
  pentest_set_trigger_high();
  HARDENED_TRY(otcrypto_ecdsa_p384_verify(&public_key, message_digest,
                                          signature, &verification_result));
  pentest_set_trigger_low();
  PENTEST_MARKER_LABEL(PENTEST_MARKER_P384_VERIFY_END);

  // Return data back to host.
  uj_output->result = true;
  if (verification_result != kHardenedBoolTrue) {
    uj_output->result = false;
  }
  uj_output->cfg = 0;

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();
  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));
  uj_output->err_status = codes;
  memcpy(uj_output->alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output->loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output->ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));

  return OK_STATUS();
}
