// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/ecdh_commands.h"

enum {
  /**
   * Bytes in one share of an unmasked P-256 private key.
   */
  kP256PrivateKeyBytes = 32,
  /**
   * Bytes in one share of a masked P-256 private key.
   */
  kP256MaskedPrivateKeyBytes = 40,
  /**
   * Words in one share of a masked P-256 private key.
   */
  kP256MaskedPrivateKeyWords = kP256MaskedPrivateKeyBytes / sizeof(uint32_t),
  /**
   * Bytes in a P-256 public key coordinate.
   */
  kP256CoordinateBytes = 32,
  /**
   * Words in a P-256 public key coordinate.
   */
  kP256CoordinateWords = kP256CoordinateBytes / sizeof(uint32_t),
  /**
   * Bytes in one share of an ECDH/P-256 shared secret.
   */
  kP256SharedSecretBytes = 32,
  /**
   * Bytes in one share of an unmasked P-384 private key.
   */
  kP384PrivateKeyBytes = 48,
  /**
   * Bytes in one share of a masked P-384 private key.
   */
  kP384MaskedPrivateKeyBytes = 56,
  /**
   * Words in one share of a masked P-384 private key.
   */
  kP384MaskedPrivateKeyWords = kP384MaskedPrivateKeyBytes / sizeof(uint32_t),
  /**
   * Bytes in a P-384 public key coordinate.
   */
  kP384CoordinateBytes = 48,
  /**
   * Words in a P-384 public key coordinate.
   */
  kP384CoordinateWords = kP384CoordinateBytes / sizeof(uint32_t),
  /**
   * Bytes in one share of an ECDH/P-384 shared secret.
   */
  kP384SharedSecretBytes = 48,
};

/**
 * Run ECDH with curve P-256.
 *
 * The caller should ensure at least kP256SharedSecretBytes of space are
 * allocated at `ss`.
 *
 * If the cryptolib returns an error saying the input is invalid, the shared
 * secret will be zero and the `valid` output will be false.
 *
 * @param d Private key.
 * @param qx Public key x coordinate.
 * @param qy Public key y coordinate.
 * @param[out] ss Shared secret key.
 * @param[out] valid Whether the input arguments were valid.
 * @return Status code (OK or error).
 */
static status_t ecdh_p256(cryptotest_ecdh_private_key_t d,
                          cryptotest_ecdh_coordinate_t qx,
                          cryptotest_ecdh_coordinate_t qy, uint32_t *ss,
                          bool *valid) {
  if (d.d0_len > kP256MaskedPrivateKeyBytes ||
      d.d1_len > kP256MaskedPrivateKeyBytes) {
    LOG_ERROR(
        "Bad P-256 private key share length (should both be <= %d): (d0 = %d, "
        "d1 "
        "= %d)",
        kP256PrivateKeyBytes, d.d0_len, d.d1_len);
    return INVALID_ARGUMENT();
  }
  if (qx.coordinate_len > kP256CoordinateBytes ||
      qy.coordinate_len > kP256CoordinateBytes) {
    LOG_ERROR(
        "Bad P-256 coordinate length (should both be <= %d): (x = %d, y = %d)",
        kP256CoordinateBytes, qx.coordinate_len, qy.coordinate_len);
    return INVALID_ARGUMENT();
  }

  // Construct the private key object.
  uint32_t private_keyblob[kP256MaskedPrivateKeyWords * 2];
  otcrypto_blinded_key_t private_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeEcdhP256,
              .key_length = kP256PrivateKeyBytes,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(private_keyblob),
      .keyblob = private_keyblob,
  };

  uint32_t p256_share0_data[kP256MaskedPrivateKeyWords] = {0};
  uint32_t p256_share1_data[kP256MaskedPrivateKeyWords] = {0};
  memcpy(p256_share0_data, d.d0, d.d0_len);
  memcpy(p256_share1_data, d.d1, d.d1_len);

  otcrypto_const_word32_buf_t share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, p256_share0_data,
                        kP256MaskedPrivateKeyWords);
  otcrypto_const_word32_buf_t share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, p256_share1_data,
                        kP256MaskedPrivateKeyWords);

  otcrypto_status_t priv_status =
      otcrypto_ecc_p256_private_key_import(share0, share1, &private_key);
  if (priv_status.value == kOtcryptoStatusValueBadArgs) {
    *valid = false;
    memset(ss, 0, kP256SharedSecretBytes);
    return OK_STATUS();
  }
  TRY(priv_status);

  // Construct the public key object.
  uint32_t public_key_buf[kP256CoordinateWords * 2];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP256,
      .key_length = sizeof(public_key_buf),
      .key = public_key_buf,
  };

  uint32_t p256_x_data[kP256CoordinateWords] = {0};
  uint32_t p256_y_data[kP256CoordinateWords] = {0};
  memcpy(p256_x_data, qx.coordinate, qx.coordinate_len);
  memcpy(p256_y_data, qy.coordinate, qy.coordinate_len);

  otcrypto_const_word32_buf_t x = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, p256_x_data, kP256CoordinateWords);
  otcrypto_const_word32_buf_t y = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, p256_y_data, kP256CoordinateWords);

  otcrypto_status_t pub_status =
      otcrypto_ecc_p256_public_key_import(x, y, &public_key);
  if (pub_status.value == kOtcryptoStatusValueBadArgs) {
    *valid = false;
    memset(ss, 0, kP256SharedSecretBytes);
    return OK_STATUS();
  }
  TRY(pub_status);

  // Create a destination for the shared secret.
  size_t shared_secret_words = kP256SharedSecretBytes / sizeof(uint32_t);
  uint32_t shared_secretblob[shared_secret_words * 2];
  memset(shared_secretblob, 0, sizeof(shared_secretblob));
  otcrypto_blinded_key_t shared_secret = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = kP256SharedSecretBytes,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(shared_secretblob),
      .keyblob = shared_secretblob,
  };

  otcrypto_status_t status =
      otcrypto_ecdh_p256(&private_key, &public_key, &shared_secret);
  switch (status.value) {
    case kOtcryptoStatusValueOk: {
      *valid = true;
      break;
    }
    case kOtcryptoStatusValueBadArgs: {
      // If the input was rejected (e.g. invalid public key, exit early.
      *valid = false;
      memset(ss, 0, kP256SharedSecretBytes);
      return OK_STATUS();
    }
    default: {
      TRY(status);
      break;
    }
  }

  // Unmask the shared secret.
  uint32_t dest_share0[shared_secret_words];
  uint32_t dest_share1[shared_secret_words];
  otcrypto_word32_buf_t share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, dest_share0, ARRAYSIZE(dest_share0));
  otcrypto_word32_buf_t share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, dest_share1, ARRAYSIZE(dest_share1));
  TRY(otcrypto_export_blinded_key(&shared_secret, &share0_buf, &share1_buf));
  TRY(hardened_xor(dest_share0, dest_share1, shared_secret_words, ss));
  return OK_STATUS();
}

/**
 * Run ECDH with curve P-384.
 *
 * The caller should ensure at least kP384SharedSecretBytes of space are
 * allocated at `ss`.
 *
 * If the cryptolib returns an error saying the input is invalid, the shared
 * secret will be zero and the `valid` output will be false.
 *
 * @param d Private key.
 * @param qx Public key x coordinate.
 * @param qy Public key y coordinate.
 * @param[out] ss Shared secret key.
 * @param[out] valid Whether the input arguments were valid.
 * @return Status code (OK or error).
 */
static status_t ecdh_p384(cryptotest_ecdh_private_key_t d,
                          cryptotest_ecdh_coordinate_t qx,
                          cryptotest_ecdh_coordinate_t qy, uint32_t *ss,
                          bool *valid) {
  if (d.d0_len > kP384MaskedPrivateKeyBytes ||
      d.d1_len > kP384MaskedPrivateKeyBytes) {
    LOG_ERROR(
        "Bad P-384 private key share length (should both be <= %d): (d0 = %d, "
        "d1 "
        "= %d)",
        kP384PrivateKeyBytes, d.d0_len, d.d1_len);
    return INVALID_ARGUMENT();
  }
  if (qx.coordinate_len > kP384CoordinateBytes ||
      qy.coordinate_len > kP384CoordinateBytes) {
    LOG_ERROR(
        "Bad P-384 coordinate length (should both be <= %d): (x = %d, y = %d)",
        kP384CoordinateBytes, qx.coordinate_len, qy.coordinate_len);
    return INVALID_ARGUMENT();
  }

  // Construct the private key object.
  uint32_t private_keyblob[kP384MaskedPrivateKeyWords * 2];
  otcrypto_blinded_key_t private_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeEcdhP384,
              .key_length = kP384PrivateKeyBytes,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(private_keyblob),
      .keyblob = private_keyblob,
  };

  // Note: the test harness might not produce the extra masking bytes; leaving
  // them safely zeroed by explicitly copying into padded buffers.
  uint32_t p384_share0_data[kP384MaskedPrivateKeyWords] = {0};
  uint32_t p384_share1_data[kP384MaskedPrivateKeyWords] = {0};
  memcpy(p384_share0_data, d.d0, d.d0_len);
  memcpy(p384_share1_data, d.d1, d.d1_len);

  otcrypto_const_word32_buf_t share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, p384_share0_data,
                        kP384MaskedPrivateKeyWords);
  otcrypto_const_word32_buf_t share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, p384_share1_data,
                        kP384MaskedPrivateKeyWords);

  otcrypto_status_t priv_status =
      otcrypto_ecc_p384_private_key_import(share0, share1, &private_key);
  if (priv_status.value == kOtcryptoStatusValueBadArgs) {
    *valid = false;
    memset(ss, 0, kP384SharedSecretBytes);
    return OK_STATUS();
  }
  TRY(priv_status);

  // Construct the public key object.
  uint32_t public_key_buf[kP384CoordinateWords * 2];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = sizeof(public_key_buf),
      .key = public_key_buf,
  };

  uint32_t p384_x_data[kP384CoordinateWords] = {0};
  uint32_t p384_y_data[kP384CoordinateWords] = {0};
  memcpy(p384_x_data, qx.coordinate, qx.coordinate_len);
  memcpy(p384_y_data, qy.coordinate, qy.coordinate_len);

  otcrypto_const_word32_buf_t x = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, p384_x_data, kP384CoordinateWords);
  otcrypto_const_word32_buf_t y = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, p384_y_data, kP384CoordinateWords);

  otcrypto_status_t pub_status =
      otcrypto_ecc_p384_public_key_import(x, y, &public_key);
  if (pub_status.value == kOtcryptoStatusValueBadArgs) {
    *valid = false;
    memset(ss, 0, kP384SharedSecretBytes);
    return OK_STATUS();
  }
  TRY(pub_status);

  // Create a destination for the shared secret.
  size_t shared_secret_words = kP384SharedSecretBytes / sizeof(uint32_t);
  uint32_t shared_secretblob[shared_secret_words * 2];
  memset(shared_secretblob, 0, sizeof(shared_secretblob));
  otcrypto_blinded_key_t shared_secret = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = kP384SharedSecretBytes,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(shared_secretblob),
      .keyblob = shared_secretblob,
  };

  otcrypto_status_t status =
      otcrypto_ecdh_p384(&private_key, &public_key, &shared_secret);
  switch (status.value) {
    case kOtcryptoStatusValueOk: {
      *valid = true;
      break;
    }
    case kOtcryptoStatusValueBadArgs: {
      // If the input was rejected (e.g. invalid public key, exit early.
      *valid = false;
      memset(ss, 0, kP384SharedSecretBytes);
      return OK_STATUS();
    }
    default: {
      TRY(status);
      break;
    }
  }

  // Unmask the shared secret.
  uint32_t dest_share0[shared_secret_words];
  uint32_t dest_share1[shared_secret_words];
  otcrypto_word32_buf_t share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, dest_share0, ARRAYSIZE(dest_share0));
  otcrypto_word32_buf_t share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, dest_share1, ARRAYSIZE(dest_share1));
  TRY(otcrypto_export_blinded_key(&shared_secret, &share0_buf, &share1_buf));
  TRY(hardened_xor(dest_share0, dest_share1, shared_secret_words, ss));
  return OK_STATUS();
}

status_t handle_ecdh(ujson_t *uj) {
  // Declare ECDH parameter ujson deserializer types
  cryptotest_ecdh_curve_t uj_curve;
  cryptotest_ecdh_private_key_t uj_private_key;
  cryptotest_ecdh_coordinate_t uj_qx;
  cryptotest_ecdh_coordinate_t uj_qy;

  // Deserialize ujson byte stream into ECDH parameters
  TRY(ujson_deserialize_cryptotest_ecdh_curve_t(uj, &uj_curve));
  TRY(ujson_deserialize_cryptotest_ecdh_private_key_t(uj, &uj_private_key));
  TRY(ujson_deserialize_cryptotest_ecdh_coordinate_t(uj, &uj_qx));
  TRY(ujson_deserialize_cryptotest_ecdh_coordinate_t(uj, &uj_qy));

  cryptotest_ecdh_derive_output_t uj_output;
  bool valid;
  switch (uj_curve) {
    case kCryptotestEcdhCurveP256: {
      uint32_t shared_secret_words[kP256SharedSecretBytes / sizeof(uint32_t)];
      TRY(ecdh_p256(uj_private_key, uj_qx, uj_qy, shared_secret_words, &valid));
      memcpy(uj_output.shared_secret, shared_secret_words,
             kP256SharedSecretBytes);
      uj_output.shared_secret_len = kP256SharedSecretBytes;
      break;
    }
    case kCryptotestEcdhCurveP384: {
      uint32_t shared_secret_words[kP384SharedSecretBytes / sizeof(uint32_t)];
      TRY(ecdh_p384(uj_private_key, uj_qx, uj_qy, shared_secret_words, &valid));
      memcpy(uj_output.shared_secret, shared_secret_words,
             kP384SharedSecretBytes);
      uj_output.shared_secret_len = kP384SharedSecretBytes;
      break;
    }
    default:
      LOG_ERROR("Unsupported ECC curve: %d", uj_curve);
      return INVALID_ARGUMENT();
  }
  uj_output.ok = (uint8_t)valid;

  RESP_OK(ujson_serialize_cryptotest_ecdh_derive_output_t, uj, &uj_output);
  return OK_STATUS(0);
}
