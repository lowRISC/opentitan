// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc.h"
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
   * Bytes in a P-256 public key coordinate.
   */
  kP256CoordinateBytes = 32,
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
   * Bytes in a P-384 public key coordinate.
   */
  kP384CoordinateBytes = 48,
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
 * @param d Private key.
 * @param qx Public key x coordinate.
 * @param qx Public key y coordinate.
 * @param[out] ss Shared secret key.
 * @return Status code (OK or error).
 */
static status_t ecdh_p256(cryptotest_ecdh_private_key_t d,
                          cryptotest_ecdh_coordinate_t qx,
                          cryptotest_ecdh_coordinate_t qy, uint32_t *ss) {
  if (qx.coordinate_len != kP256CoordinateBytes ||
      qy.coordinate_len != kP256CoordinateBytes) {
    LOG_ERROR(
        "Bad P-256 coordinate length (should both be %d): (x = %d, y = %d)",
        kP256CoordinateBytes, qx.coordinate_len, qy.coordinate_len);
    return INVALID_ARGUMENT();
  }

  // Construct the private key object.
  // TODO(#20762): once key-import exists for ECDH, use that instead.
  uint32_t private_keyblob[(kP256MaskedPrivateKeyBytes / sizeof(uint32_t)) * 2];
  memset(private_keyblob, 0, sizeof(private_keyblob));
  otcrypto_blinded_key_t private_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeEcdhP256,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(private_keyblob),
      .keyblob = private_keyblob,
      .checksum = 0,
  };

  // Construct the public key object.
  // TODO(#20762): once key-import exists for ECDH, use that instead.
  uint32_t public_key_buf[(kP256CoordinateBytes * 2) / sizeof(uint32_t)];
  memset(public_key_buf, 0, sizeof(public_key_buf));
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP256,
      .key_length = sizeof(public_key_buf),
      .key = public_key_buf,
  };

  // Create a destination for the shared secret.
  size_t shared_secret_words = kP256SharedSecretBytes / sizeof(uint32_t);
  uint32_t shared_secretblob[shared_secret_words * 2];
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

  TRY(otcrypto_ecdh_p256(&private_key, &public_key, &shared_secret));

  // Unmask the shared secret.
  uint32_t share0[shared_secret_words];
  uint32_t share1[shared_secret_words];
  TRY(otcrypto_export_blinded_key(
      shared_secret,
      (otcrypto_word32_buf_t){.data = share0, .len = ARRAYSIZE(share0)},
      (otcrypto_word32_buf_t){.data = share1, .len = ARRAYSIZE(share1)}));
  for (size_t i = 0; i < shared_secret_words; i++) {
    ss[i] = share0[i] ^ share1[i];
  }
  return OK_STATUS();
}

/**
 * Run ECDH with curve P-384.
 *
 * The caller should ensure at least kP384SharedSecretBytes of space are
 * allocated at `ss`.
 *
 * @param d Private key.
 * @param qx Public key x coordinate.
 * @param qx Public key y coordinate.
 * @param[out] ss Shared secret key.
 * @return Status code (OK or error).
 */
static status_t ecdh_p384(cryptotest_ecdh_private_key_t d,
                          cryptotest_ecdh_coordinate_t qx,
                          cryptotest_ecdh_coordinate_t qy, uint32_t *ss) {
  if (qx.coordinate_len != kP384CoordinateBytes ||
      qy.coordinate_len != kP384CoordinateBytes) {
    LOG_ERROR(
        "Bad P-384 coordinate length (should both be %d): (x = %d, y = %d)",
        kP384CoordinateBytes, qx.coordinate_len, qy.coordinate_len);
    return INVALID_ARGUMENT();
  }

  // Construct the private key object.
  // TODO(#20762): once key-import exists for ECDH, use that instead.
  uint32_t private_keyblob[(kP384MaskedPrivateKeyBytes / sizeof(uint32_t)) * 2];
  memset(private_keyblob, 0, sizeof(private_keyblob));
  otcrypto_blinded_key_t private_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeEcdhP384,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(private_keyblob),
      .keyblob = private_keyblob,
      .checksum = 0,
  };

  // Construct the public key object.
  // TODO(#20762): once key-import exists for ECDH, use that instead.
  uint32_t public_key_buf[(kP384CoordinateBytes * 2) / sizeof(uint32_t)];
  memset(public_key_buf, 0, sizeof(public_key_buf));
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = sizeof(public_key_buf),
      .key = public_key_buf,
  };

  // Create a destination for the shared secret.
  size_t shared_secret_words = kP384SharedSecretBytes / sizeof(uint32_t);
  uint32_t shared_secretblob[shared_secret_words * 2];
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

  TRY(otcrypto_ecdh_p384(&private_key, &public_key, &shared_secret));

  // Unmask the shared secret.
  uint32_t share0[shared_secret_words];
  uint32_t share1[shared_secret_words];
  TRY(otcrypto_export_blinded_key(
      shared_secret,
      (otcrypto_word32_buf_t){.data = share0, .len = ARRAYSIZE(share0)},
      (otcrypto_word32_buf_t){.data = share1, .len = ARRAYSIZE(share1)}));
  for (size_t i = 0; i < shared_secret_words; i++) {
    ss[i] = share0[i] ^ share1[i];
  }
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
  switch (uj_curve) {
    case kCryptotestEcdhCurveP256: {
      uint32_t shared_secret_words[kP256SharedSecretBytes / sizeof(uint32_t)];
      TRY(ecdh_p256(uj_private_key, uj_qx, uj_qy, shared_secret_words));
      memcpy(uj_output.shared_secret, shared_secret_words,
             kP256SharedSecretBytes);
      uj_output.shared_secret_len = kP256SharedSecretBytes;
      break;
    }
    case kCryptotestEcdhCurveP384: {
      uint32_t shared_secret_words[kP384SharedSecretBytes / sizeof(uint32_t)];
      TRY(ecdh_p384(uj_private_key, uj_qx, uj_qy, shared_secret_words));
      memcpy(uj_output.shared_secret, shared_secret_words,
             kP384SharedSecretBytes);
      uj_output.shared_secret_len = kP384SharedSecretBytes;
      break;
    }
    default:
      LOG_ERROR("Unsupported ECC curve: %d", uj_curve);
      return INVALID_ARGUMENT();
  }

  RESP_OK(ujson_serialize_cryptotest_ecdh_derive_output_t, uj, &uj_output);
  return OK_STATUS(0);
}
