// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/ecc/p256.h"
#include "sw/device/lib/crypto/impl/ecc/p384.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/ecdh_commands.h"

static const int P256_KEY_BYTES = 32;
static const int P384_KEY_BYTES = 48;

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

  otcrypto_ecc_curve_type_t curve_type;
  otcrypto_unblinded_key_t public_key;
  p256_point_t pub_p256;
  p384_point_t pub_p384;
  p256_masked_scalar_t private_key_masked_p256;
  p384_masked_scalar_t private_key_masked_p384;

  otcrypto_key_config_t key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdh,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  size_t shared_key_words;
  uint32_t *private_key_masked_raw;
  uint32_t private_keyblob_length;
  switch (uj_curve) {
    case kCryptotestEcdhCurveP256: {
      curve_type = kOtcryptoEccCurveTypeNistP256;
      memset(pub_p256.x, 0, kP256CoordWords * 4);
      memcpy(pub_p256.x, uj_qx.coordinate, uj_qx.coordinate_len);
      memset(pub_p256.y, 0, kP256CoordWords * 4);
      memcpy(pub_p256.y, uj_qy.coordinate, uj_qy.coordinate_len);
      public_key.key_mode = kOtcryptoKeyModeEcdh;
      public_key.key_length = sizeof(p256_point_t);
      public_key.key = (uint32_t *)&pub_p256;
      key_config.key_length = P256_KEY_BYTES;
      shared_key_words = P256_KEY_BYTES / sizeof(uint32_t);
      memset(private_key_masked_p256.share0, 0, kP256MaskedScalarShareBytes);
      memcpy(private_key_masked_p256.share0, uj_private_key.d0,
             kP256ScalarBytes);
      memset(private_key_masked_p256.share1, 0, kP256MaskedScalarShareBytes);
      memcpy(private_key_masked_p256.share1, uj_private_key.d1,
             kP256ScalarBytes);
      private_key_masked_raw = (uint32_t *)&private_key_masked_p256;
      private_keyblob_length = sizeof(private_key_masked_p256);
      break;
    }
    case kCryptotestEcdhCurveP384: {
      curve_type = kOtcryptoEccCurveTypeNistP384;
      memset(pub_p384.x, 0, kP384CoordWords * 4);
      memcpy(pub_p384.x, uj_qx.coordinate, uj_qx.coordinate_len);
      memset(pub_p384.y, 0, kP384CoordWords * 4);
      memcpy(pub_p384.y, uj_qy.coordinate, uj_qy.coordinate_len);
      public_key.key_mode = kOtcryptoKeyModeEcdh;
      public_key.key_length = sizeof(p384_point_t);
      public_key.key = (uint32_t *)&pub_p384;
      key_config.key_length = P384_KEY_BYTES;
      shared_key_words = P384_KEY_BYTES / sizeof(uint32_t);
      memset(private_key_masked_p384.share0, 0, kP384MaskedScalarShareBytes);
      memcpy(private_key_masked_p384.share0, uj_private_key.d0,
             kP384ScalarBytes);
      memset(private_key_masked_p384.share1, 0, kP384MaskedScalarShareBytes);
      memcpy(private_key_masked_p384.share1, uj_private_key.d1,
             kP384ScalarBytes);
      private_key_masked_raw = (uint32_t *)&private_key_masked_p384;
      private_keyblob_length = sizeof(private_key_masked_p384);
      break;
    }
    default:
      LOG_ERROR("Unsupported ECC curve: %d", uj_curve);
      return INVALID_ARGUMENT();
  }
  public_key.checksum = integrity_unblinded_checksum(&public_key);

  otcrypto_ecc_curve_t elliptic_curve = {
      .curve_type = curve_type,
      // NULL because we use a named curve
      .domain_parameter = NULL,
  };
  otcrypto_blinded_key_t private_key = {
      .config = key_config,
      .keyblob_length = private_keyblob_length,
      .keyblob = private_key_masked_raw,
  };
  private_key.checksum = integrity_blinded_checksum(&private_key);

  // Create keyblob for shared key
  uint32_t shared_keyblob[keyblob_num_words(key_config)];
  otcrypto_blinded_key_t shared_key = {
      .config = key_config,
      .keyblob_length = sizeof(shared_keyblob),
      .keyblob = shared_keyblob,
  };

  otcrypto_status_t status =
      otcrypto_ecdh(&private_key, &public_key, &elliptic_curve, &shared_key);
  cryptotest_ecdh_derive_output_t uj_output;
  switch (status.value) {
    case kOtcryptoStatusValueOk: {
      uj_output.ok = true;

      // Recover the shared secret key (Z) from its shares
      uint32_t *zShare0;
      uint32_t *zShare1;
      TRY(keyblob_to_shares(&shared_key, &zShare0, &zShare1));

      // XOR the two shares to get the raw key
      uint32_t *uj_shared_secret_u32 = (uint32_t *)uj_output.shared_secret;
      for (size_t i = 0; i < shared_key_words; i++) {
        uj_shared_secret_u32[i] = zShare0[i] ^ zShare1[i];
      }
      uj_output.shared_secret_len = shared_key_words * sizeof(uint32_t);

      break;
    }
    case kOtcryptoStatusValueBadArgs: {
      // Some ECDH test vectors test invalid inputs. If cryptolib
      // returns an invalid input code, we simply respond with ok =
      // false. For other error codes, we error out entirely.
      uj_output.ok = false;
      break;
    }
    default: {
      LOG_ERROR(
          "Unexpected status value returned from otcrypto_ecdh: "
          "0x%x",
          status.value);
      return INTERNAL();
    }
  }
  RESP_OK(ujson_serialize_cryptotest_ecdh_derive_output_t, uj, &uj_output);
  return OK_STATUS(0);
}
