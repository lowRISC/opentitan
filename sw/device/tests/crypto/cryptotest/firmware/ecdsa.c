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
#include "sw/device/tests/crypto/cryptotest/json/ecdsa_commands.h"

// Copied from //sw/device/tests/crypto/ecdsa_p256_functest.c
enum {
  /* Number of bytes in a P-256 private key. */
  kP256PrivateKeyBytes = 256 / 8,
  /* Number of bytes in a P-384 private key. */
  kP384PrivateKeyBytes = 384 / 8,
};

static const otcrypto_key_config_t kP256PrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsa,
    .key_length = kP256PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const otcrypto_key_config_t kP384PrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsa,
    .key_length = kP384PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

int set_nist_p256_params(
    cryptotest_ecdsa_coordinate_t uj_qx, cryptotest_ecdsa_coordinate_t uj_qy,
    cryptotest_ecdsa_signature_t uj_signature,
    otcrypto_ecc_curve_type_t *curve_type, otcrypto_unblinded_key_t *public_key,
    p256_ecdsa_signature_t *signature_p256, p256_point_t *pub_p256,
    otcrypto_word32_buf_t *signature_mut, size_t *digest_len) {
  *curve_type = kOtcryptoEccCurveTypeNistP256;
  if (uj_qx.coordinate_len > kP256CoordBytes) {
    LOG_ERROR(
        "Coordinate value qx too large for P256 (have = %d bytes, max = %d "
        "bytes)",
        uj_qx.coordinate_len, kP256CoordBytes);
    return false;
  }
  if (uj_qy.coordinate_len > kP256CoordBytes) {
    LOG_ERROR(
        "Coordinate value qy too large for P256 (have = %d bytes, max = %d "
        "bytes)",
        uj_qy.coordinate_len, kP256CoordBytes);
    return false;
  }
  memset(pub_p256->x, 0, kP256CoordBytes);
  memcpy(pub_p256->x, uj_qx.coordinate, uj_qx.coordinate_len);
  memset(pub_p256->y, 0, kP256CoordBytes);
  memcpy(pub_p256->y, uj_qy.coordinate, uj_qy.coordinate_len);
  public_key->key_mode = kOtcryptoKeyModeEcdsa;
  public_key->key_length = sizeof(p256_point_t);
  public_key->key = (uint32_t *)pub_p256;
  *digest_len = kP256ScalarWords;
  if (uj_signature.r_len > kP256ScalarBytes) {
    LOG_ERROR(
        "Signature r value too large for P256 (have = %d bytes, max = %d "
        "bytes)",
        uj_signature.r_len, kP256ScalarBytes);
    return false;
  }
  if (uj_signature.s_len > kP256ScalarBytes) {
    LOG_ERROR(
        "Signature s value too large for P256 (have = %d bytes, max = %d "
        "bytes)",
        uj_signature.s_len, kP256ScalarBytes);
    return false;
  }
  memset(signature_p256->r, 0, kP256ScalarBytes);
  memcpy(signature_p256->r, uj_signature.r, uj_signature.r_len);
  memset(signature_p256->s, 0, kP256ScalarBytes);
  memcpy(signature_p256->s, uj_signature.s, uj_signature.s_len);
  signature_mut->len = kP256ScalarWords * 2;
  signature_mut->data = (uint32_t *)signature_p256;

  return true;
}

int set_nist_p384_params(
    cryptotest_ecdsa_coordinate_t uj_qx, cryptotest_ecdsa_coordinate_t uj_qy,
    cryptotest_ecdsa_signature_t uj_signature,
    otcrypto_ecc_curve_type_t *curve_type, otcrypto_unblinded_key_t *public_key,
    p384_ecdsa_signature_t *signature_p384, p384_point_t *pub_p384,
    otcrypto_word32_buf_t *signature_mut, size_t *digest_len) {
  *curve_type = kOtcryptoEccCurveTypeNistP384;
  if (uj_qx.coordinate_len > kP384CoordBytes) {
    LOG_ERROR(
        "Coordinate value qx too large for P384 (have = %d bytes, max = %d "
        "bytes)",
        uj_qx.coordinate_len, kP384CoordBytes);
    return false;
  }
  if (uj_qy.coordinate_len > kP384CoordBytes) {
    LOG_ERROR(
        "Coordinate value qy too large for P384 (have = %d bytes, max = %d "
        "bytes)",
        uj_qy.coordinate_len, kP384CoordBytes);
    return false;
  }
  memset(pub_p384->x, 0, kP384CoordBytes);
  memcpy(pub_p384->x, uj_qx.coordinate, uj_qx.coordinate_len);
  memset(pub_p384->y, 0, kP384CoordBytes);
  memcpy(pub_p384->y, uj_qy.coordinate, uj_qy.coordinate_len);
  public_key->key_mode = kOtcryptoKeyModeEcdsa;
  public_key->key_length = sizeof(p384_point_t);
  public_key->key = (uint32_t *)pub_p384;
  *digest_len = kP384ScalarWords;
  if (uj_signature.r_len > kP384ScalarBytes) {
    LOG_ERROR(
        "Signature r value too large for P384 (have = %d bytes, max = %d "
        "bytes)",
        uj_signature.r_len, kP384ScalarBytes);
    return false;
  }
  if (uj_signature.s_len > kP384ScalarBytes) {
    LOG_ERROR(
        "Signature s value too large for P384 (have = %d bytes, max = %d "
        "bytes)",
        uj_signature.s_len, kP384ScalarBytes);
    return false;
  }
  memset(signature_p384->r, 0, kP384ScalarBytes);
  memcpy(signature_p384->r, uj_signature.r, uj_signature.r_len);
  memset(signature_p384->s, 0, kP384ScalarBytes);
  memcpy(signature_p384->s, uj_signature.s, uj_signature.s_len);
  signature_mut->len = kP384ScalarWords * 2;
  signature_mut->data = (uint32_t *)signature_p384;

  return true;
}

status_t interpret_verification_result(ujson_t *uj,
                                       hardened_bool_t *verification_result) {
  cryptotest_ecdsa_verify_output_t uj_output;
  switch (*verification_result) {
    case kHardenedBoolFalse:
      uj_output = kCryptotestEcdsaVerifyOutputFailure;
      break;
    case kHardenedBoolTrue:
      uj_output = kCryptotestEcdsaVerifyOutputSuccess;
      break;
    default:
      LOG_ERROR("Unexpected result value from otcrypto_ecdsa_verify: %d",
                verification_result);
      return INTERNAL();
  }
  RESP_OK(ujson_serialize_cryptotest_ecdsa_verify_output_t, uj, &uj_output);
  return OK_STATUS(0);
}

status_t interpret_verify_status(ujson_t *uj, otcrypto_status_t status,
                                 hardened_bool_t *verification_result) {
  cryptotest_ecdsa_verify_output_t uj_output;
  switch (status.value) {
    case kOtcryptoStatusValueOk:
      return interpret_verification_result(uj, verification_result);
    case kOtcryptoStatusValueBadArgs:
      // Some ECDSA test vectors test invalid inputs. If cryptolib
      // returns an invalid input code, we simply respond with
      // "validation failed". Otherwise, we error out.
      uj_output = kCryptotestEcdsaVerifyOutputFailure;
      RESP_OK(ujson_serialize_cryptotest_ecdsa_verify_output_t, uj, &uj_output);
      return OK_STATUS(0);
    default:
      LOG_ERROR(
          "Unexpected status value returned from otcrypto_ecdsa_verify: "
          "0x%x",
          status.value);
      return INTERNAL();
  }
}

status_t p256_sign(ujson_t *uj, cryptotest_ecdsa_private_key_t *uj_private_key,
                   otcrypto_ecc_curve_t elliptic_curve,
                   otcrypto_hash_digest_t message_digest,
                   otcrypto_word32_buf_t signature_mut,
                   cryptotest_ecdsa_signature_t *uj_signature) {
  p256_masked_scalar_t private_key_masked;
  otcrypto_blinded_key_t private_key = {
      .config = kP256PrivateKeyConfig,
      .keyblob_length = sizeof(private_key_masked),
      .keyblob = (uint32_t *)&private_key_masked,
  };
  memset(private_key_masked.share0, 0, kP256MaskedScalarShareBytes);
  memcpy(private_key_masked.share0, uj_private_key->d0, kP256ScalarBytes);
  memset(private_key_masked.share1, 0, kP256MaskedScalarShareBytes);
  memcpy(private_key_masked.share1, uj_private_key->d1, kP256ScalarBytes);
  private_key.checksum = integrity_blinded_checksum(&private_key);

  otcrypto_status_t status = otcrypto_ecdsa_sign(
      &private_key, message_digest, &elliptic_curve, signature_mut);
  if (status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(status.value);
  }

  memset(uj_signature->r, 0, ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES);
  memset(uj_signature->s, 0, ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES);
  p256_ecdsa_signature_t *signature_p256 =
      (p256_ecdsa_signature_t *)signature_mut.data;
  memcpy(uj_signature->r, signature_p256->r, kP256ScalarBytes);
  uj_signature->r_len = kP256ScalarBytes;
  memcpy(uj_signature->s, signature_p256->s, kP256ScalarBytes);
  uj_signature->s_len = kP256ScalarBytes;
  RESP_OK(ujson_serialize_cryptotest_ecdsa_signature_t, uj, uj_signature);

  return OK_STATUS(0);
}

status_t p384_sign(ujson_t *uj, cryptotest_ecdsa_private_key_t *uj_private_key,
                   otcrypto_ecc_curve_t elliptic_curve,
                   otcrypto_hash_digest_t message_digest,
                   otcrypto_word32_buf_t signature_mut,
                   cryptotest_ecdsa_signature_t *uj_signature) {
  p384_masked_scalar_t private_key_masked;
  otcrypto_blinded_key_t private_key = {
      .config = kP384PrivateKeyConfig,
      .keyblob_length = sizeof(private_key_masked),
      .keyblob = (uint32_t *)&private_key_masked,
  };
  memset(private_key_masked.share0, 0, kP384MaskedScalarShareBytes);
  memcpy(private_key_masked.share0, uj_private_key->d0, kP384ScalarBytes);
  memset(private_key_masked.share1, 0, kP384MaskedScalarShareBytes);
  memcpy(private_key_masked.share1, uj_private_key->d1, kP384ScalarBytes);
  private_key.checksum = integrity_blinded_checksum(&private_key);

  otcrypto_status_t status = otcrypto_ecdsa_sign(
      &private_key, message_digest, &elliptic_curve, signature_mut);
  if (status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(status.value);
  }

  memset(uj_signature->r, 0, ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES);
  memset(uj_signature->s, 0, ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES);
  p384_ecdsa_signature_t *signature_p384 =
      (p384_ecdsa_signature_t *)signature_mut.data;
  memcpy(uj_signature->r, signature_p384->r, kP384ScalarBytes);
  uj_signature->r_len = kP384ScalarBytes;
  memcpy(uj_signature->s, signature_p384->s, kP384ScalarBytes);
  uj_signature->s_len = kP384ScalarBytes;
  RESP_OK(ujson_serialize_cryptotest_ecdsa_signature_t, uj, uj_signature);

  return OK_STATUS(0);
}

status_t handle_ecdsa(ujson_t *uj) {
  // Declare ECDSA parameter ujson deserializer types
  cryptotest_ecdsa_operation_t uj_op;
  cryptotest_ecdsa_hash_alg_t uj_hash_alg;
  cryptotest_ecdsa_curve_t uj_curve;
  cryptotest_ecdsa_message_t uj_message;
  cryptotest_ecdsa_signature_t uj_signature;
  cryptotest_ecdsa_coordinate_t uj_qx;
  cryptotest_ecdsa_coordinate_t uj_qy;
  cryptotest_ecdsa_private_key_t uj_private_key;

  // Deserialize ujson byte stream into ECDSA parameters
  TRY(ujson_deserialize_cryptotest_ecdsa_operation_t(uj, &uj_op));
  TRY(ujson_deserialize_cryptotest_ecdsa_hash_alg_t(uj, &uj_hash_alg));
  TRY(ujson_deserialize_cryptotest_ecdsa_curve_t(uj, &uj_curve));
  TRY(ujson_deserialize_cryptotest_ecdsa_message_t(uj, &uj_message));
  TRY(ujson_deserialize_cryptotest_ecdsa_signature_t(uj, &uj_signature));
  TRY(ujson_deserialize_cryptotest_ecdsa_coordinate_t(uj, &uj_qx));
  TRY(ujson_deserialize_cryptotest_ecdsa_coordinate_t(uj, &uj_qy));
  TRY(ujson_deserialize_cryptotest_ecdsa_private_key_t(uj, &uj_private_key));

  otcrypto_ecc_curve_type_t curve_type;
  otcrypto_unblinded_key_t public_key;
  size_t digest_len;

  otcrypto_word32_buf_t signature_mut;
  int success;
  p256_ecdsa_signature_t signature_p256;
  p384_ecdsa_signature_t signature_p384;
  p256_point_t pub_p256;
  p384_point_t pub_p384;
  switch (uj_curve) {
    case kCryptotestEcdsaCurveP256:
      success = set_nist_p256_params(uj_qx, uj_qy, uj_signature, &curve_type,
                                     &public_key, &signature_p256, &pub_p256,
                                     &signature_mut, &digest_len);
      if (!success) {
        return INVALID_ARGUMENT();
      }
      break;
    case kCryptotestEcdsaCurveP384:
      success = set_nist_p384_params(uj_qx, uj_qy, uj_signature, &curve_type,
                                     &public_key, &signature_p384, &pub_p384,
                                     &signature_mut, &digest_len);
      if (!success) {
        return INVALID_ARGUMENT();
      }
      break;
    default:
      LOG_ERROR("Unsupported ECC curve: %d", uj_curve);
      return INVALID_ARGUMENT();
  }
  public_key.checksum = integrity_unblinded_checksum(&public_key);
  otcrypto_const_word32_buf_t signature = {
      .len = signature_mut.len,
      .data = signature_mut.data,
  };

  otcrypto_ecc_curve_t elliptic_curve = {
      .curve_type = curve_type,
      // NULL because we use a named curve
      .domain_parameter = NULL,
  };
  otcrypto_hash_mode_t mode;
  switch (uj_hash_alg) {
    case kCryptotestEcdsaHashAlgSha256:
      mode = kOtcryptoHashModeSha256;
      break;
    case kCryptotestEcdsaHashAlgSha384:
      mode = kOtcryptoHashModeSha384;
      break;
    case kCryptotestEcdsaHashAlgSha512:
      mode = kOtcryptoHashModeSha512;
      break;
    case kCryptotestEcdsaHashAlgSha3_256:
      mode = kOtcryptoHashModeSha3_256;
      break;
    case kCryptotestEcdsaHashAlgSha3_384:
      mode = kOtcryptoHashModeSha3_384;
      break;
    case kCryptotestEcdsaHashAlgSha3_512:
      mode = kOtcryptoHashModeSha3_512;
      break;
    default:
      LOG_ERROR("Unrecognized ECDSA hash mode: %d", uj_hash_alg);
      return INVALID_ARGUMENT();
  }
  uint8_t message_buf[ECDSA_CMD_MAX_MESSAGE_BYTES];
  memset(message_buf, 0, digest_len * sizeof(uint32_t));
  memcpy(message_buf, uj_message.input, uj_message.input_len);
  const otcrypto_hash_digest_t message_digest = {
      .mode = mode,
      .len = digest_len,
      .data = (uint32_t *)message_buf,
  };

  switch (uj_op) {
    case kCryptotestEcdsaOperationSign: {
      switch (uj_curve) {
        case kCryptotestEcdsaCurveP256: {
          return p256_sign(uj, &uj_private_key, elliptic_curve, message_digest,
                           signature_mut, &uj_signature);
        }
        case kCryptotestEcdsaCurveP384: {
          return p384_sign(uj, &uj_private_key, elliptic_curve, message_digest,
                           signature_mut, &uj_signature);
        }
        default:
          LOG_ERROR("Unsupported ECC curve: %d", uj_curve);
          return INVALID_ARGUMENT();
      }
      break;
    }
    case kCryptotestEcdsaOperationVerify: {
      hardened_bool_t verification_result = kHardenedBoolFalse;
      return interpret_verify_status(
          uj,
          otcrypto_ecdsa_verify(&public_key, message_digest, signature,
                                &elliptic_curve, &verification_result),
          &verification_result);
    }
    default:
      LOG_ERROR("Unrecognized ECDSA operation: %d", uj_op);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}
