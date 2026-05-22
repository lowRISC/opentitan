// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/crypto/include/sha3.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/ecdsa_commands.h"

// Copied from internal headers to remove dependencies
enum {
  kP256PrivateKeyBytes = 256 / 8,
  kP384PrivateKeyBytes = 384 / 8,

  kP256CoordBytes = 32,
  kP256CoordWords = 32 / 4,
  kP256ScalarBytes = 32,
  kP256ScalarWords = 32 / 4,
  kP256MaskedScalarShareBytes = 40,
  kP256MaskedScalarShareWords = 40 / 4,
  kP256MaskedScalarTotalShareBytes = 80,

  kP384CoordBytes = 48,
  kP384CoordWords = 48 / 4,
  kP384ScalarBytes = 48,
  kP384ScalarWords = 48 / 4,
  kP384MaskedScalarShareBytes = 56,
  kP384MaskedScalarShareWords = 56 / 4,
  kP384MaskedScalarTotalShareBytes = 112,
};

static const otcrypto_key_config_t kP256PrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP256,
    .key_length = kP256PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const otcrypto_key_config_t kP384PrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP384,
    .key_length = kP384PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// P-256 group order n in little-endian uint32_t limbs.
static const uint32_t kP256OrderLE[kP256ScalarWords] = {
    0xFC632551, 0xF3B9CAC2, 0xA7179E84, 0xBCE6FAAD,
    0xFFFFFFFF, 0xFFFFFFFF, 0x00000000, 0xFFFFFFFF,
};

// P-384 group order n in little-endian uint32_t limbs.
static const uint32_t kP384OrderLE[kP384ScalarWords] = {
    0xCCC52973, 0xECEC196A, 0x48B0A77A, 0x581A0DB2, 0xF4372DDF, 0xC7634D81,
    0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF,
};

static const otcrypto_key_config_t kP256ExportableKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP256,
    .key_length = kP256PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolTrue,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const otcrypto_key_config_t kP384ExportableKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP384,
    .key_length = kP384PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolTrue,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

int set_nist_p256_params(cryptotest_ecdsa_coordinate_t uj_qx,
                         cryptotest_ecdsa_coordinate_t uj_qy,
                         cryptotest_ecdsa_signature_t uj_signature,
                         otcrypto_unblinded_key_t *public_key,
                         uint32_t *signature_p256, uint32_t *pub_p256,
                         otcrypto_word32_buf_t *signature_mut,
                         size_t *digest_len) {
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

  uint32_t x[kP256CoordWords] = {0};
  uint32_t y[kP256CoordWords] = {0};
  memcpy(x, uj_qx.coordinate, uj_qx.coordinate_len);
  memcpy(y, uj_qy.coordinate, uj_qy.coordinate_len);

  public_key->key_mode = kOtcryptoKeyModeEcdsaP256;
  public_key->key_length = kP256CoordBytes * 2;
  public_key->key = pub_p256;

  otcrypto_const_word32_buf_t x_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, x, kP256CoordWords);
  otcrypto_const_word32_buf_t y_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, y, kP256CoordWords);
  otcrypto_ecc_p256_public_key_import(x_buf, y_buf, public_key);

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

  memset(signature_p256, 0, kP256ScalarBytes * 2);
  memcpy((uint8_t *)signature_p256, uj_signature.r, uj_signature.r_len);
  memcpy((uint8_t *)signature_p256 + kP256ScalarBytes, uj_signature.s,
         uj_signature.s_len);
  *signature_mut = OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, signature_p256,
                                     kP256ScalarWords * 2);

  return true;
}

int set_nist_p384_params(cryptotest_ecdsa_coordinate_t uj_qx,
                         cryptotest_ecdsa_coordinate_t uj_qy,
                         cryptotest_ecdsa_signature_t uj_signature,
                         otcrypto_unblinded_key_t *public_key,
                         uint32_t *signature_p384, uint32_t *pub_p384,
                         otcrypto_word32_buf_t *signature_mut,
                         size_t *digest_len) {
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

  uint32_t x[kP384CoordWords] = {0};
  uint32_t y[kP384CoordWords] = {0};
  memcpy(x, uj_qx.coordinate, uj_qx.coordinate_len);
  memcpy(y, uj_qy.coordinate, uj_qy.coordinate_len);

  public_key->key_mode = kOtcryptoKeyModeEcdsaP384;
  public_key->key_length = kP384CoordBytes * 2;
  public_key->key = pub_p384;

  otcrypto_const_word32_buf_t x_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, x, kP384CoordWords);
  otcrypto_const_word32_buf_t y_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, y, kP384CoordWords);
  otcrypto_ecc_p384_public_key_import(x_buf, y_buf, public_key);

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

  memset(signature_p384, 0, kP384ScalarBytes * 2);
  memcpy((uint8_t *)signature_p384, uj_signature.r, uj_signature.r_len);
  memcpy((uint8_t *)signature_p384 + kP384ScalarBytes, uj_signature.s,
         uj_signature.s_len);
  *signature_mut = OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, signature_p384,
                                     kP384ScalarWords * 2);

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
                   otcrypto_unblinded_key_t *public_key,
                   otcrypto_hash_digest_t message_digest,
                   otcrypto_word32_buf_t signature_mut,
                   cryptotest_ecdsa_signature_t *uj_signature) {
  uint32_t share0[kP256MaskedScalarShareWords] = {0};
  uint32_t share1[kP256MaskedScalarShareWords] = {0};
  memcpy(share0, uj_private_key->d0, uj_private_key->d0_len);
  memcpy(share1, uj_private_key->d1, uj_private_key->d1_len);

  otcrypto_const_word32_buf_t share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share0, kP256MaskedScalarShareWords);
  otcrypto_const_word32_buf_t share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1, kP256MaskedScalarShareWords);

  uint32_t keyblob[kP256MaskedScalarTotalShareBytes / sizeof(uint32_t)];
  otcrypto_blinded_key_t private_key = {
      .config = kP256PrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  otcrypto_status_t import_status = otcrypto_ecc_p256_private_key_import(
      share0_buf, share1_buf, &private_key);
  if (import_status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(import_status.value);
  }

  otcrypto_status_t status = otcrypto_ecdsa_p256_sign_verify(
      &private_key, public_key, message_digest, &signature_mut);
  if (status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(status.value);
  }

  memset(uj_signature->r, 0, ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES);
  memset(uj_signature->s, 0, ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES);

  uint8_t *sig_bytes = (uint8_t *)signature_mut.data;
  memcpy(uj_signature->r, sig_bytes, kP256ScalarBytes);
  uj_signature->r_len = kP256ScalarBytes;
  memcpy(uj_signature->s, sig_bytes + kP256ScalarBytes, kP256ScalarBytes);
  uj_signature->s_len = kP256ScalarBytes;
  RESP_OK(ujson_serialize_cryptotest_ecdsa_signature_t, uj, uj_signature);

  return OK_STATUS(0);
}

status_t p384_sign(ujson_t *uj, cryptotest_ecdsa_private_key_t *uj_private_key,
                   otcrypto_unblinded_key_t *public_key,
                   otcrypto_hash_digest_t message_digest,
                   otcrypto_word32_buf_t signature_mut,
                   cryptotest_ecdsa_signature_t *uj_signature) {
  uint32_t share0[kP384MaskedScalarShareWords] = {0};
  uint32_t share1[kP384MaskedScalarShareWords] = {0};
  memcpy(share0, uj_private_key->d0, uj_private_key->d0_len);
  memcpy(share1, uj_private_key->d1, uj_private_key->d1_len);

  otcrypto_const_word32_buf_t share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share0, kP384MaskedScalarShareWords);
  otcrypto_const_word32_buf_t share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1, kP384MaskedScalarShareWords);

  uint32_t keyblob[kP384MaskedScalarTotalShareBytes / sizeof(uint32_t)];
  otcrypto_blinded_key_t private_key = {
      .config = kP384PrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  otcrypto_status_t import_status = otcrypto_ecc_p384_private_key_import(
      share0_buf, share1_buf, &private_key);
  if (import_status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(import_status.value);
  }

  otcrypto_status_t status = otcrypto_ecdsa_p384_sign_verify(
      &private_key, public_key, message_digest, &signature_mut);
  if (status.value != kOtcryptoStatusValueOk) {
    return INTERNAL(status.value);
  }

  memset(uj_signature->r, 0, ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES);
  memset(uj_signature->s, 0, ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES);

  uint8_t *sig_bytes = (uint8_t *)signature_mut.data;
  memcpy(uj_signature->r, sig_bytes, kP384ScalarBytes);
  uj_signature->r_len = kP384ScalarBytes;
  memcpy(uj_signature->s, sig_bytes + kP384ScalarBytes, kP384ScalarBytes);
  uj_signature->s_len = kP384ScalarBytes;
  RESP_OK(ujson_serialize_cryptotest_ecdsa_signature_t, uj, uj_signature);

  return OK_STATUS(0);
}

static status_t handle_ecdsa_hash(
    ujson_t *uj, cryptotest_ecdsa_hash_alg_t uj_hash_alg,
    const cryptotest_ecdsa_message_t *uj_message) {
  size_t digest_words;
  otcrypto_status_t (*hash_fn)(const otcrypto_const_byte_buf_t *,
                               otcrypto_hash_digest_t *);
  switch (uj_hash_alg) {
    case kCryptotestEcdsaHashAlgSha256:
      digest_words = 256 / 32;
      hash_fn = otcrypto_sha2_256;
      break;
    case kCryptotestEcdsaHashAlgSha384:
      digest_words = 384 / 32;
      hash_fn = otcrypto_sha2_384;
      break;
    case kCryptotestEcdsaHashAlgSha512:
      digest_words = 512 / 32;
      hash_fn = otcrypto_sha2_512;
      break;
    case kCryptotestEcdsaHashAlgSha3_256:
      digest_words = 256 / 32;
      hash_fn = otcrypto_sha3_256;
      break;
    case kCryptotestEcdsaHashAlgSha3_384:
      digest_words = 384 / 32;
      hash_fn = otcrypto_sha3_384;
      break;
    case kCryptotestEcdsaHashAlgSha3_512:
      digest_words = 512 / 32;
      hash_fn = otcrypto_sha3_512;
      break;
    default:
      LOG_ERROR("Unsupported hash algorithm for ECDSA: %d", uj_hash_alg);
      return INVALID_ARGUMENT();
  }

  uint8_t msg_buf[uj_message->input_len];
  memcpy(msg_buf, uj_message->input, uj_message->input_len);
  const otcrypto_const_byte_buf_t msg = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, msg_buf, uj_message->input_len);

  uint32_t digest_buf[digest_words];
  memset(digest_buf, 0, digest_words * sizeof(uint32_t));
  otcrypto_hash_digest_t digest = {
      .data = digest_buf,
      .len = digest_words,
  };
  otcrypto_status_t status = hash_fn(&msg, &digest);
  if (status.value != kOtcryptoStatusValueOk) {
    LOG_ERROR("Hash operation failed with status 0x%x", status.value);
    return INTERNAL(status.value);
  }

  cryptotest_ecdsa_hash_digest_t uj_digest;
  uj_digest.digest_len = digest_words * sizeof(uint32_t);
  memcpy(uj_digest.digest, digest_buf, uj_digest.digest_len);
  RESP_OK(ujson_serialize_cryptotest_ecdsa_hash_digest_t, uj, &uj_digest);
  return OK_STATUS(0);
}

static status_t handle_ecdsa_keygen(ujson_t *uj,
                                    cryptotest_ecdsa_curve_t uj_curve) {
  cryptotest_ecdsa_keygen_resp_t resp;
  memset(&resp, 0, sizeof(resp));

  if (uj_curve == kCryptotestEcdsaCurveP256) {
    uint32_t keyblob[kP256MaskedScalarTotalShareBytes / sizeof(uint32_t)];
    otcrypto_blinded_key_t priv = {
        .config = kP256ExportableKeyConfig,
        .keyblob_length = sizeof(keyblob),
        .keyblob = keyblob,
    };
    uint32_t pub_buf[kP256CoordWords * 2];
    otcrypto_unblinded_key_t pub = {
        .key_mode = kOtcryptoKeyModeEcdsaP256,
        .key_length = kP256CoordBytes * 2,
        .key = pub_buf,
    };
    otcrypto_status_t status = otcrypto_ecdsa_p256_keygen(&priv, &pub);
    if (status.value != kOtcryptoStatusValueOk) {
      LOG_ERROR("otcrypto_ecdsa_p256_keygen failed: 0x%x", status.value);
      return INTERNAL(status.value);
    }

    uint32_t d0[kP256MaskedScalarShareWords];
    uint32_t d1[kP256MaskedScalarShareWords];
    otcrypto_word32_buf_t d0_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_word32_buf_t, d0, kP256MaskedScalarShareWords);
    otcrypto_word32_buf_t d1_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_word32_buf_t, d1, kP256MaskedScalarShareWords);
    status = otcrypto_ecc_p256_private_key_export(&priv, &d0_buf, &d1_buf);
    if (status.value != kOtcryptoStatusValueOk) {
      LOG_ERROR("otcrypto_ecc_p256_private_key_export failed: 0x%x",
                status.value);
      return INTERNAL(status.value);
    }

    uint32_t qx[kP256CoordWords];
    uint32_t qy[kP256CoordWords];
    otcrypto_word32_buf_t qx_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, qx, kP256CoordWords);
    otcrypto_word32_buf_t qy_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, qy, kP256CoordWords);
    status = otcrypto_ecc_p256_public_key_export(&pub, &qx_buf, &qy_buf);
    if (status.value != kOtcryptoStatusValueOk) {
      LOG_ERROR("otcrypto_ecc_p256_public_key_export failed: 0x%x",
                status.value);
      return INTERNAL(status.value);
    }

    resp.qx_len = kP256CoordBytes;
    memcpy(resp.qx, qx, kP256CoordBytes);
    resp.qy_len = kP256CoordBytes;
    memcpy(resp.qy, qy, kP256CoordBytes);
    resp.d0_len = kP256MaskedScalarShareBytes;
    memcpy(resp.d0, d0, kP256MaskedScalarShareBytes);
    resp.d1_len = kP256MaskedScalarShareBytes;
    memcpy(resp.d1, d1, kP256MaskedScalarShareBytes);
    uint32_t d_scalar[kP256ScalarWords];
    TRY(hardened_add_mod(d0, d1, kP256OrderLE, kP256ScalarWords, d_scalar));
    resp.d_len = kP256ScalarBytes;
    memcpy(resp.d, d_scalar, kP256ScalarBytes);
  } else if (uj_curve == kCryptotestEcdsaCurveP384) {
    uint32_t keyblob[kP384MaskedScalarTotalShareBytes / sizeof(uint32_t)];
    otcrypto_blinded_key_t priv = {
        .config = kP384ExportableKeyConfig,
        .keyblob_length = sizeof(keyblob),
        .keyblob = keyblob,
    };
    uint32_t pub_buf[kP384CoordWords * 2];
    otcrypto_unblinded_key_t pub = {
        .key_mode = kOtcryptoKeyModeEcdsaP384,
        .key_length = kP384CoordBytes * 2,
        .key = pub_buf,
    };
    otcrypto_status_t status = otcrypto_ecdsa_p384_keygen(&priv, &pub);
    if (status.value != kOtcryptoStatusValueOk) {
      LOG_ERROR("otcrypto_ecdsa_p384_keygen failed: 0x%x", status.value);
      return INTERNAL(status.value);
    }

    uint32_t d0[kP384MaskedScalarShareWords];
    uint32_t d1[kP384MaskedScalarShareWords];
    otcrypto_word32_buf_t d0_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_word32_buf_t, d0, kP384MaskedScalarShareWords);
    otcrypto_word32_buf_t d1_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_word32_buf_t, d1, kP384MaskedScalarShareWords);
    status = otcrypto_ecc_p384_private_key_export(&priv, &d0_buf, &d1_buf);
    if (status.value != kOtcryptoStatusValueOk) {
      LOG_ERROR("otcrypto_ecc_p384_private_key_export failed: 0x%x",
                status.value);
      return INTERNAL(status.value);
    }

    uint32_t qx[kP384CoordWords];
    uint32_t qy[kP384CoordWords];
    otcrypto_word32_buf_t qx_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, qx, kP384CoordWords);
    otcrypto_word32_buf_t qy_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, qy, kP384CoordWords);
    status = otcrypto_ecc_p384_public_key_export(&pub, &qx_buf, &qy_buf);
    if (status.value != kOtcryptoStatusValueOk) {
      LOG_ERROR("otcrypto_ecc_p384_public_key_export failed: 0x%x",
                status.value);
      return INTERNAL(status.value);
    }

    resp.qx_len = kP384CoordBytes;
    memcpy(resp.qx, qx, kP384CoordBytes);
    resp.qy_len = kP384CoordBytes;
    memcpy(resp.qy, qy, kP384CoordBytes);
    resp.d0_len = kP384MaskedScalarShareBytes;
    memcpy(resp.d0, d0, kP384MaskedScalarShareBytes);
    resp.d1_len = kP384MaskedScalarShareBytes;
    memcpy(resp.d1, d1, kP384MaskedScalarShareBytes);
    uint32_t d_scalar[kP384ScalarWords];
    TRY(hardened_add_mod(d0, d1, kP384OrderLE, kP384ScalarWords, d_scalar));
    resp.d_len = kP384ScalarBytes;
    memcpy(resp.d, d_scalar, kP384ScalarBytes);
  } else {
    LOG_ERROR("Unsupported ECC curve for keygen: %d", uj_curve);
    return INVALID_ARGUMENT();
  }

  RESP_OK(ujson_serialize_cryptotest_ecdsa_keygen_resp_t, uj, &resp);
  return OK_STATUS(0);
}

status_t handle_ecdsa(ujson_t *uj) {
  cryptotest_ecdsa_operation_t uj_op;
  cryptotest_ecdsa_hash_alg_t uj_hash_alg;

  TRY(ujson_deserialize_cryptotest_ecdsa_operation_t(uj, &uj_op));

  if (uj_op == kCryptotestEcdsaOperationKeyGen) {
    cryptotest_ecdsa_curve_t uj_curve;
    TRY(ujson_deserialize_cryptotest_ecdsa_curve_t(uj, &uj_curve));
    return handle_ecdsa_keygen(uj, uj_curve);
  }

  TRY(ujson_deserialize_cryptotest_ecdsa_hash_alg_t(uj, &uj_hash_alg));

  if (uj_op == kCryptotestEcdsaOperationHash) {
    cryptotest_ecdsa_message_t uj_message;
    TRY(ujson_deserialize_cryptotest_ecdsa_message_t(uj, &uj_message));
    return handle_ecdsa_hash(uj, uj_hash_alg, &uj_message);
  }

  // Sign / Verify: read remaining parameters.
  cryptotest_ecdsa_curve_t uj_curve;
  cryptotest_ecdsa_message_t uj_message;
  cryptotest_ecdsa_signature_t uj_signature;
  cryptotest_ecdsa_coordinate_t uj_qx;
  cryptotest_ecdsa_coordinate_t uj_qy;
  cryptotest_ecdsa_private_key_t uj_private_key;

  TRY(ujson_deserialize_cryptotest_ecdsa_curve_t(uj, &uj_curve));
  TRY(ujson_deserialize_cryptotest_ecdsa_message_t(uj, &uj_message));
  TRY(ujson_deserialize_cryptotest_ecdsa_signature_t(uj, &uj_signature));
  TRY(ujson_deserialize_cryptotest_ecdsa_coordinate_t(uj, &uj_qx));
  TRY(ujson_deserialize_cryptotest_ecdsa_coordinate_t(uj, &uj_qy));
  TRY(ujson_deserialize_cryptotest_ecdsa_private_key_t(uj, &uj_private_key));

  otcrypto_unblinded_key_t public_key;
  size_t digest_len;

  otcrypto_word32_buf_t signature_mut;
  int success;
  uint32_t signature_p256[kP256ScalarWords * 2];
  uint32_t signature_p384[kP384ScalarWords * 2];
  uint32_t pub_p256[kP256CoordWords * 2];
  uint32_t pub_p384[kP384CoordWords * 2];

  switch (uj_curve) {
    case kCryptotestEcdsaCurveP256:
      success = set_nist_p256_params(uj_qx, uj_qy, uj_signature, &public_key,
                                     signature_p256, pub_p256, &signature_mut,
                                     &digest_len);
      if (!success) {
        return INVALID_ARGUMENT();
      }
      break;
    case kCryptotestEcdsaCurveP384:
      success = set_nist_p384_params(uj_qx, uj_qy, uj_signature, &public_key,
                                     signature_p384, pub_p384, &signature_mut,
                                     &digest_len);
      if (!success) {
        return INVALID_ARGUMENT();
      }
      break;
    default:
      LOG_ERROR("Unsupported ECC curve: %d", uj_curve);
      return INVALID_ARGUMENT();
  }

  otcrypto_const_word32_buf_t signature = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, signature_mut.data, signature_mut.len);

  otcrypto_hash_mode_t mode;
  size_t hash_digest_words;
  switch (uj_hash_alg) {
    case kCryptotestEcdsaHashAlgSha256:
      mode = kOtcryptoHashModeSha256;
      hash_digest_words = 256 / 32;
      break;
    case kCryptotestEcdsaHashAlgSha384:
      mode = kOtcryptoHashModeSha384;
      hash_digest_words = 384 / 32;
      break;
    case kCryptotestEcdsaHashAlgSha512:
      mode = kOtcryptoHashModeSha512;
      hash_digest_words = 512 / 32;
      break;
    case kCryptotestEcdsaHashAlgSha3_256:
      mode = kOtcryptoHashModeSha3_256;
      hash_digest_words = 256 / 32;
      break;
    case kCryptotestEcdsaHashAlgSha3_384:
      mode = kOtcryptoHashModeSha3_384;
      hash_digest_words = 384 / 32;
      break;
    case kCryptotestEcdsaHashAlgSha3_512:
      mode = kOtcryptoHashModeSha3_512;
      hash_digest_words = 512 / 32;
      break;
    default:
      LOG_ERROR("Unrecognized ECDSA hash mode: %d", uj_hash_alg);
      return INVALID_ARGUMENT();
  }
  // The cryptolib requires message_digest.len == curve scalar words exactly.
  // Words are in MSW-first order, so:
  //   hash > curve: take the first digest_len words (leftmost/most-significant
  //                 bits)
  //   hash < curve: right-align the hash at the end of the buffer
  //                 (zero-pad high words)
  uint32_t message_buf[ECDSA_CMD_MAX_MESSAGE_WORDS];
  memset(message_buf, 0, digest_len * sizeof(uint32_t));
  if (hash_digest_words >= digest_len) {
    memcpy(message_buf, uj_message.input, digest_len * sizeof(uint32_t));
  } else {
    size_t offset_bytes = (digest_len - hash_digest_words) * sizeof(uint32_t);
    memcpy((uint8_t *)message_buf + offset_bytes, uj_message.input,
           uj_message.input_len);
  }
  const otcrypto_hash_digest_t message_digest = {
      .mode = mode,
      .len = digest_len,
      .data = message_buf,
  };

  switch (uj_op) {
    case kCryptotestEcdsaOperationSign: {
      switch (uj_curve) {
        case kCryptotestEcdsaCurveP256: {
          return p256_sign(uj, &uj_private_key, &public_key, message_digest,
                           signature_mut, &uj_signature);
        }
        case kCryptotestEcdsaCurveP384: {
          return p384_sign(uj, &uj_private_key, &public_key, message_digest,
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
      otcrypto_status_t status;
      switch (uj_curve) {
        case kCryptotestEcdsaCurveP256: {
          status = otcrypto_ecdsa_p256_verify(&public_key, message_digest,
                                              &signature, &verification_result);
          break;
        }
        case kCryptotestEcdsaCurveP384: {
          status = otcrypto_ecdsa_p384_verify(&public_key, message_digest,
                                              &signature, &verification_result);
          break;
        }
        default:
          LOG_ERROR("Unsupported ECC curve: %d", uj_curve);
          return INVALID_ARGUMENT();
      }
      return interpret_verify_status(uj, status, &verification_result);
    }
    default:
      LOG_ERROR("Unrecognized ECDSA operation: %d", uj_op);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}
