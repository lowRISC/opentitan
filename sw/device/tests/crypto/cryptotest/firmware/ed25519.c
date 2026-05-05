// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/ed25519_commands.h"

// Copied from internal headers to remove dependencies.
// kOtcryptoKeyModeEd25519 is typed as kOtcryptoKeyTypeEcc, so the keyblob
// library appends 64 redundant bits per share to all Ed25519 keys (see
// keyblob.c). These extra bytes are zero-padded and unused by the Ed25519
// algorithm itself, but the keyblob layout requires them so that the share1
// pointer lands at the correct offset within the keyblob.
enum {
  kEd25519MaskedScalarShareBytes =
      ED25519_CMD_PRIVATE_KEY_SHARE_BYTES + (64 / 8),
  kEd25519MaskedScalarShareWords = kEd25519MaskedScalarShareBytes / 4,
  kEd25519MaskedScalarTotalShareWords = 2 * kEd25519MaskedScalarShareWords,
  kEd25519SignatureWords = ED25519_CMD_SIGNATURE_BYTES / 4,
  kEd25519MaxSignatureWords = ED25519_CMD_MAX_SIGNATURE_BYTES / 4,
  kEd25519PublicKeyWords = ED25519_CMD_PUBLIC_KEY_BYTES / 4,
};

static const otcrypto_key_config_t kEd25519PrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEd25519,
    .key_length = ED25519_CMD_PRIVATE_KEY_SHARE_BYTES,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

status_t handle_ed25519(ujson_t *uj) {
  cryptotest_ed25519_operation_t uj_op;
  cryptotest_ed25519_sign_mode_t uj_sign_mode;
  cryptotest_ed25519_message_t uj_message;
  cryptotest_ed25519_signature_t uj_signature;
  cryptotest_ed25519_public_key_t uj_public_key;
  cryptotest_ed25519_private_key_t uj_private_key;

  TRY(ujson_deserialize_cryptotest_ed25519_operation_t(uj, &uj_op));
  TRY(ujson_deserialize_cryptotest_ed25519_sign_mode_t(uj, &uj_sign_mode));
  TRY(ujson_deserialize_cryptotest_ed25519_message_t(uj, &uj_message));
  TRY(ujson_deserialize_cryptotest_ed25519_signature_t(uj, &uj_signature));
  TRY(ujson_deserialize_cryptotest_ed25519_public_key_t(uj, &uj_public_key));
  TRY(ujson_deserialize_cryptotest_ed25519_private_key_t(uj, &uj_private_key));

  otcrypto_eddsa_sign_mode_t sign_mode;
  switch (uj_sign_mode) {
    case kCryptotestEd25519SignModeEddsa:
      sign_mode = kOtcryptoEddsaSignModeEddsa;
      break;
    case kCryptotestEd25519SignModeHashEddsa:
      sign_mode = kOtcryptoEddsaSignModeHashEddsa;
      break;
    default:
      LOG_ERROR("Unrecognized Ed25519 sign mode: %d", uj_sign_mode);
      return INVALID_ARGUMENT();
  }

  otcrypto_const_byte_buf_t message = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (const uint8_t *)uj_message.input,
      uj_message.input_len);

  switch (uj_op) {
    case kCryptotestEd25519OperationSign: {
      if (uj_private_key.d0_len > ED25519_CMD_PRIVATE_KEY_SHARE_BYTES ||
          uj_private_key.d1_len > ED25519_CMD_PRIVATE_KEY_SHARE_BYTES) {
        LOG_ERROR(
            "Ed25519 private key share too large (have d0 = %d d1 = %d, max = "
            "%d bytes)",
            uj_private_key.d0_len, uj_private_key.d0_len,
            ED25519_CMD_PRIVATE_KEY_SHARE_BYTES);
        return INVALID_ARGUMENT();
      }

      // The keyblob layout is [share0 || share1], each
      // kEd25519MaskedScalarShareWords words wide. The extra words beyond the
      // 32-byte key data are zero-padding for the 64 redundant bits required by
      // the ECC keyblob format.
      uint32_t keyblob[kEd25519MaskedScalarTotalShareWords] = {0};
      memcpy(keyblob, uj_private_key.d0, uj_private_key.d0_len);
      memcpy(keyblob + kEd25519MaskedScalarShareWords, uj_private_key.d1,
             uj_private_key.d1_len);

      otcrypto_blinded_key_t private_key = {
          .config = kEd25519PrivateKeyConfig,
          .keyblob_length = sizeof(keyblob),
          .keyblob = keyblob,
      };
      private_key.checksum = integrity_blinded_checksum(&private_key);

      // Derive the public key from the private key.
      uint32_t public_key_buf[kEd25519PublicKeyWords];
      otcrypto_unblinded_key_t public_key = {
          .key_mode = kOtcryptoKeyModeEd25519,
          .key_length = ED25519_CMD_PUBLIC_KEY_BYTES,
          .key = public_key_buf,
      };
      otcrypto_status_t keygen_status =
          otcrypto_ed25519_public_key_from_private(&private_key, &public_key);
      if (keygen_status.value != kOtcryptoStatusValueOk) {
        return INTERNAL(keygen_status.value);
      }

      uint32_t signature_data[kEd25519SignatureWords];
      otcrypto_word32_buf_t signature = OTCRYPTO_MAKE_BUF(
          otcrypto_word32_buf_t, signature_data, kEd25519SignatureWords);

      otcrypto_status_t status = otcrypto_ed25519_sign_verify(
          &private_key, &public_key, &message, sign_mode, &signature);

      cryptotest_ed25519_verify_output_t uj_output;
      switch (status.value) {
        case kOtcryptoStatusValueOk:
          uj_output = kCryptotestEd25519VerifyOutputSuccess;
          break;
        case kOtcryptoStatusValueBadArgs:
          uj_output = kCryptotestEd25519VerifyOutputFailure;
          break;
        default:
          LOG_ERROR(
              "Unexpected status value returned from "
              "otcrypto_ed25519_sign_verify: "
              "0x%x",
              status.value);
          return INTERNAL();
      }
      RESP_OK(ujson_serialize_cryptotest_ed25519_verify_output_t, uj,
              &uj_output);
      return OK_STATUS();
    }
    case kCryptotestEd25519OperationVerify: {
      if (uj_public_key.public_key_len > ED25519_CMD_PUBLIC_KEY_BYTES) {
        LOG_ERROR(
            "Invalid Ed25519 public key length (have = %d, want = %d bytes)",
            uj_public_key.public_key_len, ED25519_CMD_PUBLIC_KEY_BYTES);
        return INVALID_ARGUMENT();
      }

      uint32_t public_key_buf[kEd25519PublicKeyWords];
      memcpy(public_key_buf, uj_public_key.public_key,
             ED25519_CMD_PUBLIC_KEY_BYTES);
      otcrypto_unblinded_key_t public_key = {
          .key_mode = kOtcryptoKeyModeEd25519,
          .key_length = ED25519_CMD_PUBLIC_KEY_BYTES,
          .key = public_key_buf,
      };
      public_key.checksum = integrity_unblinded_checksum(&public_key);

      uint32_t signature_data[kEd25519MaxSignatureWords];
      memset(signature_data, 0xff, sizeof(signature_data));
      memcpy(signature_data, uj_signature.signature,
             uj_signature.signature_len);
      size_t signature_words = ceil_div(uj_signature.signature_len, 4);
      otcrypto_const_word32_buf_t signature = OTCRYPTO_MAKE_BUF(
          otcrypto_const_word32_buf_t, signature_data, signature_words);

      hardened_bool_t verification_result = kHardenedBoolFalse;
      otcrypto_status_t status = otcrypto_ed25519_verify(
          &public_key, &message, sign_mode, &signature, &verification_result);

      cryptotest_ed25519_verify_output_t uj_output;
      switch (status.value) {
        case kOtcryptoStatusValueOk:
          switch (verification_result) {
            case kHardenedBoolTrue:
              uj_output = kCryptotestEd25519VerifyOutputSuccess;
              break;
            case kHardenedBoolFalse:
              uj_output = kCryptotestEd25519VerifyOutputFailure;
              break;
            default:
              LOG_ERROR(
                  "Unexpected result value from otcrypto_ed25519_verify: %d",
                  verification_result);
              return INTERNAL();
          }
          break;
        case kOtcryptoStatusValueBadArgs:
          uj_output = kCryptotestEd25519VerifyOutputFailure;
          break;
        default:
          LOG_ERROR(
              "Unexpected status value returned from otcrypto_ed25519_verify: "
              "0x%x",
              status.value);
          return INTERNAL();
      }
      RESP_OK(ujson_serialize_cryptotest_ed25519_verify_output_t, uj,
              &uj_output);
      return OK_STATUS();
    }
    default:
      LOG_ERROR("Unrecognized Ed25519 operation: %d", uj_op);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
