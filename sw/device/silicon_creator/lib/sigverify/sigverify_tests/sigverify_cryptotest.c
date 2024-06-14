// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <stdbool.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_verify.h"
#include "sw/device/tests/crypto/cryptotest/json/ecdsa_commands.h"

// Include commands
#include "sw/device/tests/crypto/cryptotest/json/commands.h"
#include "sw/device/tests/crypto/cryptotest/json/ecdsa_commands.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

bool ecdsa_p256_params_set(cryptotest_ecdsa_coordinate_t uj_qx,
                           cryptotest_ecdsa_coordinate_t uj_qy,
                           cryptotest_ecdsa_signature_t uj_signature,
                           ecdsa_p256_public_key_t *public_key,
                           ecdsa_p256_signature_t *signature_p256) {
  if (uj_qx.coordinate_len > kEcdsaP256SignatureComponentBytes) {
    LOG_ERROR(
        "Coordinate value qx too large for P256 (have = %d bytes, max = %d "
        "bytes)",
        uj_qx.coordinate_len, kEcdsaP256SignatureComponentBytes);
    return false;
  }
  if (uj_qy.coordinate_len > kEcdsaP256SignatureComponentBytes) {
    LOG_ERROR(
        "Coordinate value qy too large for P256 (have = %d bytes, max = %d "
        "bytes)",
        uj_qy.coordinate_len, kEcdsaP256SignatureComponentBytes);
    return false;
  }
  memset(public_key->x, 0, kEcdsaP256SignatureComponentBytes);
  memcpy(public_key->x, uj_qx.coordinate, uj_qx.coordinate_len);
  memset(public_key->y, 0, kEcdsaP256SignatureComponentBytes);
  memcpy(public_key->y, uj_qy.coordinate, uj_qy.coordinate_len);

  if (uj_signature.r_len > kEcdsaP256SignatureComponentBytes) {
    LOG_ERROR(
        "Signature r value too large for P256 (have = %d bytes, max = %d "
        "bytes)",
        uj_signature.r_len, kEcdsaP256SignatureComponentBytes);
    return false;
  }
  if (uj_signature.s_len > kEcdsaP256SignatureComponentBytes) {
    LOG_ERROR(
        "Signature s value too large for P256 (have = %d bytes, max = %d "
        "bytes)",
        uj_signature.s_len, kEcdsaP256SignatureComponentBytes);
    return false;
  }
  memset(signature_p256->r, 0, kEcdsaP256SignatureComponentBytes);
  memcpy(signature_p256->r, uj_signature.r, uj_signature.r_len);
  memset(signature_p256->s, 0, kEcdsaP256SignatureComponentBytes);
  memcpy(signature_p256->s, uj_signature.s, uj_signature.s_len);
  return true;
}

status_t sigverify_p256_to_status(ujson_t *uj,
                                  const ecdsa_p256_signature_t *signature,
                                  const ecdsa_p256_public_key_t *public_key,
                                  hmac_digest_t *digest) {
  uint32_t flash_exec = 0;
  rom_error_t result =
      sigverify_ecdsa_p256_verify(signature, public_key, digest, &flash_exec);

  hardened_bool_t verification_result = kHardenedBoolFalse;
  if (result == kErrorOk && flash_exec == kSigverifyEcdsaSuccess) {
    verification_result = kHardenedBoolTrue;
  }

  cryptotest_ecdsa_verify_output_t uj_output;
  switch (verification_result) {
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

status_t sigverify_ecdsa_process_command(ujson_t *uj) {
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

  ecdsa_p256_public_key_t public_key;
  ecdsa_p256_signature_t signature_p256;
  switch (uj_curve) {
    case kCryptotestEcdsaCurveP256:
      if (!ecdsa_p256_params_set(uj_qx, uj_qy, uj_signature, &public_key,
                                 &signature_p256)) {
        return INVALID_ARGUMENT();
      }
      break;
    default:
      LOG_ERROR("Unsupported ECC curve: %d", uj_curve);
      return INVALID_ARGUMENT();
  }

  switch (uj_hash_alg) {
    case kCryptotestEcdsaHashAlgSha256:
      break;
    default:
      LOG_ERROR("Unsupported ECDSA hash mode: %d", uj_hash_alg);
      return INVALID_ARGUMENT();
  }

  hmac_digest_t digest_be;
  memset(digest_be.digest, 0, kHmacDigestNumWords * sizeof(uint32_t));
  memcpy(digest_be.digest, uj_message.input, uj_message.input_len);

  hmac_digest_t digest;
  for (size_t i = 0; launder32(i) < kHmacDigestNumWords; i++) {
    digest.digest[i] =
        __builtin_bswap32(digest_be.digest[kHmacDigestNumWords - 1 - i]);
  }

  switch (uj_op) {
    case kCryptotestEcdsaOperationVerify: {
      return sigverify_p256_to_status(uj, &signature_p256, &public_key,
                                      &digest);
    }
    default:
      LOG_ERROR("Usupported ECDSA operation: %d", uj_op);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}

status_t process_cmd(ujson_t *uj) {
  while (true) {
    cryptotest_cmd_t cmd;
    TRY(ujson_deserialize_cryptotest_cmd_t(uj, &cmd));
    switch (cmd) {
      case kCryptotestCommandEcdsa:
        RESP_ERR(uj, sigverify_ecdsa_process_command(uj));
        break;
      default:
        LOG_ERROR("Unsupported command: %d", cmd);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
  }

  return OK_STATUS(0);
}

bool test_main(void) {
  CHECK(otbn_boot_app_load() == kErrorOk);

  ujson_t uj = ujson_ottf_console();
  return status_ok(process_cmd(&uj));
}
