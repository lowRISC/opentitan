// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/verify.h"
#include "sw/device/tests/crypto/cryptotest/json/sphincsplus_commands.h"

status_t handle_sphincsplus_verify(ujson_t *uj) {
  // Declare SPHINCS+ parameter ujson deserializer types
  cryptotest_sphincsplus_hash_alg_t uj_hash_alg;
  cryptotest_sphincsplus_public_key_t uj_public_key;
  cryptotest_sphincsplus_message_t uj_message;
  cryptotest_sphincsplus_signature_t uj_signature;

  // Deserialize ujson byte stream into SPHINCS+ parameters
  TRY(ujson_deserialize_cryptotest_sphincsplus_hash_alg_t(uj, &uj_hash_alg));
  TRY(ujson_deserialize_cryptotest_sphincsplus_public_key_t(uj,
                                                            &uj_public_key));
  TRY(ujson_deserialize_cryptotest_sphincsplus_message_t(uj, &uj_message));
  TRY(ujson_deserialize_cryptotest_sphincsplus_signature_t(uj, &uj_signature));

  if (uj_public_key.public_len != kSpxVerifyPkBytes) {
    LOG_ERROR("Incorrect public key length: (expected = %d, got = %d)",
              kSpxVerifyPkBytes, uj_public_key.public_len);
    return INVALID_ARGUMENT();
  }
  if (uj_signature.signature_len != kSpxVerifySigBytes) {
    LOG_ERROR("Incorrect signature length: (expected = %d, got = %d)",
              kSpxVerifySigBytes, uj_signature.signature_len);
    return INVALID_ARGUMENT();
  }

  switch (uj_hash_alg) {
    case kCryptotestSphincsPlusHashAlgSha256:
      break;
    case kCryptotestSphincsPlusHashAlgShake256:
      LOG_ERROR("SPHINCS+ SHAKE-256 is currently unsupported.");
      return INVALID_ARGUMENT();
    default:
      LOG_ERROR("Unrecognized SPHINCS+ hash mode: %d", uj_hash_alg);
      return INVALID_ARGUMENT();
  }
  uint32_t exp_root[kSpxVerifyRootNumWords];
  spx_public_key_root((uint32_t *)uj_public_key.public, exp_root);
  uint32_t act_root[kSpxVerifyRootNumWords];
  rom_error_t error =
      spx_verify((uint32_t *)uj_signature.signature, NULL, 0, NULL, 0, NULL, 0,
                 (uint8_t *)uj_message.message, uj_message.message_len,
                 (uint32_t *)uj_public_key.public, act_root);
  cryptotest_sphincsplus_verify_output_t uj_output;
  switch (error) {
    case kErrorOk:
      uj_output = kCryptotestSphincsPlusVerifyOutputSuccess;
      for (size_t i = 0; i < kSpxVerifyRootNumWords; i++) {
        if (exp_root[i] != act_root[i]) {
          uj_output = kCryptotestSphincsPlusVerifyOutputFailure;
          break;
        }
      }
      RESP_OK(ujson_serialize_cryptotest_sphincsplus_verify_output_t, uj,
              &uj_output);
      break;
    case kErrorSigverifyBadSpxSignature:
      OT_FALLTHROUGH_INTENDED;
    case kErrorSigverifyBadSpxKey:
      uj_output = kCryptotestSphincsPlusVerifyOutputFailure;
      // Respond "failure" if the IUT reports an invalid argument
      RESP_OK(ujson_serialize_cryptotest_sphincsplus_verify_output_t, uj,
              &uj_output);
      break;
    default:
      LOG_ERROR(
          "Unexpected error value returned from spx_verify: "
          "0x%x",
          error);
      return INTERNAL();
  }
  return OK_STATUS(0);
}

status_t handle_sphincsplus(ujson_t *uj) {
  cryptotest_sphincsplus_operation_t uj_op;
  TRY(ujson_deserialize_cryptotest_sphincsplus_operation_t(uj, &uj_op));
  switch (uj_op) {
    case kCryptotestSphincsPlusOperationVerify:
      return handle_sphincsplus_verify(uj);
    default:
      LOG_ERROR("Unsupported SPHINCS+ operation: %d", uj_op);
      return INVALID_ARGUMENT();
  }
}
