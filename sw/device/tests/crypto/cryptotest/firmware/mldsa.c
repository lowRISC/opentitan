// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/cryptotest/firmware/mldsa.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/mldsa/mldsa.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/mldsa.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/mldsa_commands.h"

static status_t handle_mldsa_sign(ujson_t *uj) {
  cryptotest_mldsa_private_key_seed_t uj_seed;
  cryptotest_mldsa_message_t uj_msg;
  cryptotest_mldsa_context_t uj_ctx;

  TRY(ujson_deserialize_cryptotest_mldsa_private_key_seed_t(uj, &uj_seed));
  TRY(ujson_deserialize_cryptotest_mldsa_message_t(uj, &uj_msg));
  TRY(ujson_deserialize_cryptotest_mldsa_context_t(uj, &uj_ctx));

  if (uj_seed.private_seed_len != 32 ||
      uj_ctx.context_len > kOtcryptoMldsa87CtxMaxBytes) {
    cryptotest_mldsa_signature_t uj_sig = {
        .signature_len = 0,
    };
    RESP_OK(ujson_serialize_cryptotest_mldsa_signature_t, uj, &uj_sig);
    return OK_STATUS(0);
  }

  // Construct xi keyblob with share 0 = private_seed and share 1 = 0.
  static uint32_t xi_data[16];
  memset(xi_data, 0, sizeof(xi_data));
  memcpy(xi_data, uj_seed.private_seed, 32);

  otcrypto_blinded_key_t xi = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMldsa87,
              .key_length = 64,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(xi_data),
      .keyblob = xi_data,
  };
  xi.checksum = otcrypto_integrity_blinded_checksum(&xi);

  static uint32_t pk_data[kOtcryptoMldsa87PkWords];
  otcrypto_unblinded_key_t pk = {
      .key_mode = kOtcryptoKeyModePqcMldsa87,
      .key_length = kOtcryptoMldsa87PkBytes,
      .key = pk_data,
  };
  pk.checksum = otcrypto_integrity_unblinded_checksum(&pk);

  static uint32_t sk_data[kOtcryptoMldsa87SkWords];
  otcrypto_blinded_key_t sk = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMldsa87,
              .key_length = kOtcryptoMldsa87SkBytes,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(sk_data),
      .keyblob = sk_data,
  };
  sk.checksum = otcrypto_integrity_blinded_checksum(&sk);

  status_t kg_status = mldsa87_det_keygen_internal_start(&xi);
  if (!status_ok(kg_status)) {
    LOG_ERROR("mldsa87_det_keygen_internal_start failed");
    cryptotest_mldsa_signature_t uj_sig = {
        .signature_len = 0,
    };
    RESP_OK(ujson_serialize_cryptotest_mldsa_signature_t, uj, &uj_sig);
    return OK_STATUS(0);
  }
  kg_status = mldsa87_keygen_internal_finalize(&pk, &sk);
  if (!status_ok(kg_status)) {
    LOG_ERROR("mldsa87_keygen_internal_finalize failed");
    cryptotest_mldsa_signature_t uj_sig = {
        .signature_len = 0,
    };
    RESP_OK(ujson_serialize_cryptotest_mldsa_signature_t, uj, &uj_sig);
    return OK_STATUS(0);
  }
  sk.checksum = otcrypto_integrity_blinded_checksum(&sk);

  otcrypto_const_byte_buf_t msg =
      otcrypto_make_const_byte_buf(uj_msg.message, uj_msg.message_len);
  otcrypto_const_byte_buf_t ctx =
      otcrypto_make_const_byte_buf(uj_ctx.context, uj_ctx.context_len);

  static uint32_t sig_data[kOtcryptoMldsa87SigWords];
  otcrypto_word32_buf_t sig =
      otcrypto_make_word32_buf(sig_data, kOtcryptoMldsa87SigWords);

  otcrypto_status_t status =
      otcrypto_mldsa87_sign(&sk, &msg, &ctx, kOtcryptoMldsaHashModePure,
                            kOtcryptoMldsaSignModeDet, &sig);
  if (!status_ok(status)) {
    LOG_ERROR("otcrypto_mldsa87_sign failed with status 0x%x", status.value);
    cryptotest_mldsa_signature_t uj_sig = {
        .signature_len = 0,
    };
    RESP_OK(ujson_serialize_cryptotest_mldsa_signature_t, uj, &uj_sig);
    return OK_STATUS(0);
  }

  cryptotest_mldsa_signature_t uj_sig = {
      .signature_len = 4627,
  };
  memcpy(uj_sig.signature, sig_data, 4627);

  RESP_OK(ujson_serialize_cryptotest_mldsa_signature_t, uj, &uj_sig);
  return OK_STATUS(0);
}

static status_t handle_mldsa_verify(ujson_t *uj) {
  cryptotest_mldsa_public_key_t uj_pk;
  cryptotest_mldsa_message_t uj_msg;
  cryptotest_mldsa_context_t uj_ctx;
  cryptotest_mldsa_signature_t uj_sig;

  TRY(ujson_deserialize_cryptotest_mldsa_public_key_t(uj, &uj_pk));
  TRY(ujson_deserialize_cryptotest_mldsa_message_t(uj, &uj_msg));
  TRY(ujson_deserialize_cryptotest_mldsa_context_t(uj, &uj_ctx));
  TRY(ujson_deserialize_cryptotest_mldsa_signature_t(uj, &uj_sig));

  otcrypto_unblinded_key_t pk = {
      .key_mode = kOtcryptoKeyModePqcMldsa87,
      .key_length = uj_pk.public_key_len,
      .key = (uint32_t *)uj_pk.public_key,
  };
  pk.checksum = otcrypto_integrity_unblinded_checksum(&pk);

  otcrypto_const_byte_buf_t msg =
      otcrypto_make_const_byte_buf(uj_msg.message, uj_msg.message_len);
  otcrypto_const_byte_buf_t ctx =
      otcrypto_make_const_byte_buf(uj_ctx.context, uj_ctx.context_len);

  static uint32_t sig_data[kOtcryptoMldsa87SigWords];
  memset(sig_data, 0, sizeof(sig_data));
  memcpy(sig_data, uj_sig.signature,
         uj_sig.signature_len < 4627 ? uj_sig.signature_len : 4627);
  size_t sig_words =
      (uj_sig.signature_len == 4627) ? kOtcryptoMldsa87SigWords : 0;
  otcrypto_const_word32_buf_t sig =
      otcrypto_make_const_word32_buf(sig_data, sig_words);

  hardened_bool_t verification_result = kHardenedBoolFalse;
  otcrypto_status_t status = otcrypto_mldsa87_verify(
      &pk, &msg, &ctx, &sig, kOtcryptoMldsaHashModePure, &verification_result);
  if (!status_ok(status)) {
    cryptotest_mldsa_verify_result_t uj_res = {
        .valid = false,
    };
    RESP_OK(ujson_serialize_cryptotest_mldsa_verify_result_t, uj, &uj_res);
    return OK_STATUS(0);
  }

  cryptotest_mldsa_verify_result_t uj_res = {
      .valid = (verification_result == kHardenedBoolTrue),
  };
  RESP_OK(ujson_serialize_cryptotest_mldsa_verify_result_t, uj, &uj_res);
  return OK_STATUS(0);
}

status_t handle_mldsa(ujson_t *uj) {
  cryptotest_mldsa_operation_t uj_op;
  TRY(ujson_deserialize_cryptotest_mldsa_operation_t(uj, &uj_op));
  switch (uj_op) {
    case kCryptotestMldsaOperationSign:
      return handle_mldsa_sign(uj);
    case kCryptotestMldsaOperationVerify:
      return handle_mldsa_verify(uj);
    default:
      LOG_ERROR("Unsupported ML-DSA operation: %d", uj_op);
      return INVALID_ARGUMENT();
  }
}
