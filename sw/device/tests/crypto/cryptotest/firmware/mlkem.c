// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/cryptotest/firmware/mlkem.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/mlkem.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/mlkem_commands.h"

static status_t handle_mlkem_encaps(ujson_t *uj) {
  cryptotest_mlkem_public_key_t uj_pk;
  cryptotest_mlkem_message_t uj_m;

  TRY(ujson_deserialize_cryptotest_mlkem_public_key_t(uj, &uj_pk));
  TRY(ujson_deserialize_cryptotest_mlkem_message_t(uj, &uj_m));

  if (uj_pk.public_key_len != kOtcryptoMlkem1024PkBytes) {
    LOG_ERROR("Incorrect public key length: expected = %d, got = %d",
              kOtcryptoMlkem1024PkBytes, uj_pk.public_key_len);
    return INVALID_ARGUMENT();
  }
  if (uj_m.message_len != kOtcryptoMlkem1024SharedSecretBytes) {
    LOG_ERROR("Incorrect message length: expected = %d, got = %d",
              kOtcryptoMlkem1024SharedSecretBytes, uj_m.message_len);
    return INVALID_ARGUMENT();
  }

  otcrypto_unblinded_key_t pk = {
      .key_mode = kOtcryptoKeyModePqcMlkem1024,
      .key_length = kOtcryptoMlkem1024PkBytes,
      .key = (uint32_t *)uj_pk.public_key,
  };

  otcrypto_const_word32_buf_t m = {
      .data = (uint32_t *)uj_m.message,
      .len = kOtcryptoMlkem1024SharedSecretWords,
  };

  uint32_t ct_data[kOtcryptoMlkem1024CtWords];
  otcrypto_word32_buf_t ct = {
      .data = ct_data,
      .len = kOtcryptoMlkem1024CtWords,
  };

  uint32_t ss_data[kOtcryptoMlkem1024SharedSecretWords];
  otcrypto_blinded_key_t ss = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = kOtcryptoMlkem1024SharedSecretBytes / 2,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kOtcryptoMlkem1024SharedSecretBytes,
      .keyblob = ss_data,
  };
  ss.checksum = otcrypto_integrity_blinded_checksum(&ss);

  status_t status = otcrypto_mlkem1024_encaps(&pk, &m, &ct, &ss);
  if (!status_ok(status)) {
    LOG_ERROR("otcrypto_mlkem1024_encaps failed");
    return status;
  }

  cryptotest_mlkem_ciphertext_t uj_ct = {
      .ciphertext_len = kOtcryptoMlkem1024CtBytes,
  };
  memcpy(uj_ct.ciphertext, ct_data, kOtcryptoMlkem1024CtBytes);

  cryptotest_mlkem_shared_secret_t uj_ss = {
      .shared_secret_len = kOtcryptoMlkem1024SharedSecretBytes,
  };
  memcpy(uj_ss.shared_secret, ss_data, kOtcryptoMlkem1024SharedSecretBytes);

  RESP_OK(ujson_serialize_cryptotest_mlkem_ciphertext_t, uj, &uj_ct);
  RESP_OK(ujson_serialize_cryptotest_mlkem_shared_secret_t, uj, &uj_ss);
  return OK_STATUS(0);
}

static status_t handle_mlkem_decaps(ujson_t *uj) {
  cryptotest_mlkem_secret_key_t uj_sk;
  cryptotest_mlkem_ciphertext_t uj_ct;

  TRY(ujson_deserialize_cryptotest_mlkem_secret_key_t(uj, &uj_sk));
  TRY(ujson_deserialize_cryptotest_mlkem_ciphertext_t(uj, &uj_ct));

  if (uj_sk.secret_key_len != kOtcryptoMlkem1024SkBytes) {
    LOG_ERROR("Incorrect secret key length: expected = %d, got = %d",
              kOtcryptoMlkem1024SkBytes, uj_sk.secret_key_len);
    return INVALID_ARGUMENT();
  }
  if (uj_ct.ciphertext_len != kOtcryptoMlkem1024CtBytes) {
    LOG_ERROR("Incorrect ciphertext length: expected = %d, got = %d",
              kOtcryptoMlkem1024CtBytes, uj_ct.ciphertext_len);
    return INVALID_ARGUMENT();
  }

  otcrypto_blinded_key_t sk = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = kOtcryptoMlkem1024SkBytes / 2,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kOtcryptoMlkem1024SkBytes,
      .keyblob = (uint32_t *)uj_sk.secret_key,
  };
  sk.checksum = otcrypto_integrity_blinded_checksum(&sk);

  otcrypto_const_word32_buf_t ct = {
      .data = (uint32_t *)uj_ct.ciphertext,
      .len = kOtcryptoMlkem1024CtWords,
  };

  uint32_t ss_data[kOtcryptoMlkem1024SharedSecretWords];
  otcrypto_blinded_key_t ss = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = kOtcryptoMlkem1024SharedSecretBytes / 2,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kOtcryptoMlkem1024SharedSecretBytes,
      .keyblob = ss_data,
  };
  ss.checksum = otcrypto_integrity_blinded_checksum(&ss);

  status_t status = otcrypto_mlkem1024_decaps(&sk, &ct, &ss);
  if (!status_ok(status)) {
    LOG_ERROR("otcrypto_mlkem1024_decaps failed");
    return status;
  }

  cryptotest_mlkem_shared_secret_t uj_ss = {
      .shared_secret_len = kOtcryptoMlkem1024SharedSecretBytes,
  };
  memcpy(uj_ss.shared_secret, ss_data, kOtcryptoMlkem1024SharedSecretBytes);

  RESP_OK(ujson_serialize_cryptotest_mlkem_shared_secret_t, uj, &uj_ss);
  return OK_STATUS(0);
}

status_t handle_mlkem(ujson_t *uj) {
  cryptotest_mlkem_operation_t uj_op;
  TRY(ujson_deserialize_cryptotest_mlkem_operation_t(uj, &uj_op));
  switch (uj_op) {
    case kCryptotestMlkemOperationEncaps:
      return handle_mlkem_encaps(uj);
    case kCryptotestMlkemOperationDecaps:
      return handle_mlkem_decaps(uj);
    default:
      LOG_ERROR("Unsupported ML-KEM operation: %d", uj_op);
      return INVALID_ARGUMENT();
  }
}
