// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/hmac_drbg.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/hmac_drbg_commands.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('h', 'm', 'd')

status_t handle_hmac_drbg(ujson_t *uj) {
  // Deserialize test arguments from UART.
  cryptotest_hmac_drbg_mode_t uj_mode;
  TRY(ujson_deserialize_cryptotest_hmac_drbg_mode_t(uj, &uj_mode));

  cryptotest_hmac_drbg_input_t uj_input;
  TRY(ujson_deserialize_cryptotest_hmac_drbg_input_t(uj, &uj_input));

  otcrypto_hash_mode_t mode;
  switch (uj_mode) {
    case kCryptotestHmacDrbgModeSha256:
      mode = kOtcryptoHashModeSha256;
      break;
    case kCryptotestHmacDrbgModeSha384:
      mode = kOtcryptoHashModeSha384;
      break;
    case kCryptotestHmacDrbgModeSha512:
      mode = kOtcryptoHashModeSha512;
      break;
    default:
      return INVALID_ARGUMENT();
  }

  otcrypto_const_byte_buf_t entropy = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, uj_input.entropy, uj_input.entropy_len);
  otcrypto_const_byte_buf_t nonce = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, uj_input.nonce, uj_input.nonce_len);
  otcrypto_const_byte_buf_t perso_string = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, uj_input.personalization_string,
      uj_input.personalization_string_len);
  otcrypto_const_byte_buf_t reseed_entropy =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, uj_input.reseed_entropy,
                        uj_input.reseed_entropy_len);
  otcrypto_const_byte_buf_t reseed_addl = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, uj_input.reseed_additional_input,
      uj_input.reseed_additional_input_len);
  otcrypto_const_byte_buf_t addl_1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, uj_input.additional_input_1,
                        uj_input.additional_input_1_len);
  otcrypto_const_byte_buf_t addl_2 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, uj_input.additional_input_2,
                        uj_input.additional_input_2_len);

  // Buffer for random output.
  cryptotest_hmac_drbg_output_t uj_output = {
      .output_len = uj_input.output_len,
  };
  otcrypto_byte_buf_t output = OTCRYPTO_MAKE_BUF(
      otcrypto_byte_buf_t, uj_output.output, uj_output.output_len);

  // Instantiate HMAC-DRBG context.
  otcrypto_hmac_drbg_context_t ctx;
  TRY(otcrypto_hmac_drbg_init(&ctx, &entropy, &nonce, &perso_string,
                              /*reseed_interval=*/10000, mode));

  // Reseed if the test vector requires it.
  if (uj_input.reseed) {
    TRY(otcrypto_hmac_drbg_reseed(&ctx, &reseed_entropy, &reseed_addl));
  }

  // Add first additional input (the test vectors require generating
  // `output_len` bytes of output here, which are discarded).
  TRY(otcrypto_hmac_drbg_generate(&ctx, &addl_1, &output));

  // Add second additional input and generate random output.
  TRY(otcrypto_hmac_drbg_generate(&ctx, &addl_2, &output));

  TRY(otcrypto_hmac_drbg_deinit(&ctx));

  // Send output to host via UART.
  RESP_OK(ujson_serialize_cryptotest_hmac_drbg_output_t, uj, &uj_output);
  return OK_STATUS(0);
}
