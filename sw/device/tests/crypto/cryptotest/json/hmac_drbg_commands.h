// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_HMAC_DRBG_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_HMAC_DRBG_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define MODULE_ID MAKE_MODULE_ID('j', 'h', 'd')

#define HMAC_DRBG_CMD_MAX_ENTROPY_BYTES 32
#define HMAC_DRBG_CMD_MAX_NONCE_BYTES 16
#define HMAC_DRBG_CMD_MAX_PERSONALIZATION_STRING_BYTES 32
#define HMAC_DRBG_CMD_MAX_ADDITIONAL_INPUT_BYTES 32
#define HMAC_DRBG_CMD_MAX_OUTPUT_BYTES 256

// clang-format off

#define HMAC_DRBG_MODE(_, value) \
    value(_, Sha256) \
    value(_, Sha384) \
    value(_, Sha512)
UJSON_SERDE_ENUM(CryptotestHmacDrbgMode, cryptotest_hmac_drbg_mode_t, HMAC_DRBG_MODE);

#define HMAC_DRBG_INPUT(field, string) \
    field(entropy, uint8_t, HMAC_DRBG_CMD_MAX_ENTROPY_BYTES) \
    field(entropy_len, size_t) \
    field(nonce, uint8_t, HMAC_DRBG_CMD_MAX_NONCE_BYTES) \
    field(nonce_len, size_t) \
    field(personalization_string, uint8_t, HMAC_DRBG_CMD_MAX_PERSONALIZATION_STRING_BYTES) \
    field(personalization_string_len, size_t) \
    field(reseed, uint8_t) \
    field(reseed_entropy, uint8_t, HMAC_DRBG_CMD_MAX_ENTROPY_BYTES) \
    field(reseed_entropy_len, size_t) \
    field(reseed_additional_input, uint8_t, HMAC_DRBG_CMD_MAX_ADDITIONAL_INPUT_BYTES) \
    field(reseed_additional_input_len, size_t) \
    field(additional_input_1, uint8_t, HMAC_DRBG_CMD_MAX_ADDITIONAL_INPUT_BYTES) \
    field(additional_input_1_len, size_t) \
    field(additional_input_2, uint8_t, HMAC_DRBG_CMD_MAX_ADDITIONAL_INPUT_BYTES) \
    field(additional_input_2_len, size_t) \
    field(output_len, size_t)
UJSON_SERDE_STRUCT(CryptotestHmacDrbgInput, cryptotest_hmac_drbg_input_t, HMAC_DRBG_INPUT);

#define HMAC_DRBG_OUTPUT(field, string) \
    field(output, uint8_t, HMAC_DRBG_CMD_MAX_OUTPUT_BYTES) \
    field(output_len, size_t)
UJSON_SERDE_STRUCT(CryptotestHmacDrbgOutput, cryptotest_hmac_drbg_output_t, HMAC_DRBG_OUTPUT);

#undef MODULE_ID

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_HMAC_DRBG_COMMANDS_H_
