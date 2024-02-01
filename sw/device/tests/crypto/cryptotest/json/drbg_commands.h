// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_DRBG_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_DRBG_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define DRBG_CMD_MAX_ENTROPY_BYTES 48
#define DRBG_CMD_MAX_PERSONALIZATION_STRING_BYTES 48
#define DRBG_CMD_MAX_ADDITIONAL_INPUT_BYTES 48
#define DRBG_CMD_MAX_OUTPUT_BYTES 64

// clang-format off

#define DRBG_INPUT(field, string) \
    field(entropy, uint8_t, DRBG_CMD_MAX_ENTROPY_BYTES) \
    field(entropy_len, size_t) \
    field(personalization_string, uint8_t, DRBG_CMD_MAX_PERSONALIZATION_STRING_BYTES) \
    field(personalization_string_len, size_t) \
    field(reseed, uint8_t) \
    field(reseed_entropy, uint8_t, DRBG_CMD_MAX_ENTROPY_BYTES) \
    field(reseed_entropy_len, size_t) \
    field(reseed_additional_input, uint8_t, DRBG_CMD_MAX_ADDITIONAL_INPUT_BYTES) \
    field(reseed_additional_input_len, size_t) \
    field(additional_input_1, uint8_t, DRBG_CMD_MAX_ADDITIONAL_INPUT_BYTES) \
    field(additional_input_1_len, size_t) \
    field(additional_input_2, uint8_t, DRBG_CMD_MAX_ADDITIONAL_INPUT_BYTES) \
    field(additional_input_2_len, size_t) \
    field(output_len, size_t)
UJSON_SERDE_STRUCT(CryptotestDrbgInput, cryptotest_drbg_input_t, DRBG_INPUT);

#define DRBG_OUTPUT(field, string) \
    field(output, uint8_t, DRBG_CMD_MAX_OUTPUT_BYTES) \
    field(output_len, size_t)
UJSON_SERDE_STRUCT(CryptotestDrbgOutput, cryptotest_drbg_output_t, DRBG_OUTPUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_DRBG_COMMANDS_H_
