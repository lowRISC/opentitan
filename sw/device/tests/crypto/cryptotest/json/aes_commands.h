// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_AES_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_AES_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define AES_CMD_MAX_MSG_BYTES 64
#define AES_CMD_MAX_KEY_BYTES 32  // 256 / 8

// clang-format off

#define AES_SUBCOMMAND(_, value) \
    value(_, AesBlock) \
    value(_, AesGcm)
UJSON_SERDE_ENUM(AesSubcommand, aes_subcommand_t, AES_SUBCOMMAND);

// AES arguments
#define AES_MODE(_, value) \
    value(_, Ecb) \
    value(_, Cbc) \
    value(_, Cfb) \
    value(_, Ofb) \
    value(_, Ctr)
UJSON_SERDE_ENUM(CryptotestAesMode, cryptotest_aes_mode_t, AES_MODE);

#define AES_OPERATION(_, value) \
    value(_, Encrypt) \
    value(_, Decrypt)
UJSON_SERDE_ENUM(CryptotestAesOperation, cryptotest_aes_operation_t, AES_OPERATION);

#define AES_PADDING(_, value) \
    value(_, Pkcs7) \
    value(_, Iso9797M2) \
    value(_, Null)
UJSON_SERDE_ENUM(CryptotestAesPadding, cryptotest_aes_padding_t, AES_PADDING);

#define AES_DATA(field, string) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_length, size_t) \
    field(iv, uint8_t, 16) \
    field(input, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(input_len, size_t)
UJSON_SERDE_STRUCT(CryptotestAesData, cryptotest_aes_data_t, AES_DATA);

#define AES_OUTPUT(field, string) \
    field(output, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(output_len, uint32_t)
UJSON_SERDE_STRUCT(CryptotestAesOutput, cryptotest_aes_output_t, AES_OUTPUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_AES_COMMANDS_H_
