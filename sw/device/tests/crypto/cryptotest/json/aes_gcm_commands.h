// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_AES_GCM_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_AES_GCM_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define MODULE_ID MAKE_MODULE_ID('j', 'b', 'e')

#define AES_GCM_CMD_MAX_MSG_BYTES 64
#define AES_GCM_CMD_MAX_KEY_BYTES 32  // 256 / 8
#define AES_GCM_CMD_MAX_TAG_BYTES 16  // 128 / 8

// clang-format off

#define AES_GCM_SUBCOMMAND(_, value) \
    value(_, AesGcmOp)
UJSON_SERDE_ENUM(AesGcmSubcommand, aes_gcm_subcommand_t, AES_GCM_SUBCOMMAND);

#define AES_GCM_OPERATION(_, value) \
    value(_, Encrypt) \
    value(_, Decrypt)
UJSON_SERDE_ENUM(CryptotestAesGcmOperation, cryptotest_aes_gcm_operation_t, AES_GCM_OPERATION);

#define AES_GCM_DATA(field, string) \
    field(key, uint8_t, AES_GCM_CMD_MAX_KEY_BYTES) \
    field(key_length, size_t) \
    field(iv, uint8_t, 16) \
    field(iv_length, size_t) \
    field(input, uint8_t, AES_GCM_CMD_MAX_MSG_BYTES) \
    field(input_length, size_t) \
    field(aad, uint8_t, AES_GCM_CMD_MAX_MSG_BYTES) \
    field(aad_length, size_t) \
    field(tag, uint8_t, AES_GCM_CMD_MAX_TAG_BYTES) \
    field(tag_length, size_t)
UJSON_SERDE_STRUCT(CryptotestAesGcmData, cryptotest_aes_gcm_data_t, AES_GCM_DATA);

#define AES_GCM_OUTPUT(field, string) \
    field(output, uint8_t, AES_GCM_CMD_MAX_MSG_BYTES) \
    field(output_len, size_t) \
    field(tag, uint8_t, AES_GCM_CMD_MAX_TAG_BYTES) \
    field(tag_len, size_t) \
    field(tag_valid, bool)
UJSON_SERDE_STRUCT(CryptotestAesGcmOutput, cryptotest_aes_gcm_output_t, AES_GCM_OUTPUT);

#undef MODULE_ID

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_AES_GCM_COMMANDS_H_
