// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_AES_GCM_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_AES_GCM_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// All of these max values are calculated from the
// NIST AES GCM testvectors.
#define AES_GCM_CMD_MAX_MSG_BYTES 64
#define AES_GCM_CMD_MAX_KEY_BYTES 32
#define AES_GCM_CMD_MAX_IV_BYTES 128
#define AES_GCM_CMD_MAX_AAD_BYTES 90
#define AES_GCM_CMD_MAX_TAG_BYTES 16

// clang-format off

// AES-GCM arguments
#define AES_GCM_OPERATION(_, value) \
    value(_, Encrypt) \
    value(_, Decrypt)
UJSON_SERDE_ENUM(CryptotestAesGcmOperation, cryptotest_aes_gcm_operation_t, AES_GCM_OPERATION);

#define AES_GCM_DATA(field, string) \
    field(key, uint8_t, AES_GCM_CMD_MAX_KEY_BYTES) \
    field(key_length, size_t) \
    field(iv, uint8_t, AES_GCM_CMD_MAX_IV_BYTES) \
    field(iv_length, size_t) \
    field(aad, uint8_t, AES_GCM_CMD_MAX_AAD_BYTES) \
    field(aad_length, size_t) \
    field(tag, uint8_t, AES_GCM_CMD_MAX_TAG_BYTES) \
    field(tag_length, size_t) \
    field(input, uint8_t, AES_GCM_CMD_MAX_MSG_BYTES) \
    field(input_length, size_t)
UJSON_SERDE_STRUCT(CryptotestAesGcmData, cryptotest_aes_gcm_data_t, AES_GCM_DATA);

#define AES_GCM_OUTPUT(field, string) \
    field(oneshot_output, uint8_t, AES_GCM_CMD_MAX_MSG_BYTES) \
    field(stepwise_output, uint8_t, AES_GCM_CMD_MAX_MSG_BYTES) \
    field(output_length, size_t)
UJSON_SERDE_STRUCT(CryptotestAesGcmOutput, cryptotest_aes_gcm_output_t, AES_GCM_OUTPUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_AES_GCM_COMMANDS_H_
