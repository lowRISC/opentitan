// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_SHA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_SHA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define SHA_CMD_MAX_DIGEST_BYTES 256
#define SHA_CMD_MAX_MSG_BYTES 256

// clang-format off

#define SHA_MODE(_, value) \
    value(_, SHA2_256) \
    value(_, SHA2_384) \
    value(_, SHA2_512) \
    value(_, SHA3_224) \
    value(_, SHA3_256) \
    value(_, SHA3_384) \
    value(_, SHA3_512) \
    value(_, SHAKE_128) \
    value(_, SHAKE_256)
UJSON_SERDE_ENUM(CryptotestShaMode, cryptotest_sha_mode_t, SHA_MODE);

#define SHA_INPUT(field, string) \
    field(msg, uint8_t, SHA_CMD_MAX_MSG_BYTES) \
    field(msg_len, uint32_t) \
    field(out_len, uint32_t)
UJSON_SERDE_STRUCT(CryptotestShaInput, cryptotest_sha_input_t, SHA_INPUT);

#define SHA_OUTPUT(field, string) \
    field(digest, uint8_t, SHA_CMD_MAX_DIGEST_BYTES) \
    field(digest_len, uint32_t)
UJSON_SERDE_STRUCT(CryptotestShaOutput, cryptotest_sha_output_t, SHA_OUTPUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_SHA_COMMANDS_H_
