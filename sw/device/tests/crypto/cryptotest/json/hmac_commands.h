// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_HMAC_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_HMAC_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define HMAC_CMD_MAX_MESSAGE_BYTES 256
#define HMAC_CMD_MAX_KEY_BYTES 192
#define HMAC_CMD_MAX_TAG_BYTES 64

// clang-format off

#define HMAC_HASH_ALG(_, value) \
    value(_, Sha256) \
    value(_, Sha384) \
    value(_, Sha512) \
    value(_, Sha3_256) \
    value(_, Sha3_384) \
    value(_, Sha3_512)
UJSON_SERDE_ENUM(CryptotestHmacHashAlg, cryptotest_hmac_hash_alg_t, HMAC_HASH_ALG);

#define HMAC_MESSAGE(field, string) \
    field(message, uint8_t, HMAC_CMD_MAX_MESSAGE_BYTES) \
    field(message_len, size_t)
UJSON_SERDE_STRUCT(CryptotestHmacMessage, cryptotest_hmac_message_t, HMAC_MESSAGE);

#define HMAC_KEY(field, string) \
    field(key, uint8_t, HMAC_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t)
UJSON_SERDE_STRUCT(CryptotestHmacKey, cryptotest_hmac_key_t, HMAC_KEY);

#define HMAC_TAG(field, string) \
    field(oneshot_tag, uint8_t, HMAC_CMD_MAX_TAG_BYTES) \
    field(streaming_tag, uint8_t, HMAC_CMD_MAX_TAG_BYTES) \
    field(tag_len, size_t)
UJSON_SERDE_STRUCT(CryptotestHmacTag, cryptotest_hmac_tag_t, HMAC_TAG);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_HMAC_COMMANDS_H_
