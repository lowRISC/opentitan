// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_HASH_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_HASH_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define HASH_CMD_MAX_MESSAGE_BYTES 17068
#define HASH_CMD_MAX_CUSTOMIZATION_STRING_BYTES 16
#define HASH_CMD_MAX_DIGEST_BYTES 256

// clang-format off

#define HASH_ALGORITHM(_, value) \
    value(_, Sha256) \
    value(_, Sha384) \
    value(_, Sha512) \
    value(_, Sha3_224) \
    value(_, Sha3_256) \
    value(_, Sha3_384) \
    value(_, Sha3_512) \
    value(_, Shake128) \
    value(_, Shake256) \
    value(_, Cshake128) \
    value(_, Cshake256)
UJSON_SERDE_ENUM(CryptotestHashAlgorithm, cryptotest_hash_algorithm_t, HASH_ALGORITHM);

#define SHAKE_DIGEST_LENGTH(field, string) \
    field(length, size_t)
UJSON_SERDE_STRUCT(CryptotestHashShakeDigestLength, cryptotest_hash_shake_digest_length_t, SHAKE_DIGEST_LENGTH);

#define HASH_MESSAGE(field, string) \
    field(message, uint8_t, HASH_CMD_MAX_MESSAGE_BYTES) \
    field(message_len, size_t) \
    field(customization_string, uint8_t, HASH_CMD_MAX_CUSTOMIZATION_STRING_BYTES) \
    field(customization_string_len, size_t)
UJSON_SERDE_STRUCT(CryptotestHashMessage, cryptotest_hash_message_t, HASH_MESSAGE);

#define HASH_OUTPUT(field, string) \
    field(oneshot_digest, uint8_t, HASH_CMD_MAX_DIGEST_BYTES) \
    field(stepwise_digest, uint8_t, HASH_CMD_MAX_DIGEST_BYTES) \
    field(digest_len, size_t)
UJSON_SERDE_STRUCT(CryptotestHashOutput, cryptotest_hash_output_t, HASH_OUTPUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_HASH_COMMANDS_H_
