// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_KMAC_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_KMAC_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// These two are >= the longest size our test vectors happen to use.
#define KMAC_CMD_MAX_MESSAGE_BYTES 256
#define KMAC_CMD_MAX_TAG_BYTES 64

// These two are the longest size OpenTitan's KMAC hardware IP supports
#define KMAC_CMD_MAX_CUSTOMIZATION_STRING_BYTES 36
#define KMAC_CMD_MAX_KEY_BYTES 64

// clang-format off

#define KMAC_MODE(_, value) \
    value(_, Kmac128) \
    value(_, Kmac256)
UJSON_SERDE_ENUM(CryptotestKmacMode, cryptotest_kmac_mode_t, KMAC_MODE);

#define KMAC_REQUIRED_TAG_LENGTH(field, string) \
    field(required_tag_length, size_t)
UJSON_SERDE_STRUCT(CryptotestKmacRequiredTagLength, cryptotest_kmac_required_tag_length_t, KMAC_REQUIRED_TAG_LENGTH);

#define KMAC_MESSAGE(field, string) \
    field(message, uint8_t, KMAC_CMD_MAX_MESSAGE_BYTES) \
    field(message_len, size_t)
UJSON_SERDE_STRUCT(CryptotestKmacMessage, cryptotest_kmac_message_t, KMAC_MESSAGE);

#define KMAC_KEY(field, string) \
    field(key, uint8_t, KMAC_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t)
UJSON_SERDE_STRUCT(CryptotestKmacKey, cryptotest_kmac_key_t, KMAC_KEY);

#define KMAC_CUSTOMIZATION_STRING(field, string) \
    field(customization_string, uint8_t, KMAC_CMD_MAX_CUSTOMIZATION_STRING_BYTES) \
    field(customization_string_len, size_t)
UJSON_SERDE_STRUCT(CryptotestKmacCustomizationString, cryptotest_kmac_customization_string_t, KMAC_CUSTOMIZATION_STRING);

#define KMAC_TAG(field, string) \
    field(tag, uint8_t, KMAC_CMD_MAX_TAG_BYTES) \
    field(tag_len, size_t)
UJSON_SERDE_STRUCT(CryptotestKmacTag, cryptotest_kmac_tag_t, KMAC_TAG);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_KMAC_COMMANDS_H_
