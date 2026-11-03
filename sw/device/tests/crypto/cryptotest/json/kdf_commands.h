// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_KDF_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_KDF_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define MODULE_ID MAKE_MODULE_ID('j', 'k', 'd')

#define KDF_CMD_MAX_KEY_BYTES 192
#define KDF_CMD_MAX_LABEL_BYTES 192
#define KDF_CMD_MAX_CONTEXT_BYTES 256
#define KDF_CMD_MAX_OUTPUT_BYTES 256

// clang-format off

#define KDF_ALGORITHM(_, value)     value(_, Hkdf)     value(_, KmacKdf)     value(_, KdfCtr)
UJSON_SERDE_ENUM(CryptotestKdfAlgorithm, cryptotest_kdf_algorithm_t, KDF_ALGORITHM);

#define KDF_MODE(_, value)     value(_, Sha256)     value(_, Sha384)     value(_, Sha512)     value(_, Kmac128)     value(_, Kmac256)
UJSON_SERDE_ENUM(CryptotestKdfMode, cryptotest_kdf_mode_t, KDF_MODE);

#define KDF_REQUIRED_OUTPUT_LENGTH(field, string)     field(required_output_length, size_t)
UJSON_SERDE_STRUCT(CryptotestKdfRequiredOutputLength, cryptotest_kdf_required_output_length_t, KDF_REQUIRED_OUTPUT_LENGTH);

#define KDF_KEY(field, string)     field(key, uint8_t, KDF_CMD_MAX_KEY_BYTES)     field(key_len, size_t)
UJSON_SERDE_STRUCT(CryptotestKdfKey, cryptotest_kdf_key_t, KDF_KEY);

#define KDF_LABEL(field, string)     field(label, uint8_t, KDF_CMD_MAX_LABEL_BYTES)     field(label_len, size_t)
UJSON_SERDE_STRUCT(CryptotestKdfLabel, cryptotest_kdf_label_t, KDF_LABEL);

#define KDF_CONTEXT(field, string)     field(context, uint8_t, KDF_CMD_MAX_CONTEXT_BYTES)     field(context_len, size_t)
UJSON_SERDE_STRUCT(CryptotestKdfContext, cryptotest_kdf_context_t, KDF_CONTEXT);

#define KDF_OUTPUT(field, string)     field(output, uint8_t, KDF_CMD_MAX_OUTPUT_BYTES)     field(output_len, size_t)
UJSON_SERDE_STRUCT(CryptotestKdfOutput, cryptotest_kdf_output_t, KDF_OUTPUT);

#undef MODULE_ID

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_KDF_COMMANDS_H_
