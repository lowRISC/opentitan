// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_MLKEM_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_MLKEM_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define MODULE_ID MAKE_MODULE_ID('j', 'm', 'k')

#define MLKEM_CMD_MAX_PUBLIC_KEY_BYTES 1568
#define MLKEM_CMD_MAX_SECRET_KEY_BYTES 3168
#define MLKEM_CMD_MAX_CIPHERTEXT_BYTES 1568
#define MLKEM_CMD_MAX_SHARED_SECRET_BYTES 32
#define MLKEM_CMD_MAX_MSG_BYTES 32

// clang-format off

#define MLKEM_OPERATION(_, value) \
    value(_, Encaps) \
    value(_, Decaps)
UJSON_SERDE_ENUM(CryptotestMlkemOperation, cryptotest_mlkem_operation_t, MLKEM_OPERATION);

#define MLKEM_PUBLIC_KEY(field, string) \
    field(public_key, uint8_t, MLKEM_CMD_MAX_PUBLIC_KEY_BYTES) \
    field(public_key_len, size_t)
UJSON_SERDE_STRUCT(CryptotestMlkemPublicKey, cryptotest_mlkem_public_key_t, MLKEM_PUBLIC_KEY);

#define MLKEM_SECRET_KEY(field, string) \
    field(secret_key, uint8_t, MLKEM_CMD_MAX_SECRET_KEY_BYTES) \
    field(secret_key_len, size_t)
UJSON_SERDE_STRUCT(CryptotestMlkemSecretKey, cryptotest_mlkem_secret_key_t, MLKEM_SECRET_KEY);

#define MLKEM_CIPHERTEXT(field, string) \
    field(ciphertext, uint8_t, MLKEM_CMD_MAX_CIPHERTEXT_BYTES) \
    field(ciphertext_len, size_t)
UJSON_SERDE_STRUCT(CryptotestMlkemCiphertext, cryptotest_mlkem_ciphertext_t, MLKEM_CIPHERTEXT);

#define MLKEM_MESSAGE(field, string) \
    field(message, uint8_t, MLKEM_CMD_MAX_MSG_BYTES) \
    field(message_len, size_t)
UJSON_SERDE_STRUCT(CryptotestMlkemMessage, cryptotest_mlkem_message_t, MLKEM_MESSAGE);

#define MLKEM_SHARED_SECRET(field, string) \
    field(shared_secret, uint8_t, MLKEM_CMD_MAX_SHARED_SECRET_BYTES) \
    field(shared_secret_len, size_t)
UJSON_SERDE_STRUCT(CryptotestMlkemSharedSecret, cryptotest_mlkem_shared_secret_t, MLKEM_SHARED_SECRET);

#undef MODULE_ID

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_MLKEM_COMMANDS_H_
