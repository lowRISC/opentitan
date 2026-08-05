// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_MLDSA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_MLDSA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define MODULE_ID MAKE_MODULE_ID('j', 'm', 'd')

#define MLDSA_CMD_MAX_PRIVATE_SEED_BYTES 33
#define MLDSA_CMD_MAX_PUBLIC_KEY_BYTES 2593
#define MLDSA_CMD_MAX_SIGNATURE_BYTES 4628
#define MLDSA_CMD_MAX_MSG_BYTES 512
#define MLDSA_CMD_MAX_CTX_BYTES 256

// clang-format off

#define MLDSA_OPERATION(_, value) \
    value(_, Sign) \
    value(_, Verify)
UJSON_SERDE_ENUM(CryptotestMldsaOperation, cryptotest_mldsa_operation_t, MLDSA_OPERATION);

#define MLDSA_PRIVATE_KEY_SEED(field, string) \
    field(private_seed, uint8_t, MLDSA_CMD_MAX_PRIVATE_SEED_BYTES) \
    field(private_seed_len, size_t)
UJSON_SERDE_STRUCT(CryptotestMldsaPrivateKeySeed, cryptotest_mldsa_private_key_seed_t, MLDSA_PRIVATE_KEY_SEED);

#define MLDSA_PUBLIC_KEY(field, string) \
    field(public_key, uint8_t, MLDSA_CMD_MAX_PUBLIC_KEY_BYTES) \
    field(public_key_len, size_t)
UJSON_SERDE_STRUCT(CryptotestMldsaPublicKey, cryptotest_mldsa_public_key_t, MLDSA_PUBLIC_KEY);

#define MLDSA_MESSAGE(field, string) \
    field(message, uint8_t, MLDSA_CMD_MAX_MSG_BYTES) \
    field(message_len, size_t)
UJSON_SERDE_STRUCT(CryptotestMldsaMessage, cryptotest_mldsa_message_t, MLDSA_MESSAGE);

#define MLDSA_CONTEXT(field, string) \
    field(context, uint8_t, MLDSA_CMD_MAX_CTX_BYTES) \
    field(context_len, size_t)
UJSON_SERDE_STRUCT(CryptotestMldsaContext, cryptotest_mldsa_context_t, MLDSA_CONTEXT);

#define MLDSA_SIGNATURE(field, string) \
    field(signature, uint8_t, MLDSA_CMD_MAX_SIGNATURE_BYTES) \
    field(signature_len, size_t)
UJSON_SERDE_STRUCT(CryptotestMldsaSignature, cryptotest_mldsa_signature_t, MLDSA_SIGNATURE);

#define MLDSA_VERIFY_RESULT(field, string) \
    field(valid, bool)
UJSON_SERDE_STRUCT(CryptotestMldsaVerifyResult, cryptotest_mldsa_verify_result_t, MLDSA_VERIFY_RESULT);

#undef MODULE_ID

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_MLDSA_COMMANDS_H_
