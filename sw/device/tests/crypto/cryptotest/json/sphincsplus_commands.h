// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_SPHINCSPLUS_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_SPHINCSPLUS_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define SPHINCSPLUS_CMD_MAX_MESSAGE_BYTES 3300
#define SPHINCSPLUS_CMD_MAX_SIGNATURE_BYTES 7856
#define SPHINCSPLUS_CMD_MAX_PUBLIC_KEY_BYTES 32

// clang-format off

#define SPHINCSPLUS_OPERATION(_, value) \
    value(_, Verify)
UJSON_SERDE_ENUM(CryptotestSphincsPlusOperation, cryptotest_sphincsplus_operation_t, SPHINCSPLUS_OPERATION);

#define SPHINCSPLUS_HASH_ALG(_, value) \
    value(_, Sha256) \
    value(_, Shake256)
UJSON_SERDE_ENUM(CryptotestSphincsPlusHashAlg, cryptotest_sphincsplus_hash_alg_t, SPHINCSPLUS_HASH_ALG);

#define SPHINCSPLUS_MESSAGE(field, string) \
    field(message, uint8_t, SPHINCSPLUS_CMD_MAX_MESSAGE_BYTES) \
    field(message_len, size_t)
UJSON_SERDE_STRUCT(CryptotestSphincsPlusMessage, cryptotest_sphincsplus_message_t, SPHINCSPLUS_MESSAGE);

#define SPHINCSPLUS_SIGNATURE(field, string) \
    field(signature, uint8_t, SPHINCSPLUS_CMD_MAX_SIGNATURE_BYTES) \
    field(signature_len, size_t)
UJSON_SERDE_STRUCT(CryptotestSphincsPlusSignature, cryptotest_sphincsplus_signature_t, SPHINCSPLUS_SIGNATURE);

#define SPHINCSPLUS_PUBLIC_KEY(field, string) \
    field(public, uint8_t, SPHINCSPLUS_CMD_MAX_PUBLIC_KEY_BYTES) \
    field(public_len, size_t)
UJSON_SERDE_STRUCT(CryptotestSphincsPlusPublicKey, cryptotest_sphincsplus_public_key_t, SPHINCSPLUS_PUBLIC_KEY);

#define SPHINCSPLUS_VERIFY_OUTPUT(_, value) \
    value(_, Success) \
    value(_, Failure)
UJSON_SERDE_ENUM(CryptotestSphincsPlusVerifyOutput, cryptotest_sphincsplus_verify_output_t, SPHINCSPLUS_VERIFY_OUTPUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_SPHINCSPLUS_COMMANDS_H_
