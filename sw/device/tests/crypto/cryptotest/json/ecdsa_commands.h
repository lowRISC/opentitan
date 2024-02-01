// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_ECDSA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_ECDSA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define ECDSA_CMD_MAX_MESSAGE_BYTES 64
#define ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES 64
#define ECDSA_CMD_MAX_COORDINATE_BYTES 64
#define ECDSA_CMD_MAX_PRIVATE_KEY_SHARE_BYTES 64

// clang-format off

// Following a `Verify` Operation, the host is expected to send the following parameters, in order:
// - hash_alg (ECDSA_HASH_ALG)
// - curve (ECDSA_CURVE)
// - message_digest (ECDSA_MESSAGE)
// - signature (ECDSA_SIGNATURE)
// - qx (ECDSA_COORDINATE)
// - qy (ECDSA_COORDINATE)
// The device will then respond with:
// - result (ECDSA_VERIFY_OUTPUT)
#define ECDSA_OPERATION(_, value) \
    value(_, Sign) \
    value(_, Verify)
UJSON_SERDE_ENUM(CryptotestEcdsaOperation, cryptotest_ecdsa_operation_t, ECDSA_OPERATION);

#define ECDSA_HASH_ALG(_, value) \
    value(_, Sha256) \
    value(_, Sha384) \
    value(_, Sha512) \
    value(_, Sha3_256) \
    value(_, Sha3_384) \
    value(_, Sha3_512)
UJSON_SERDE_ENUM(CryptotestEcdsaHashAlg, cryptotest_ecdsa_hash_alg_t, ECDSA_HASH_ALG);

#define ECDSA_CURVE(_, value) \
    value(_, P256) \
    value(_, P384)
UJSON_SERDE_ENUM(CryptotestEcdsaCurve, cryptotest_ecdsa_curve_t, ECDSA_CURVE);

#define ECDSA_MESSAGE(field, string) \
    field(input, uint8_t, ECDSA_CMD_MAX_MESSAGE_BYTES) \
    field(input_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEcdsaMessage, cryptotest_ecdsa_message_t, ECDSA_MESSAGE);

#define ECDSA_SIGNATURE(field, string) \
    field(r, uint8_t, ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES) \
    field(r_len, size_t) \
    field(s, uint8_t, ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES) \
    field(s_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEcdsaSignature, cryptotest_ecdsa_signature_t, ECDSA_SIGNATURE);

#define ECDSA_COORDINATE(field, string) \
    field(coordinate, uint8_t, ECDSA_CMD_MAX_COORDINATE_BYTES) \
    field(coordinate_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEcdsaCoordinate, cryptotest_ecdsa_coordinate_t, ECDSA_COORDINATE);

#define ECDSA_PRIVATE_KEY(field, string) \
    field(d0, uint8_t, ECDSA_CMD_MAX_PRIVATE_KEY_SHARE_BYTES) \
    field(d0_len, size_t) \
    field(d1, uint8_t, ECDSA_CMD_MAX_PRIVATE_KEY_SHARE_BYTES) \
    field(d1_len, size_t) \
    field(unmasked_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEcdsaPrivateKey, cryptotest_ecdsa_private_key_t, ECDSA_PRIVATE_KEY);

#define ECDSA_VERIFY_OUTPUT(_, value) \
    value(_, Success) \
    value(_, Failure)
UJSON_SERDE_ENUM(CryptotestEcdsaVerifyOutput, cryptotest_ecdsa_verify_output_t, ECDSA_VERIFY_OUTPUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_ECDSA_COMMANDS_H_
