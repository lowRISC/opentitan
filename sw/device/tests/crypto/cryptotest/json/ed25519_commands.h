// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_ED25519_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_ED25519_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// Ed25519 key and signature sizes (fixed by the algorithm).
#define ED25519_CMD_MAX_MESSAGE_BYTES 1024
#define ED25519_CMD_SIGNATURE_BYTES 64
#define ED25519_CMD_MAX_SIGNATURE_BYTES 128
#define ED25519_CMD_PRIVATE_KEY_SHARE_BYTES 32
#define ED25519_CMD_PUBLIC_KEY_BYTES 32

// clang-format off

// SignCheck operation (sign-then-verify round trip):
// The host sends, in order:
// - operation (ED25519_OPERATION = SignCheck)
// - sign_mode (ED25519_SIGN_MODE)
// - message (ED25519_MESSAGE)
// - signature (ED25519_SIGNATURE)  [unused, sent as zeros]
// - public_key (ED25519_PUBLIC_KEY) [unused, sent as zeros]
// - private_key (ED25519_PRIVATE_KEY)
// The device responds with:
// - result (ED25519_VERIFY_OUTPUT)
//
// Sign operation (signature generation):
// The host sends, in order:
// - operation (ED25519_OPERATION = Sign)
// - sign_mode (ED25519_SIGN_MODE)
// - message (ED25519_MESSAGE)
// - private_key (ED25519_PRIVATE_KEY)
// The device responds with:
// - sign_resp (ED25519_SIGN_RESP)
//
// Verify operation:
// The host sends, in order:
// - operation (ED25519_OPERATION = Verify)
// - sign_mode (ED25519_SIGN_MODE)
// - message (ED25519_MESSAGE)
// - signature (ED25519_SIGNATURE)
// - public_key (ED25519_PUBLIC_KEY)
// - private_key (ED25519_PRIVATE_KEY) [unused, sent as zeros]
// The device responds with:
// - result (ED25519_VERIFY_OUTPUT)

#define ED25519_OPERATION(_, value) \
    value(_, SignCheck) \
    value(_, Sign) \
    value(_, Verify) \
    value(_, KeyGen)
UJSON_SERDE_ENUM(CryptotestEd25519Operation, cryptotest_ed25519_operation_t, ED25519_OPERATION);

#define ED25519_SIGN_MODE(_, value) \
    value(_, Eddsa) \
    value(_, HashEddsa)
UJSON_SERDE_ENUM(CryptotestEd25519SignMode, cryptotest_ed25519_sign_mode_t, ED25519_SIGN_MODE);

#define ED25519_MESSAGE(field, string) \
    field(input, uint8_t, ED25519_CMD_MAX_MESSAGE_BYTES) \
    field(input_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEd25519Message, cryptotest_ed25519_message_t, ED25519_MESSAGE);

#define ED25519_SIGNATURE(field, string) \
    field(signature, uint8_t, ED25519_CMD_MAX_SIGNATURE_BYTES) \
    field(signature_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEd25519Signature, cryptotest_ed25519_signature_t, ED25519_SIGNATURE);

#define ED25519_PUBLIC_KEY(field, string) \
    field(public_key, uint8_t, ED25519_CMD_PUBLIC_KEY_BYTES) \
    field(public_key_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEd25519PublicKey, cryptotest_ed25519_public_key_t, ED25519_PUBLIC_KEY);

#define ED25519_PRIVATE_KEY(field, string) \
    field(d0, uint8_t, ED25519_CMD_PRIVATE_KEY_SHARE_BYTES) \
    field(d0_len, size_t) \
    field(d1, uint8_t, ED25519_CMD_PRIVATE_KEY_SHARE_BYTES) \
    field(d1_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEd25519PrivateKey, cryptotest_ed25519_private_key_t, ED25519_PRIVATE_KEY);

#define ED25519_VERIFY_OUTPUT(_, value) \
    value(_, Success) \
    value(_, Failure)
UJSON_SERDE_ENUM(CryptotestEd25519VerifyOutput, cryptotest_ed25519_verify_output_t, ED25519_VERIFY_OUTPUT);

#define ED25519_SIGN_RESP(field, string) \
    field(signature, uint8_t, ED25519_CMD_SIGNATURE_BYTES) \
    field(signature_len, size_t) \
    field(public_key, uint8_t, ED25519_CMD_PUBLIC_KEY_BYTES) \
    field(public_key_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEd25519SignResp, cryptotest_ed25519_sign_resp_t, ED25519_SIGN_RESP);

#define ED25519_KEYGEN_RESP(field, string) \
    field(d, uint8_t, ED25519_CMD_PRIVATE_KEY_SHARE_BYTES) \
    field(d_len, size_t) \
    field(q, uint8_t, ED25519_CMD_PUBLIC_KEY_BYTES) \
    field(q_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEd25519KeygenResp, cryptotest_ed25519_keygen_resp_t, ED25519_KEYGEN_RESP);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_ED25519_COMMANDS_H_
