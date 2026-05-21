// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_X25519_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_X25519_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// X25519 key and shared secret sizes (fixed by the algorithm).
#define X25519_CMD_PRIVATE_KEY_BYTES 32
#define X25519_CMD_PUBLIC_KEY_BYTES 32
#define X25519_CMD_SHARED_SECRET_BYTES 32

// clang-format off

// Shared secret generation
// The host sends, in order:
// - private_key (X25519_PRIVATE_KEY)  [raw scalar; blinding is applied on the device]
// - public_key (X25519_PUBLIC_KEY)    [peer's u-coordinate]
// The device responds with:
// - output (X25519_DERIVE_OUTPUT)     [unblinded shared secret and result]

#define X25519_SUBCOMMAND(_, value) \
    value(_, X25519SSG)
UJSON_SERDE_ENUM(X25519Subcommand, x25519_subcommand_t, X25519_SUBCOMMAND);

#define X25519_PRIVATE_KEY(field, string) \
    field(private_key, uint8_t, X25519_CMD_PRIVATE_KEY_BYTES) \
    field(private_key_len, size_t)
UJSON_SERDE_STRUCT(CryptotestX25519PrivateKey, cryptotest_x25519_private_key_t, X25519_PRIVATE_KEY);

#define X25519_PUBLIC_KEY(field, string) \
    field(public_key, uint8_t, X25519_CMD_PUBLIC_KEY_BYTES) \
    field(public_key_len, size_t)
UJSON_SERDE_STRUCT(CryptotestX25519PublicKey, cryptotest_x25519_public_key_t, X25519_PUBLIC_KEY);

#define X25519_DERIVE_OUTPUT(field, string) \
    field(result, bool) \
    field(shared_secret, uint8_t, X25519_CMD_SHARED_SECRET_BYTES) \
    field(shared_secret_len, size_t)
UJSON_SERDE_STRUCT(CryptotestX25519DeriveOutput, cryptotest_x25519_derive_output_t, X25519_DERIVE_OUTPUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_X25519_COMMANDS_H_
