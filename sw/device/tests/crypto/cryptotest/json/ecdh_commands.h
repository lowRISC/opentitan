// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_ECDH_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_ECDH_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define ECDH_CMD_MAX_PRIVATE_KEY_BYTES 48
#define ECDH_CMD_MAX_SHARED_SECRET_BYTES 48
#define ECDH_CMD_MAX_COORDINATE_BYTES 48
#define ECDH_CMD_MAX_PRIVATE_KEY_SHARE_BYTES 64

// clang-format off

#define ECDH_CURVE(_, value) \
    value(_, P256) \
    value(_, P384)
UJSON_SERDE_ENUM(CryptotestEcdhCurve, cryptotest_ecdh_curve_t, ECDH_CURVE);

#define ECDH_PRIVATE_KEY(field, string) \
    field(d0, uint8_t, ECDH_CMD_MAX_PRIVATE_KEY_SHARE_BYTES) \
    field(d0_len, size_t) \
    field(d1, uint8_t, ECDH_CMD_MAX_PRIVATE_KEY_SHARE_BYTES) \
    field(d1_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEcdhPrivateKey, cryptotest_ecdh_private_key_t, ECDH_PRIVATE_KEY);

#define ECDH_COORDINATE(field, string) \
    field(coordinate, uint8_t, ECDH_CMD_MAX_COORDINATE_BYTES) \
    field(coordinate_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEcdhCoordinate, cryptotest_ecdh_coordinate_t, ECDH_COORDINATE);

#define ECDH_DERIVE_OUTPUT(field, string) \
    field(ok, uint8_t) \
    field(shared_secret, uint8_t, ECDH_CMD_MAX_SHARED_SECRET_BYTES) \
    field(shared_secret_len, size_t)
UJSON_SERDE_STRUCT(CryptotestEcdhDeriveOutput, cryptotest_ecdh_derive_output_t, ECDH_DERIVE_OUTPUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_ECDH_COMMANDS_H_
