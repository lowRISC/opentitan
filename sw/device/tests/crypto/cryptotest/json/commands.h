// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define COMMAND(_, value) \
    value(_, Aes) \
    value(_, Drbg) \
    value(_, Ecdsa) \
    value(_, Ecdh) \
    value(_, Hash) \
    value(_, Hmac) \
    value(_, Kmac) \
    value(_, AesSca) \
    value(_, ExtClkScaFi) \
    value(_, IbexFi) \
    value(_, KmacSca) \
    value(_, OtbnFi) \
    value(_, PrngSca) \
    value(_, Sha3Sca) \
    value(_, TriggerSca)
UJSON_SERDE_ENUM(CryptotestCommand, cryptotest_cmd_t, COMMAND);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_COMMANDS_H_
