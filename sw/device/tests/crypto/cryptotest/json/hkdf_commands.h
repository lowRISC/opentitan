// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_HKDF_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_HKDF_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define MODULE_ID MAKE_MODULE_ID('j', 'h', 'k')

#define HKDF_CMD_MAX_IKM_BYTES 128
#define HKDF_CMD_MAX_SALT_BYTES 128
#define HKDF_CMD_MAX_INFO_BYTES 128
#define HKDF_CMD_MAX_OKM_BYTES 256

// clang-format off

#define HKDF_HASH_ALG(_, value) \
    value(_, Sha256) \
    value(_, Sha384) \
    value(_, Sha512)
UJSON_SERDE_ENUM(CryptotestHkdfHashAlg, cryptotest_hkdf_hash_alg_t, HKDF_HASH_ALG);

#define HKDF_DATA(field, string) \
    field(ikm, uint8_t, HKDF_CMD_MAX_IKM_BYTES) \
    field(ikm_len, size_t) \
    field(salt, uint8_t, HKDF_CMD_MAX_SALT_BYTES) \
    field(salt_len, size_t) \
    field(info, uint8_t, HKDF_CMD_MAX_INFO_BYTES) \
    field(info_len, size_t) \
    field(okm_len, size_t)
UJSON_SERDE_STRUCT(CryptotestHkdfData, cryptotest_hkdf_data_t, HKDF_DATA);

#define HKDF_OKM(field, string) \
    field(okm, uint8_t, HKDF_CMD_MAX_OKM_BYTES) \
    field(okm_len, size_t) \
    field(status_ok, bool)
UJSON_SERDE_STRUCT(CryptotestHkdfOkm, cryptotest_hkdf_okm_t, HKDF_OKM);

#undef MODULE_ID

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_HKDF_COMMANDS_H_
