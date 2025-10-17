// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_RSA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_RSA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define MODULE_ID MAKE_MODULE_ID('r', 'a', 's')

#define RSA_CMD_MAX_MESSAGE_BYTES 512
#define RSA_CMD_MAX_N_BYTES 512
#define RSA_CMD_MAX_SIGNATURE_BYTES 512

// clang-format off

#define RSA_SUBCOMMAND(_, value) \
    value(_, RsaVerify)
UJSON_SERDE_ENUM(RsaSubcommand, rsa_subcommand_t, RSA_SUBCOMMAND);

#define RSA_VERIFY(field, string) \
    field(msg, uint8_t, RSA_CMD_MAX_MESSAGE_BYTES) \
    field(msg_len, size_t) \
    field(e, uint32_t) \
    field(n, uint8_t, RSA_CMD_MAX_N_BYTES) \
    field(security_level, size_t) \
    field(sig, uint8_t, RSA_CMD_MAX_SIGNATURE_BYTES) \
    field(sig_len, size_t) \
    field(hashing, size_t) \
    field(padding, size_t)
UJSON_SERDE_STRUCT(CryptotestRsaVerify, cryptotest_rsa_verify_t, RSA_VERIFY);

#define RSA_VERIFY_RESP(field, string) \
    field(result, bool)
UJSON_SERDE_STRUCT(CryptotestRsaVerifyResp, cryptotest_rsa_verify_resp_t, RSA_VERIFY_RESP);

#undef MODULE_ID

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_RSA_COMMANDS_H_
