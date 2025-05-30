// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTO_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTO_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define CRYPTOFI_HMAC_CMD_MAX_MESSAGE_BYTES 16
#define CRYPTOFI_HMAC_CMD_MAX_KEY_BYTES 32
#define CRYPTOFI_HMAC_CMD_MAX_TAG_WORDS 8

// clang-format off

#define CRYPTOFI_SUBCOMMAND(_, value) \
    value(_, Aes) \
    value(_, Init) \
    value(_, Kmac) \
    value(_, KmacState) \
    value(_, Sha256) \
    value(_, ShadowRegAccess) \
    value(_, ShadowRegRead)
C_ONLY(UJSON_SERDE_ENUM(CryptoFiSubcommand, crypto_fi_subcommand_t, CRYPTOFI_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(CryptoFiSubcommand, crypto_fi_subcommand_t, CRYPTOFI_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define CRYPTOFI_AES_MODE(field, string) \
    field(key_trigger, bool) \
    field(plaintext_trigger, bool) \
    field(encrypt_trigger, bool) \
    field(ciphertext_trigger, bool)
UJSON_SERDE_STRUCT(CryptoFiAesMode, crypto_fi_aes_mode_t, CRYPTOFI_AES_MODE);

#define CRYPTOFI_KMAC_MODE(field, string) \
    field(key_trigger, bool) \
    field(absorb_trigger, bool) \
    field(static_trigger, bool) \
    field(squeeze_trigger, bool)
UJSON_SERDE_STRUCT(CryptoFiKmacMode, crypto_fi_kmac_mode_t, CRYPTOFI_KMAC_MODE);

#define CRYPTOFI_AES_CIPHERTEXT(field, string) \
    field(ciphertext, uint8_t, 16) \
    field(alerts, uint32_t, 3) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(FiAesCiphertext, crypto_fi_aes_ciphertext_t, CRYPTOFI_AES_CIPHERTEXT);

#define CRYPTOFI_KMAC_STATE(field, string) \
    field(share0, uint8_t, 200) \
    field(share1, uint8_t, 200) \
    field(digest, uint8_t, 8) \
    field(alerts, uint32_t, 3) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(FiKmacState, crypto_fi_kmac_state_t, CRYPTOFI_KMAC_STATE);

#define CRYPTOFI_KMAC_DIGEST(field, string) \
    field(digest, uint8_t, 8) \
    field(digest_2nd, uint8_t, 8) \
    field(alerts, uint32_t, 3) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(FiKmacDigest, crypto_fi_kmac_digest_t, CRYPTOFI_KMAC_DIGEST);

#define CRYPTOFI_TEST_RESULT_MULT(field, string) \
    field(result, uint32_t, 3) \
    field(alerts, uint32_t, 3) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(CRYPTOFITestResultMult, crypto_fi_test_result_mult_t, CRYPTOFI_TEST_RESULT_MULT);

#define CRYPTOFI_HMAC_MESSAGE(field, string) \
    field(message, uint8_t, CRYPTOFI_HMAC_CMD_MAX_MESSAGE_BYTES)
UJSON_SERDE_STRUCT(FiHmacMessage, crypto_fi_hmac_message_t, CRYPTOFI_HMAC_MESSAGE);

#define CRYPTOFI_HMAC_TAG(field, string) \
    field(tag, uint32_t, CRYPTOFI_HMAC_CMD_MAX_TAG_WORDS) \
    field(alerts, uint32_t, 3) \
    field(err_status, uint32_t)
UJSON_SERDE_STRUCT(FiHmacTag, crypto_fi_hmac_tag_t, CRYPTOFI_HMAC_TAG);

#define CRYPTOFI_HMAC_MODE(field, string) \
    field(start_trigger, bool) \
    field(msg_trigger, bool) \
    field(process_trigger, bool) \
    field(finish_trigger, bool)
UJSON_SERDE_STRUCT(CryptoFiHmacMode, crypto_fi_hmac_mode_t, CRYPTOFI_HMAC_MODE);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTO_FI_COMMANDS_H_
