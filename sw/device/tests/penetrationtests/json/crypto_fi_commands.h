// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTO_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTO_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define CRYPTOFI_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, Aes) \
    value(_, Kmac)
UJSON_SERDE_ENUM(CryptoFiSubcommand, crypto_fi_subcommand_t, CRYPTOFI_SUBCOMMAND);

#define CRYPTOFI_AES_MODE(field, string) \
    field(key_trigger, bool) \
    field(plaintext_trigger, bool) \
    field(encrypt_trigger, bool) \
    field(ciphertext_trigger, bool)
UJSON_SERDE_STRUCT(CryptoFiAesMode, crypto_fi_aes_mode_t, CRYPTOFI_AES_MODE);

#define CRYPTOFI_KMAC_MODE(field, string) \
    field(key_trigger, bool) \
    field(absorb_trigger, bool) \
    field(squeeze_trigger, bool)
UJSON_SERDE_STRUCT(CryptoFiKmacMode, crypto_fi_kmac_mode_t, CRYPTOFI_KMAC_MODE);

#define CRYPTOFI_AES_CIPHERTEXT(field, string) \
    field(ciphertext, uint8_t, 16) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(FiAesCiphertext, crypto_fi_aes_ciphertext_t, CRYPTOFI_AES_CIPHERTEXT);

#define CRYPTOFI_KMAC_DIGEST(field, string) \
    field(digest, uint8_t, 8) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(FiKmacDigest, crypto_fi_kmac_digest_t, CRYPTOFI_KMAC_DIGEST);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTO_FI_COMMANDS_H_
