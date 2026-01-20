// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_FI_SYM_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_FI_SYM_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define AES_CMD_MAX_MSG_BYTES 64
#define AES_CMD_MAX_KEY_BYTES 32
#define AES_CMD_MAX_BLOCK_BYTES 16

#define TDES_CMD_MAX_MSG_BYTES 64
#define TDES_CMD_MAX_KEY_BYTES 21
#define TDES_CMD_MAX_BLOCK_BYTES 8

#define HMAC_CMD_MAX_MSG_BYTES 64
#define HMAC_CMD_MAX_KEY_BYTES 192
#define HMAC_CMD_MAX_TAG_BYTES 64

#define DRBG_CMD_MAX_ENTROPY_BYTES 32
#define DRBG_CMD_MAX_NONCE_BYTES 16
#define DRBG_CMD_MAX_OUTPUT_BYTES 256

#define TRNG_CMD_MAX_OUTPUT_BYTES 4

// clang-format off

#define CRYPTOLIBFISYM_SUBCOMMAND(_, value) \
    value(_, Aes) \
    value(_, Cmac) \
    value(_, Gcm) \
    value(_, Tdes) \
    value(_, Hmac) \
    value(_, DrbgGenerate) \
    value(_, DrbgReseed) \
    value(_, TrngGenerate) \
    value(_, TrngInit) \
    value(_, Init)
C_ONLY(UJSON_SERDE_ENUM(CryptoLibFiSymSubcommand, cryptolib_fi_sym_subcommand_t, CRYPTOLIBFISYM_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(CryptoLibFiSymSubcommand, cryptolib_fi_sym_subcommand_t, CRYPTOLIBFISYM_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define CRYPTOLIBFISYM_AES_IN(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(op_enc, bool) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymAesIn, cryptolib_fi_sym_aes_in_t, CRYPTOLIBFISYM_AES_IN);

#define CRYPTOLIBFISYM_AES_OUT(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymAesOut, cryptolib_fi_sym_aes_out_t, CRYPTOLIBFISYM_AES_OUT);

#define CRYPTOLIBFISYM_CMAC_IN(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymCmacIn, cryptolib_fi_sym_cmac_in_t, CRYPTOLIBFISYM_CMAC_IN);

#define CRYPTOLIBFISYM_CMAC_OUT(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymCmacOut, cryptolib_fi_sym_cmac_out_t, CRYPTOLIBFISYM_CMAC_OUT);

#define CRYPTOLIBFISYM_GCM_IN(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(aad, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(aad_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(tag, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(tag_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymGcmIn, cryptolib_fi_sym_gcm_in_t, CRYPTOLIBFISYM_GCM_IN);

#define CRYPTOLIBFISYM_GCM_OUT(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(tag, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(tag_len, size_t) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymGcmOut, cryptolib_fi_sym_gcm_out_t, CRYPTOLIBFISYM_GCM_OUT);

#define CRYPTOLIBFISYM_TDES_IN(field, string) \
    field(data, uint8_t, TDES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, TDES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, TDES_CMD_MAX_BLOCK_BYTES) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(op_enc, bool) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymTdesIn, cryptolib_fi_sym_tdes_in_t, CRYPTOLIBFISYM_TDES_IN);

#define CRYPTOLIBFISYM_TDES_OUT(field, string) \
    field(data, uint8_t, TDES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymTdesOut, cryptolib_fi_sym_tdes_out_t, CRYPTOLIBFISYM_TDES_OUT);

#define CRYPTOLIBFISYM_HMAC_IN(field, string) \
    field(data, uint8_t, HMAC_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, HMAC_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(hash_mode, size_t) \
    field(mode, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymHmacIn, cryptolib_fi_sym_hmac_in_t, CRYPTOLIBFISYM_HMAC_IN);

#define CRYPTOLIBFISYM_HMAC_OUT(field, string) \
    field(data, uint8_t, HMAC_CMD_MAX_TAG_BYTES) \
    field(data_len, size_t) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymHmacOut, cryptolib_fi_sym_hmac_out_t, CRYPTOLIBFISYM_HMAC_OUT);

#define CRYPTOLIBFISYM_DRBG_GENERATE_IN(field, string) \
    field(nonce, uint8_t, DRBG_CMD_MAX_NONCE_BYTES) \
    field(nonce_len, size_t) \
    field(data_len, size_t) \
    field(mode, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymDrbgGenerateIn, cryptolib_fi_sym_drbg_generate_in_t, CRYPTOLIBFISYM_DRBG_GENERATE_IN);

#define CRYPTOLIBFISYM_DRBG_RESEED_IN(field, string) \
    field(entropy, uint8_t, DRBG_CMD_MAX_ENTROPY_BYTES) \
    field(entropy_len, size_t) \
    field(nonce, uint8_t, DRBG_CMD_MAX_NONCE_BYTES) \
    field(nonce_len, size_t) \
    field(reseed_interval, size_t) \
    field(mode, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymDrbgReseedIn, cryptolib_fi_sym_drbg_reseed_in_t, CRYPTOLIBFISYM_DRBG_RESEED_IN);

#define CRYPTOLIBFISYM_DRBG_GENERATE_OUT(field, string) \
    field(data, uint8_t, DRBG_CMD_MAX_OUTPUT_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymDrbgGenerateOut, cryptolib_fi_sym_drbg_generate_out_t, CRYPTOLIBFISYM_DRBG_GENERATE_OUT);

#define CRYPTOLIBFISYM_DRBG_RESEED_OUT(field, string) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymDrbgReseedOut, cryptolib_fi_sym_drbg_reseed_out_t, CRYPTOLIBFISYM_DRBG_RESEED_OUT);

#define CRYPTOLIBFISYM_TRNG_GENERATE_IN(field, string) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymTrngGenerateIn, cryptolib_fi_sym_trng_generate_in_t, CRYPTOLIBFISYM_TRNG_GENERATE_IN);

#define CRYPTOLIBFISYM_TRNG_INIT_IN(field, string) \
    field(mode, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymTrngInitIn, cryptolib_fi_sym_trng_init_in_t, CRYPTOLIBFISYM_TRNG_INIT_IN);

#define CRYPTOLIBFISYM_TRNG_GENERATE_OUT(field, string) \
    field(data, uint8_t, TRNG_CMD_MAX_OUTPUT_BYTES) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymTrngGenerateOut, cryptolib_fi_sym_trng_generate_out_t, CRYPTOLIBFISYM_TRNG_GENERATE_OUT);

#define CRYPTOLIBFISYM_TRNG_INIT_OUT(field, string) \
    field(status, size_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(err_status, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibFiSymTrngInitOut, cryptolib_fi_sym_trng_init_out_t, CRYPTOLIBFISYM_TRNG_INIT_OUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_FI_SYM_COMMANDS_H_
