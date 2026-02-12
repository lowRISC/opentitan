// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_SCA_SYM_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_SCA_SYM_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define MODULE_ID MAKE_MODULE_ID('j', 's', 's')

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

// clang-format off

#define CRYPTOLIBSCASYM_SUBCOMMAND(_, value) \
    value(_, AesFvsrPlaintext) \
    value(_, AesFvsrKey) \
    value(_, AesDaisy) \
    value(_, CmacFvsrPlaintext) \
    value(_, CmacFvsrKey) \
    value(_, CmacDaisy) \
    value(_, GcmFvsrPlaintext) \
    value(_, GcmFvsrKey) \
    value(_, GcmDaisy) \
    value(_, TdesFvsrPlaintext) \
    value(_, TdesFvsrKey) \
    value(_, TdesDaisy) \
    value(_, HmacFvsrPlaintext) \
    value(_, HmacFvsrKey) \
    value(_, HmacDaisy) \
    value(_, DrbgGenerateBatch) \
    value(_, DrbgReseed) \
    value(_, Init)
C_ONLY(UJSON_SERDE_ENUM(CryptoLibScaSymSubcommand, cryptolib_sca_sym_subcommand_t, CRYPTOLIBSCASYM_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(CryptoLibScaSymSubcommand, cryptolib_sca_sym_subcommand_t, CRYPTOLIBSCASYM_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define CRYPTOLIBSCASYM_AES_IN(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(op_enc, bool) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymAesIn, cryptolib_sca_sym_aes_in_t, CRYPTOLIBSCASYM_AES_IN);

#define CRYPTOLIBSCASYM_AES_OUT(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymAesOut, cryptolib_sca_sym_aes_out_t, CRYPTOLIBSCASYM_AES_OUT);

#define CRYPTOLIBSCASYM_CMAC_IN(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymCmacIn, cryptolib_sca_sym_cmac_in_t, CRYPTOLIBSCASYM_CMAC_IN);

#define CRYPTOLIBSCASYM_CMAC_OUT(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymCmacOut, cryptolib_sca_sym_cmac_out_t, CRYPTOLIBSCASYM_CMAC_OUT);

#define CRYPTOLIBSCASYM_GCM_IN(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(aad, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(aad_len, size_t) \
    field(key, uint8_t, AES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, AES_CMD_MAX_BLOCK_BYTES) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymGcmIn, cryptolib_sca_sym_gcm_in_t, CRYPTOLIBSCASYM_GCM_IN);

#define CRYPTOLIBSCASYM_GCM_OUT(field, string) \
    field(data, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(data_len, uint32_t) \
    field(tag, uint8_t, AES_CMD_MAX_MSG_BYTES) \
    field(tag_len, uint32_t) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymGcmOut, cryptolib_sca_sym_gcm_out_t, CRYPTOLIBSCASYM_GCM_OUT);

#define CRYPTOLIBSCASYM_TDES_IN(field, string) \
    field(data, uint8_t, TDES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, TDES_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(iv, uint8_t, TDES_CMD_MAX_BLOCK_BYTES) \
    field(padding, size_t) \
    field(mode, size_t) \
    field(op_enc, bool) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymTdesIn, cryptolib_sca_sym_tdes_in_t, CRYPTOLIBSCASYM_TDES_IN);

#define CRYPTOLIBSCASYM_TDES_OUT(field, string) \
    field(data, uint8_t, TDES_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymTdesOut, cryptolib_sca_sym_tdes_out_t, CRYPTOLIBSCASYM_TDES_OUT);

#define CRYPTOLIBSCASYM_HMAC_IN(field, string) \
    field(data, uint8_t, HMAC_CMD_MAX_MSG_BYTES) \
    field(data_len, size_t) \
    field(key, uint8_t, HMAC_CMD_MAX_KEY_BYTES) \
    field(key_len, size_t) \
    field(hash_mode, size_t) \
    field(mode, size_t) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymHmacIn, cryptolib_sca_sym_hmac_in_t, CRYPTOLIBSCASYM_HMAC_IN);

#define CRYPTOLIBSCASYM_HMAC_OUT(field, string) \
    field(data, uint8_t, HMAC_CMD_MAX_TAG_BYTES) \
    field(data_len, size_t) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymHmacOut, cryptolib_sca_sym_hmac_out_t, CRYPTOLIBSCASYM_HMAC_OUT);

#define CRYPTOLIBSCASYM_DRBG_GENERATE_IN(field, string) \
    field(data_len, size_t) \
    field(nonce, uint8_t, DRBG_CMD_MAX_NONCE_BYTES) \
    field(nonce_len, size_t) \
    field(mode, size_t) \
    field(cfg, size_t) \
    field(num_iterations, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymDrbgGenerateIn, cryptolib_sca_sym_drbg_generate_in_t, CRYPTOLIBSCASYM_DRBG_GENERATE_IN);

#define CRYPTOLIBSCASYM_DRBG_RESEED_IN(field, string) \
    field(entropy, uint8_t, DRBG_CMD_MAX_ENTROPY_BYTES) \
    field(entropy_len, size_t) \
    field(nonce, uint8_t, DRBG_CMD_MAX_NONCE_BYTES) \
    field(nonce_len, size_t) \
    field(reseed_interval, size_t) \
    field(mode, size_t) \
    field(cfg, size_t) \
    field(trigger, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymDrbgReseedIn, cryptolib_sca_sym_drbg_reseed_in_t, CRYPTOLIBSCASYM_DRBG_RESEED_IN);

#define CRYPTOLIBSCASYM_DRBG_GENERATE_OUT(field, string) \
    field(data, uint8_t, DRBG_CMD_MAX_OUTPUT_BYTES) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymDrbgGenerateOut, cryptolib_sca_sym_drbg_generate_out_t, CRYPTOLIBSCASYM_DRBG_GENERATE_OUT);

#define CRYPTOLIBSCASYM_DRBG_RESEED_OUT(field, string) \
    field(status, size_t) \
    field(cfg, size_t)
UJSON_SERDE_STRUCT(CryptoLibScaSymDrbgReseedOut, cryptolib_sca_sym_drbg_reseed_out_t, CRYPTOLIBSCASYM_DRBG_RESEED_OUT);

#undef MODULE_ID

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_SCA_SYM_COMMANDS_H_
