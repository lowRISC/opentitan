// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_OTBN_SCA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_OTBN_SCA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define OTBNSCA_CMD_MAX_APP_SELECT_BYTES 1
#define OTBNSCA_CMD_MAX_EN_MASKS_BYTES 1
#define OTBNSCA_CMD_MAX_NUM_TRACES_BYTES 4
#define OTBNSCA_CMD_MAX_BATCH_DIGEST_BYTES 40
#define OTBNSCA_CMD_MAX_MASK_BYTES 40
#define OTBNSCA_CMD_MAX_CONSTANT_BYTES 40
#define OTBNSCA_CMD_MAX_ECC_SEED_BYTES 40
#define OTBNSCA_CMD_MAX_ECC_COORD_BYTES 32
#define OTBNSCA_CMD_MAX_SEED_BYTES 40
#define OTBNSCA_CMD_MAX_K_BYTES 80
#define OTBNSCA_CMD_MAX_ALPHA_INV_BYTES 32
#define OTBNSCA_CMD_MAX_ALPHA_BYTES 16

// clang-format off

// OTBN SCA arguments

#define OTBNSCA_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, Ecc256EcdsaKeygenFvsrSeedBatch) \
    value(_, Ecc256EcdsaKeygenFvsrKeyBatch) \
    value(_, Ecc256EcdsaSecretKeygen) \
    value(_, Ecc256EcdsaGenKeypair) \
    value(_, Ecc256SetSeed) \
    value(_, Ecc256SetC) \
    value(_, Ecc256EnMasks) \
    value(_, Ecc256AppSelect) \
    value(_, Ecc256Modinv)
UJSON_SERDE_ENUM(OtbnScaSubcommand, otbn_sca_subcommand_t, OTBNSCA_SUBCOMMAND);

#define OTBN_SCA_EN_MASKS(field, string) \
    field(en_masks, uint8_t, OTBNSCA_CMD_MAX_EN_MASKS_BYTES)
UJSON_SERDE_STRUCT(CryptotestOtbnScaEnMasks, cryptotest_otbn_sca_en_masks_t, OTBN_SCA_EN_MASKS);

#define OTBN_SCA_APP_SELECT(field, string) \
    field(app, uint8_t, OTBNSCA_CMD_MAX_APP_SELECT_BYTES)
UJSON_SERDE_STRUCT(CryptotestOtbnScaAppSelect, cryptotest_otbn_sca_app_select_t, OTBN_SCA_APP_SELECT);

#define OTBN_SCA_NUM_TRACES(field, string) \
    field(num_traces, uint8_t, OTBNSCA_CMD_MAX_NUM_TRACES_BYTES)
UJSON_SERDE_STRUCT(CryptotestOtbnScaNumTraces, cryptotest_otbn_sca_num_traces_t, OTBN_SCA_NUM_TRACES);

#define OTBN_SCA_BATCH_DIGEST(field, string) \
    field(batch_digest, uint8_t, OTBNSCA_CMD_MAX_BATCH_DIGEST_BYTES)
UJSON_SERDE_STRUCT(CryptotestOtbnScaBatchDigest, cryptotest_otbn_sca_batch_digest_t, OTBN_SCA_BATCH_DIGEST);

#define OTBN_SCA_ECC_SEED_D0(field, string) \
    field(d0, uint8_t, OTBNSCA_CMD_MAX_ECC_SEED_BYTES / 2)
UJSON_SERDE_STRUCT(CryptotestOtbnScaEccSeedD0, cryptotest_otbn_sca_ecc_seed_d0_t, OTBN_SCA_ECC_SEED_D0);

#define OTBN_SCA_ECC_SEED_D1(field, string) \
    field(d1, uint8_t, OTBNSCA_CMD_MAX_ECC_SEED_BYTES / 2)
UJSON_SERDE_STRUCT(CryptotestOtbnScaEccSeedD1, cryptotest_otbn_sca_ecc_seed_d1_t, OTBN_SCA_ECC_SEED_D1);

#define OTBN_SCA_ECC_SEED(field, string) \
    field(d0, uint8_t, OTBNSCA_CMD_MAX_ECC_SEED_BYTES) \
    field(d1, uint8_t, OTBNSCA_CMD_MAX_ECC_SEED_BYTES)
UJSON_SERDE_STRUCT(CryptotestOtbnScaEccSeed, cryptotest_otbn_sca_ecc_seed_t, OTBN_SCA_ECC_SEED);

#define OTBN_SCA_ECC_COORD(field, string) \
    field(x, uint8_t, OTBNSCA_CMD_MAX_ECC_COORD_BYTES) \
    field(y, uint8_t, OTBNSCA_CMD_MAX_ECC_COORD_BYTES)
UJSON_SERDE_STRUCT(CryptotestOtbnScaEccCoord, cryptotest_otbn_sca_ecc_coord_t, OTBN_SCA_ECC_COORD);

#define OTBN_SCA_ALPHA(field, string) \
    field(alpha_inv, uint8_t, OTBNSCA_CMD_MAX_ALPHA_INV_BYTES) \
    field(alpha, uint8_t, OTBNSCA_CMD_MAX_ALPHA_BYTES)
UJSON_SERDE_STRUCT(CryptotestOtbnScaAlpha, cryptotest_otbn_sca_alpha_t, OTBN_SCA_ALPHA);

#define OTBN_SCA_MASK(field, string) \
    field(mask, uint8_t, OTBNSCA_CMD_MAX_MASK_BYTES)
UJSON_SERDE_STRUCT(CryptotestOtbnScaMask, cryptotest_otbn_sca_mask_t, OTBN_SCA_MASK);

#define OTBN_SCA_K(field, string) \
    field(k, uint8_t, OTBNSCA_CMD_MAX_K_BYTES) \
    field(k_len, size_t)
UJSON_SERDE_STRUCT(CryptotestOtbnScaK, cryptotest_otbn_sca_k_t, OTBN_SCA_K);

#define OTBN_SCA_SEED(field, string) \
    field(seed, uint8_t, OTBNSCA_CMD_MAX_SEED_BYTES)
UJSON_SERDE_STRUCT(CryptotestOtbnScaSeed, cryptotest_otbn_sca_seed_t, OTBN_SCA_SEED);

#define OTBN_SCA_CONSTANT(field, string) \
    field(constant, uint8_t, OTBNSCA_CMD_MAX_CONSTANT_BYTES) \
    field(constant_len, size_t)
UJSON_SERDE_STRUCT(CryptotestOtbnScaConstant, cryptotest_otbn_sca_constant_t, OTBN_SCA_CONSTANT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_OTBN_SCA_COMMANDS_H_
