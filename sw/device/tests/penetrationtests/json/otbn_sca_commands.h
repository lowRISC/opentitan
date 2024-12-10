// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_OTBN_SCA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_OTBN_SCA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define OTBNSCA_CMD_MAX_BATCH_DIGEST_BYTES 40
#define OTBNSCA_CMD_MAX_SEED_BYTES 40

// clang-format off

// OTBN SCA arguments

#define OTBNSCA_SUBCOMMAND(_, value) \
    value(_, Ecc256EcdsaKeygenFvsrKeyBatch) \
    value(_, Ecc256EcdsaKeygenFvsrSeedBatch) \
    value(_, Ecc256EnMasks) \
    value(_, Ecc256SetC) \
    value(_, Ecc256SetSeed) \
    value(_, Init) \
    value(_, InitKeyMgr) \
    value(_, KeySideloadFvsr) \
    value(_, Rsa512Decrypt)
UJSON_SERDE_ENUM(OtbnScaSubcommand, otbn_sca_subcommand_t, OTBNSCA_SUBCOMMAND);

#define OTBN_SCA_EN_MASKS(field, string) \
    field(en_masks, bool)
UJSON_SERDE_STRUCT(PenetrationtestOtbnScaEnMasks, penetrationtest_otbn_sca_en_masks_t, OTBN_SCA_EN_MASKS);

#define OTBN_SCA_NUM_TRACES(field, string) \
    field(num_traces, uint32_t)
UJSON_SERDE_STRUCT(PenetrationtestOtbnScaNumTraces, penetrationtest_otbn_sca_num_traces_t, OTBN_SCA_NUM_TRACES);

#define OTBN_SCA_BATCH_DIGEST(field, string) \
    field(batch_digest, uint8_t, OTBNSCA_CMD_MAX_BATCH_DIGEST_BYTES)
UJSON_SERDE_STRUCT(PenetrationtestOtbnScaBatchDigest, penetrationtest_otbn_sca_batch_digest_t, OTBN_SCA_BATCH_DIGEST);

#define OTBN_SCA_SEED(field, string) \
    field(seed, uint8_t, OTBNSCA_CMD_MAX_SEED_BYTES)
UJSON_SERDE_STRUCT(PenetrationtestOtbnScaSeed, penetrationtest_otbn_sca_seed_t, OTBN_SCA_SEED);

#define OTBN_SCA_CONSTANT(field, string) \
    field(constant, uint8_t, OTBNSCA_CMD_MAX_SEED_BYTES)
UJSON_SERDE_STRUCT(PenetrationtestOtbnScaConstant, penetrationtest_otbn_sca_constant_t, OTBN_SCA_CONSTANT);

#define OTBN_SCA_KEY(field, string) \
    field(shares, uint32_t, 4) \
    field(keys, uint32_t, 2)
UJSON_SERDE_STRUCT(PenetrationtestOtbnScaKey, penetrationtest_otbn_sca_key_t, OTBN_SCA_KEY);

#define OTBN_SCA_FIXED_SEED(field, string) \
    field(fixed_seed, uint32_t)
UJSON_SERDE_STRUCT(PenetrationtestOtbnScaFixedKey, penetrationtest_otbn_sca_fixed_seed_t, OTBN_SCA_FIXED_SEED);

#define OTBN_SCA_RSA512_DEC(field, string) \
    field(mod, uint8_t, 64) \
    field(exp, uint8_t, 64) \
    field(msg, uint8_t, 64)
UJSON_SERDE_STRUCT(PenetrationtestOtbnScaRsa512Dec, penetrationtest_otbn_sca_rsa512_dec_t, OTBN_SCA_RSA512_DEC);

#define OTBN_SCA_RSA512_DEC_OUT(field, string) \
    field(out, uint8_t, 64)
UJSON_SERDE_STRUCT(PenetrationtestOtbnScaRsa512DecOut, penetrationtest_otbn_sca_rsa512_dec_out_t, OTBN_SCA_RSA512_DEC_OUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_OTBN_SCA_COMMANDS_H_
