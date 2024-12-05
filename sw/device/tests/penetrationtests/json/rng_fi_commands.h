// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_RNG_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_RNG_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define RNGFI_SUBCOMMAND(_, value) \
    value(_, CsrngInit) \
    value(_, CsrngBias) \
    value(_, CsrngBiasFWOverride) \
    value(_, CsrngBiasFWOverrideStatic) \
    value(_, EdnInit) \
    value(_, EdnRespAck) \
    value(_, EdnBias) \
    value(_, FWOverride) \
    value(_, EntropySrcBias)
UJSON_SERDE_ENUM(RngFiSubcommand, rng_fi_subcommand_t, RNGFI_SUBCOMMAND);

#define CRYPTOFI_CSRNG_MODE(field, string) \
    field(start_trigger, bool) \
    field(valid_trigger, bool) \
    field(read_trigger, bool) \
    field(all_trigger, bool)
UJSON_SERDE_STRUCT(CryptoFiCsrngMode, crypto_fi_csrng_mode_t, CRYPTOFI_CSRNG_MODE);

#define RNGFI_CSRNG_OUTPUT(field, string) \
    field(res, uint32_t) \
    field(rand, uint32_t, 16) \
    field(alerts, uint32_t, 3) \
    field(err_status, uint32_t)
UJSON_SERDE_STRUCT(RngFiCsrngOutput, rng_fi_csrng_output_t, RNGFI_CSRNG_OUTPUT);

#define RNGFI_CSRNG_OV_OUTPUT(field, string) \
    field(res, uint32_t) \
    field(rand, uint32_t, 12) \
    field(alerts, uint32_t, 3) \
    field(err_status, uint32_t)
UJSON_SERDE_STRUCT(RngFiCsrngOvOutput, rng_fi_csrng_ov_output_t, RNGFI_CSRNG_OV_OUTPUT);

#define RNGFI_ENTRBIAS_OUTPUT(field, string) \
    field(rand, uint32_t, 32) \
    field(alerts, uint32_t, 3) \
    field(err_status, uint32_t)
UJSON_SERDE_STRUCT(RngFiEntrBiasOutput, rng_fi_entropy_src_bias_t, RNGFI_ENTRBIAS_OUTPUT);

#define RNGFI_FWOVERWRITE_OUTPUT(field, string) \
    field(rand, uint32_t, 32) \
    field(alerts, uint32_t, 3) \
    field(err_status, uint32_t)
UJSON_SERDE_STRUCT(RngFiFwOverwriteOutput, rng_fi_fw_overwrite_t, RNGFI_FWOVERWRITE_OUTPUT);

#define RNGFI_EDN(field, string) \
    field(collisions, uint32_t) \
    field(rand, uint32_t, 16) \
    field(alerts, uint32_t, 3) \
    field(err_status, uint32_t)
UJSON_SERDE_STRUCT(RngFiEdn, rng_fi_edn_t, RNGFI_EDN);

#define RNGFI_FWOVERWRITE_HEALTH(field, string) \
    field(disable_health_check, bool)
UJSON_SERDE_STRUCT(RngFiFwOverwriteHealt, rng_fi_fw_overwrite_health_t, RNGFI_FWOVERWRITE_HEALTH);

#define RNGFI_SEED(field, string) \
    field(seed, uint32_t, 12)
UJSON_SERDE_STRUCT(RngFiSeed, rng_fi_seed_t, RNGFI_SEED);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_RNG_FI_COMMANDS_H_
