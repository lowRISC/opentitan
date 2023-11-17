// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_PRNG_SCA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_PRNG_SCA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define PRNGSCA_CMD_MAX_LFSR_BYTES 4

// clang-format off

// PRNG SCA arguments

#define PRNGSCA_SUBCOMMAND(_, value) \
    value(_, SeedPrng)
UJSON_SERDE_ENUM(PrngScaSubcommand, prng_sca_subcommand_t, PRNGSCA_SUBCOMMAND);

#define PRNG_SCA_LFSR(field, string) \
    field(seed, uint8_t, PRNGSCA_CMD_MAX_LFSR_BYTES) \
    field(seed_length, size_t)
UJSON_SERDE_STRUCT(CryptotestPrngScaLfsr, cryptotest_prng_sca_lfsr_t, PRNG_SCA_LFSR);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_PRNG_SCA_COMMANDS_H_
