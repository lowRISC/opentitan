// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define CRYPTOLIBFI_SUBCOMMAND(_, value) \
    value(_, Init)
C_ONLY(UJSON_SERDE_ENUM(CryptoLibFiSubcommand, cryptolib_fi_subcommand_t, CRYPTOLIBFI_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(CryptoLibFiSubcommand, cryptolib_fi_subcommand_t, CRYPTOLIBFI_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_CRYPTOLIB_FI_COMMANDS_H_
