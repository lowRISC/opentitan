// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_EDN_SCA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_EDN_SCA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define EDNSCA_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, BusData) \
    value(_, BusDataBatch)
C_ONLY(UJSON_SERDE_ENUM(EdnScaSubcommand, edn_sca_subcommand_t, EDNSCA_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(EdnScaSubcommand, edn_sca_subcommand_t, EDNSCA_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define EDNSCA_RESULT(field, string) \
    field(rnd_data, uint32_t, 4)
UJSON_SERDE_STRUCT(EdnScaResult, edn_sca_result_t, EDNSCA_RESULT);

#define EDNSCA_BATCH(field, string) \
    field(num_iterations, uint32_t)
UJSON_SERDE_STRUCT(EdnScaBatch, edn_sca_batch_t, EDNSCA_BATCH);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_EDN_SCA_COMMANDS_H_
