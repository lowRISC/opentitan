// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_IBEX_SCA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_IBEX_SCA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define IBEXSCA_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, KeySideloading) \
    value(_, RFRead) \
    value(_, RFReadBatchFvsr) \
    value(_, RFReadBatchRandom) \
    value(_, RFWrite) \
    value(_, RFWriteBatchFvsr) \
    value(_, RFWriteBatchRandom) \
    value(_, TLRead) \
    value(_, TLReadBatchFvsr) \
    value(_, TLReadBatchFvsrFixAddress) \
    value(_, TLReadBatchRandom) \
    value(_, TLReadBatchRandomFixAddress) \
    value(_, TLWrite) \
    value(_, TLWriteBatchFvsr) \
    value(_, TLWriteBatchFvsrFixAddress) \
    value(_, TLWriteBatchRandom) \
    value(_, TLWriteBatchRandomFixAddress)
UJSON_SERDE_ENUM(IbexScaSubcommand, ibex_sca_subcommand_t, IBEXSCA_SUBCOMMAND);

#define IBEXSCA_TEST_DATA(field, string) \
    field(data, uint32_t, 8)
UJSON_SERDE_STRUCT(IbexScaTestData, ibex_sca_test_data_t, IBEXSCA_TEST_DATA);

#define IBEXSCA_SALT(field, string) \
    field(salt, uint32_t, 8)
UJSON_SERDE_STRUCT(IbexScaSalt, ibex_sca_salt_t, IBEXSCA_SALT);

#define IBEXSCA_KEY(field, string) \
    field(share0, uint32_t, 8) \
    field(share1, uint32_t, 8)
UJSON_SERDE_STRUCT(IbexScaKey, ibex_sca_key_t, IBEXSCA_KEY);

#define IBEXSCA_TEST_FVSR(field, string) \
    field(num_iterations, uint32_t) \
    field(fixed_data, uint32_t)
UJSON_SERDE_STRUCT(IbexScaTestFvsr, ibex_sca_test_fvsr_t, IBEXSCA_TEST_FVSR);

#define IBEXSCA_RESULT(field, string) \
    field(result, uint32_t)
UJSON_SERDE_STRUCT(IbexScaResult, ibex_sca_result_t, IBEXSCA_RESULT);

#define IBEXSCA_BATCH(field, string) \
    field(num_iterations, uint32_t)
UJSON_SERDE_STRUCT(IbexScaBatch, ibex_sca_batch_t, IBEXSCA_BATCH);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_IBEX_SCA_COMMANDS_H_
