// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_EDN_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_EDN_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define EDNFI_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, BusData) \
    value(_, BusAck)
UJSON_SERDE_ENUM(EdnFiSubcommand, edn_fi_subcommand_t, EDNFI_SUBCOMMAND);

#define EDNFI_TEST_RESULT(field, string) \
    field(result, uint32_t) \
    field(err_status, uint32_t)
UJSON_SERDE_STRUCT(EdnFiTestResult, edn_fi_test_result_t, EDNFI_TEST_RESULT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_EDN_FI_COMMANDS_H_
