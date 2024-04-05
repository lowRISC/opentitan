// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_OTBN_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_OTBN_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define OTBNFI_SUBCOMMAND(_, value) \
    value(_, InitKeyMgr) \
    value(_, Init) \
    value(_, CharUnrolledRegOpLoop) \
    value(_, CharUnrolledDmemOpLoop) \
    value(_, CharHardwareRegOpLoop) \
    value(_, CharHardwareDmemOpLoop) \
    value(_, LoadIntegrity) \
    value(_, KeySideload)
UJSON_SERDE_ENUM(OtbnFiSubcommand, otbn_fi_subcommand_t, OTBNFI_SUBCOMMAND);

#define OTBNFI_LOOP_COUNTER_OUTPUT(field, string) \
    field(loop_counter, uint32_t) \
    field(err_status, uint32_t) \
    field(alerts, uint32_t)
UJSON_SERDE_STRUCT(OtbnFiLoopCounterOutput, otbn_fi_loop_counter_t, OTBNFI_LOOP_COUNTER_OUTPUT);

#define OTBNFI_RESULT_OUTPUT(field, string) \
    field(result, uint32_t) \
    field(err_status, uint32_t)
UJSON_SERDE_STRUCT(OtbnFiResultOutput, otbn_fi_result_t, OTBNFI_RESULT_OUTPUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_JSON_OTBN_FI_COMMANDS_H_
