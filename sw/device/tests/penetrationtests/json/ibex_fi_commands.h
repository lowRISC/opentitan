// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_IBEX_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_IBEX_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define IBEXFI_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, CharUnrolledRegOpLoop) \
    value(_, CharRegOpLoop) \
    value(_, CharUnrolledMemOpLoop) \
    value(_, CharMemOpLoop) \
    value(_, CharRegisterFile) \
    value(_, CharRegisterFileRead) \
    value(_, CharCondBranch) \
    value(_, CharUncondBranch) \
    value(_, CharSramWrite) \
    value(_, CharSramWriteStatic) \
    value(_, CharSramRead) \
    value(_, CharSramStatic) \
    value(_, CharFlashWrite) \
    value(_, CharFlashRead) \
    value(_, CharCsrRead) \
    value(_, CharCsrWrite) \
    value(_, AddressTranslationCfg) \
    value(_, AddressTranslation)
UJSON_SERDE_ENUM(IbexFiSubcommand, ibex_fi_subcommand_t, IBEXFI_SUBCOMMAND);

#define IBEXFI_TEST_RESULT(field, string) \
    field(result, uint32_t) \
    field(err_status, uint32_t) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(IbexFiTestResult, ibex_fi_test_result_t, IBEXFI_TEST_RESULT);

#define IBEXFI_TEST_RESULT_MULT(field, string) \
    field(result1, uint32_t) \
    field(result2, uint32_t) \
    field(err_status, uint32_t) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(IbexFiTestResultMult, ibex_fi_test_result_mult_t, IBEXFI_TEST_RESULT_MULT);

#define IBEXFI_LOOP_COUNTER_OUTPUT(field, string) \
    field(loop_counter, uint32_t) \
    field(err_status, uint32_t) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(IbexFiLoopCounterOutput, ibex_fi_loop_counter_t, IBEXFI_LOOP_COUNTER_OUTPUT);

#define IBEXFI_LOOP_COUNTER_MIRRORED_OUTPUT(field, string) \
    field(loop_counter1, uint32_t) \
    field(loop_counter2, uint32_t) \
    field(err_status, uint32_t) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(IbexFiLoopCounterMirroredOutput, ibex_fi_loop_counter_mirrored_t, IBEXFI_LOOP_COUNTER_MIRRORED_OUTPUT);

#define IBEXFI_FAULTY_ADDRESSES(field, string) \
    field(err_status, uint32_t) \
    field(addresses, uint32_t, 8) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(IbexFiFaultyAddresses, ibex_fi_faulty_addresses_t, IBEXFI_FAULTY_ADDRESSES);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_IBEX_FI_COMMANDS_H_
