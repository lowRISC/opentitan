// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_IBEX_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_IBEX_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define IBEXFI_NUM_REGS 32
#define IBEXFI_SRAM_WORDS 64
#define IBEXFI_MAX_FAULTY_ADDRESSES_DATA 13
#define IBEXFI_MAX_RESULT_ARRAY 12

// clang-format off

#define IBEXFI_SUBCOMMAND(_, value) \
    value(_, AddressTranslation) \
    value(_, AddressTranslationCfg) \
    value(_, CharAddiSingleBeq) \
    value(_, CharAddiSingleBeqCm) \
    value(_, CharAddiSingleBeqNeg) \
    value(_, CharAddiSingleBne) \
    value(_, CharAddiSingleBneNeg) \
    value(_, CharCondBranchBeq) \
    value(_, CharCondBranchBge) \
    value(_, CharCondBranchBgeu) \
    value(_, CharCondBranchBlt) \
    value(_, CharCondBranchBltu) \
    value(_, CharCondBranchBne) \
    value(_, CharCsrRead) \
    value(_, CharCsrWrite) \
    value(_, CharFlashRead) \
    value(_, CharFlashWrite) \
    value(_, CharHardenedCheckComplementBranch) \
    value(_, CharHardenedCheckUnimp) \
    value(_, CharHardenedCheck2Unimps) \
    value(_, CharHardenedCheck3Unimps) \
    value(_, CharHardenedCheck4Unimps) \
    value(_, CharHardenedCheck5Unimps) \
    value(_, CharMemOpLoop) \
    value(_, CharRegisterFile) \
    value(_, CharRegisterFileRead) \
    value(_, CharRegOpLoop) \
    value(_, CharSingleBeq) \
    value(_, CharSingleBne) \
    value(_, CharSramRead) \
    value(_, CharSramStatic) \
    value(_, CharSramWrite) \
    value(_, CharSramWriteRead) \
    value(_, CharSramWriteStaticUnrolled) \
    value(_, CharUncondBranch) \
    value(_, CharUncondBranchNop) \
    value(_, CharUnrolledMemOpLoop) \
    value(_, CharUnrolledRegOpLoop) \
    value(_, CharUnrolledRegOpLoopChain) \
    value(_, Init) \
    value(_, OtpDataRead) \
    value(_, OtpReadLock) \
    value(_, OtpWriteLock)
C_ONLY(UJSON_SERDE_ENUM(IbexFiSubcommand, ibex_fi_subcommand_t, IBEXFI_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(IbexFiSubcommand, ibex_fi_subcommand_t, IBEXFI_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define IBEXFI_TEST_RESULT(field, string) \
    field(result, uint32_t) \
    field(registers, uint32_t, IBEXFI_NUM_REGS) \
    field(err_status, uint32_t) \
    field(alerts, uint32_t, 3) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(IbexFiTestResult, ibex_fi_test_result_t, IBEXFI_TEST_RESULT);

#define IBEXFI_TEST_RESULT_ARRAY(field, string) \
    field(result, uint32_t, IBEXFI_MAX_RESULT_ARRAY) \
    field(registers, uint32_t, IBEXFI_NUM_REGS) \
    field(err_status, uint32_t) \
    field(alerts, uint32_t, 3) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(IbexFiTestResultArray, ibex_fi_test_result_array_t, IBEXFI_TEST_RESULT_ARRAY);

#define IBEXFI_TEST_RESULT_SRAM(field, string) \
    field(memory, uint32_t, IBEXFI_SRAM_WORDS) \
    field(registers, uint32_t, IBEXFI_NUM_REGS) \
    field(err_status, uint32_t) \
    field(alerts, uint32_t, 3) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(IbexFiTestResultSram, ibex_fi_test_result_sram_t, IBEXFI_TEST_RESULT_SRAM);

#define IBEXFI_TEST_RESULT_MULT(field, string) \
    field(result1, uint32_t) \
    field(result2, uint32_t) \
    field(err_status, uint32_t) \
    field(alerts, uint32_t, 3) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(IbexFiTestResultMult, ibex_fi_test_result_mult_t, IBEXFI_TEST_RESULT_MULT);

#define IBEXFI_FAULTY_DATA(field, string) \
    field(err_status, uint32_t) \
    field(registers, uint32_t, IBEXFI_NUM_REGS) \
    field(data_faulty, bool, IBEXFI_MAX_FAULTY_ADDRESSES_DATA) \
    field(data, uint32_t, IBEXFI_MAX_FAULTY_ADDRESSES_DATA) \
    field(alerts, uint32_t, 3) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(IbexFiFaultyData, ibex_fi_faulty_data_t, IBEXFI_FAULTY_DATA);

#define IBEXFI_FAULTY_ADDRESS_DATA(field, string) \
    field(err_status, uint32_t) \
    field(registers, uint32_t, IBEXFI_NUM_REGS) \
    field(addresses, uint32_t, IBEXFI_MAX_FAULTY_ADDRESSES_DATA) \
    field(data, uint32_t, IBEXFI_MAX_FAULTY_ADDRESSES_DATA) \
    field(alerts, uint32_t, 3) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(IbexFiFaultyAddressData, ibex_fi_faulty_addresses_data_t, IBEXFI_FAULTY_ADDRESS_DATA);

#define IBEXFI_RF_DUMP(field, string) \
    field(registers, uint32_t, IBEXFI_NUM_REGS) \
    field(err_status, uint32_t) \
    field(alerts, uint32_t, 3) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(IbexFiRfDump, ibex_fi_rf_dump_t, IBEXFI_RF_DUMP);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_IBEX_FI_COMMANDS_H_
