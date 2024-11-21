// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_OTBN_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_OTBN_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define OTBNFI_SUBCOMMAND(_, value) \
    value(_, CharDmemAccess) \
    value(_, CharHardwareDmemOpLoop) \
    value(_, CharHardwareRegOpLoop) \
    value(_, CharJal) \
    value(_, CharMem) \
    value(_, CharRF) \
    value(_, CharUnrolledDmemOpLoop) \
    value(_, CharUnrolledRegOpLoop) \
    value(_, Init) \
    value(_, InitKeyMgr) \
    value(_, KeySideload)  \
    value(_, LoadIntegrity)
UJSON_SERDE_ENUM(OtbnFiSubcommand, otbn_fi_subcommand_t, OTBNFI_SUBCOMMAND);

#define OTBNFI_LOOP_COUNTER_OUTPUT(field, string) \
    field(loop_counter, uint32_t) \
    field(err_otbn, uint32_t) \
    field(err_ibx, uint32_t) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(OtbnFiLoopCounterOutput, otbn_fi_loop_counter_t, OTBNFI_LOOP_COUNTER_OUTPUT);

#define OTBNFI_RESULT_OUTPUT(field, string) \
    field(result, uint32_t) \
    field(err_otbn, uint32_t) \
    field(err_ibx, uint32_t) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(OtbnFiResultOutput, otbn_fi_result_t, OTBNFI_RESULT_OUTPUT);

#define OTBNFI_KEY_OUTPUT(field, string) \
    field(res, uint32_t) \
    field(keys, uint32_t, 4) \
    field(err_otbn, uint32_t) \
    field(err_ibx, uint32_t) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(OtbnFiKeyOutput, otbn_fi_keys_t, OTBNFI_KEY_OUTPUT);

#define OTBNFI_MEM_CFG(field, string) \
    field(byte_offset, uint32_t) \
    field(num_words, uint32_t) \
    field(imem, bool) \
    field(dmem, bool)
UJSON_SERDE_STRUCT(OtbnFiMemCfg, otbn_fi_mem_cfg_t, OTBNFI_MEM_CFG);

#define OTBNFI_MEM_OUTPUT(field, string) \
    field(res, uint32_t) \
    field(imem_data, uint32_t, 8) \
    field(imem_addr, uint32_t, 8) \
    field(dmem_data, uint32_t, 8) \
    field(dmem_addr, uint32_t, 8) \
    field(err_otbn, uint32_t) \
    field(err_ibx, uint32_t) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(OtbnFiMemOutput, otbn_fi_mem_t, OTBNFI_MEM_OUTPUT);

#define OTBNFI_DATA_OUTPUT(field, string) \
    field(res, uint32_t) \
    field(data, uint32_t, 256) \
    field(insn_cnt, uint32_t) \
    field(err_otbn, uint32_t) \
    field(err_ibx, uint32_t) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(OtbnFiDataOutput, otbn_fi_data_t, OTBNFI_DATA_OUTPUT);

#define OTBNFI_RF_CHAR_OUTPUT(field, string) \
    field(res, uint32_t) \
    field(faulty_gpr, uint32_t, 29) \
    field(faulty_wdr, uint32_t, 256) \
    field(err_otbn, uint32_t) \
    field(err_ibx, uint32_t) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(OtbnFiRfCharOutput, otbn_fi_rf_char_t, OTBNFI_RF_CHAR_OUTPUT);

#define OTBNFI_RESULT_CNT_OUTPUT(field, string) \
    field(result, uint32_t) \
    field(insn_cnt, uint32_t) \
    field(err_otbn, uint32_t) \
    field(err_ibx, uint32_t) \
    field(alerts, uint32_t, 3)
UJSON_SERDE_STRUCT(OtbnFiResultCntOutput, otbn_fi_result_cnt_t, OTBNFI_RESULT_CNT_OUTPUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_OTBN_FI_COMMANDS_H_
