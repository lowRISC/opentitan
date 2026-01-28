// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_GDB_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_GDB_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define GDB_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, Try) \
    value(_, Switch) \
    value(_, If)
C_ONLY(UJSON_SERDE_ENUM(GdbSubcommand, gdb_subcommand_t, GDB_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(GdbSubcommand, gdb_subcommand_t, GDB_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define GDB_OUT(field, string) \
    field(err_status, uint32_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(ast_alerts, uint32_t, 2) \
    field(status, uint32_t) \
    field(result, bool)
UJSON_SERDE_STRUCT(GdbOut, gdb_out_t, GDB_OUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_GDB_COMMANDS_H_
