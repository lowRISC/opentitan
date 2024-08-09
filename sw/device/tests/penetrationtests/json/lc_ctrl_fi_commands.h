// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_LC_CTRL_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_LC_CTRL_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define LCCTRLFI_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, RuntimeCorruption)
UJSON_SERDE_ENUM(LcCtrlFiSubcommand, lc_ctrl_fi_subcommand_t, LCCTRLFI_SUBCOMMAND);

#define LCCTRLFI_CORRUPTION(field, string) \
    field(res, uint32_t) \
    field(state, uint32_t) \
    field(counter, uint32_t) \
    field(alerts, uint32_t, 3) \
    field(err_status, uint32_t)
UJSON_SERDE_STRUCT(LcCtrlFiCorruption, lc_ctrl_fi_corruption_t, LCCTRLFI_CORRUPTION);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_LC_CTRL_FI_COMMANDS_H_
