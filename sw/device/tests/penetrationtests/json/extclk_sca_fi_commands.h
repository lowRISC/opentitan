// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_EXTCLK_SCA_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_EXTCLK_SCA_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

// EXTCLK SCA FI arguments

#define EXTCLK_SCA_FI_SUBCOMMAND(_, value) \
    value(_, Configure)
UJSON_SERDE_ENUM(ExtClkScaFiSubcommand, extclk_sca_fi_subcommand_t, EXTCLK_SCA_FI_SUBCOMMAND);

#define EXTCLK_SCA_FI_CFG(field, string) \
    field(sel, bool) \
    field(hi_speed_sel, bool)
UJSON_SERDE_STRUCT(PenetrationtestExtClkScaFiCfg, penetrationtest_extclk_sca_fi_cfg_t, EXTCLK_SCA_FI_CFG);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_EXTCLK_SCA_FI_COMMANDS_H_
