// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_TRIGGER_SCA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_TRIGGER_SCA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define TRIGGERSCA_CMD_MAX_SOURCE_BYTES 1

// clang-format off

// TRIGGER SCA arguments

#define TRIGGERSCA_SUBCOMMAND(_, value) \
    value(_, SelectTriggerSource)
UJSON_SERDE_ENUM(TriggerScaSubcommand, trigger_sca_subcommand_t, TRIGGERSCA_SUBCOMMAND);

#define TRIGGER_SCA_SOURCE(field, string) \
    field(source, uint8_t)
UJSON_SERDE_STRUCT(CryptotestTriggerScaSource, cryptotest_trigger_sca_source_t, TRIGGER_SCA_SOURCE);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_TRIGGER_SCA_COMMANDS_H_
