// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_ALERT_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_ALERT_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

// AES SCA arguments

#define ALERT_FI_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, Trigger) \
    value(_, SensorCtrlTrigger) \
    value(_, IbexSwFatal)
C_ONLY(UJSON_SERDE_ENUM(AlertFiSubcommand, alert_fi_subcommand_t, ALERT_FI_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(AlertFiSubcommand, alert_fi_subcommand_t, ALERT_FI_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define ALERT_FI_TRIGGER(field, string) \
    field(alert, uint32_t)
UJSON_SERDE_STRUCT(AlertFiTrigger, alert_fi_trigger_t, ALERT_FI_TRIGGER);

#define ALERT_FI_ALERT_OUT(field, string) \
    field(err_status, uint32_t) \
    field(alerts, uint32_t, 3) \
    field(loc_alerts, uint32_t) \
    field(ast_alerts, uint32_t, 2)
UJSON_SERDE_STRUCT(AlertFiAlertOut, alert_fi_alert_out_t, ALERT_FI_ALERT_OUT);

#define ALERT_FI_EMPTY_OUT(field, string) \
    field(success, bool)
UJSON_SERDE_STRUCT(AlertFiEmptyOut, alert_fi_empty_out_t, ALERT_FI_EMPTY_OUT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_ALERT_FI_COMMANDS_H_
