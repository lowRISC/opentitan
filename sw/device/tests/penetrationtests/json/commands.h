// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define COMMAND(_, value) \
    value(_, AesSca) \
    value(_, ExtClkScaFi) \
    value(_, IbexFi) \
    value(_, IbexSca) \
    value(_, KmacSca) \
    value(_, LCCtrlFi) \
    value(_, OtbnFi) \
    value(_, PrngSca) \
    value(_, RngFi) \
    value(_, Sha3Sca) \
    value(_, TriggerSca)
UJSON_SERDE_ENUM(PenetrationtestCommand, penetrationtest_cmd_t, COMMAND);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_COMMANDS_H_
