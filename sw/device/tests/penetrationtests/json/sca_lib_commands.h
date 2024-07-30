// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_SCA_LIB_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_SCA_LIB_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define PENETRATIONTEST_DEVICE_ID(field, string) \
    field(device_id, uint32_t, 8)
UJSON_SERDE_STRUCT(PenetrationtestDeviceId, penetrationtest_device_id_t, PENETRATIONTEST_DEVICE_ID);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_SCA_LIB_COMMANDS_H_
