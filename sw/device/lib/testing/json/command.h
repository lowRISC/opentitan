// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_COMMAND_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_COMMAND_H_

#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif
// clang-format off

#define ENUM_TEST_COMMAND(_, value) \
    value(_, ChipStartup) \
    value(_, GpioSet) \
    value(_, GpioGet) \
    value(_, PinmuxConfig)
UJSON_SERDE_ENUM(TestCommand, test_command_t, ENUM_TEST_COMMAND);

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_COMMAND_H_
