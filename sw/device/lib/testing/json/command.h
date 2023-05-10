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
    value(_, EnterNormalSleep) \
    value(_, EnterDeepSleep) \
    value(_, I2cTargetAddress) \
    value(_, I2cReadTransaction) \
    value(_, I2cWriteTransaction) \
    value(_, I2cWriteTransactionSlow) \
    value(_, PinmuxConfig) \
    value(_, SpiConfigureJedecId) \
    value(_, SpiReadStatus) \
    value(_, SpiWaitForUpload) \
    value(_, SpiWriteStatus) \
    value(_, SpiWriteSfdp) \
    value(_, SpiFlashReadId) \
    value(_, SpiFlashReadSfdp) \
    value(_, SpiFlashEraseSector) \
    value(_, SpiFlashEmulator) \
    value(_, SpiFlashWrite) \
    value(_, SpiMailboxMap) \
    value(_, SpiMailboxUnmap) \
    value(_, SpiMailboxWrite) \
    value(_, SpiPassthruSetAddressMap) \
    value(_, SwStrapRead)
UJSON_SERDE_ENUM(TestCommand, test_command_t, ENUM_TEST_COMMAND);

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_COMMAND_H_
