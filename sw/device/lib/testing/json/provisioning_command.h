// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PROVISIONING_COMMAND_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PROVISIONING_COMMAND_H_

#include "sw/device/lib/ujson/ujson_derive.h"

#ifdef __cplusplus
extern "C" {
#endif
// clang-format off

#define ENUM_CP_PROVISIONING_COMMAND(_, value) \
    value(_, EraseAndWriteAll) \
    value(_, FlashInfoEraseDeviceIdAndManufState) \
    value(_, FlashInfoWriteDeviceIdAndManufState) \
    value(_, FlashInfoEraseWaferAuthSecret) \
    value(_, FlashInfoWriteWaferAuthSecret) \
    value(_, OtpSecret0WriteAndLock) \
    value(_, Done)
UJSON_SERDE_ENUM(CpProvisioningCommand, cp_provisioning_command_t, ENUM_CP_PROVISIONING_COMMAND);

#define ENUM_FT_SRAM_PROVISIONING_COMMAND(_, value) \
    value(_, OtpCreatorSwCfgWrite) \
    value(_, OtpOwnerSwCfgWrite) \
    value(_, OtpHwCfgWrite) \
    value(_, WriteAll) \
    value(_, Done)
UJSON_SERDE_ENUM(FtSramProvisioningCommand, ft_sram_provisioning_command_t, ENUM_FT_SRAM_PROVISIONING_COMMAND);

#define ENUM_FT_PERSONALIZE_COMMAND(_, value) \
    value(_, Done)
UJSON_SERDE_ENUM(FtPersonalizeCommand, ft_personalize_command_t, ENUM_FT_PERSONALIZE_COMMAND);

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PROVISIONING_COMMAND_H_
