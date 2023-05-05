// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_I2C_TARGET_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_I2C_TARGET_H_

#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif
// clang-format off

#define STRUCT_I2C_TARGET_ADDRESS(field, string) \
    field(id0, uint8_t) \
    field(mask0, uint8_t) \
    field(id1, uint8_t) \
    field(mask1, uint8_t)
UJSON_SERDE_STRUCT(I2cTargetAddress, i2c_target_address_t, STRUCT_I2C_TARGET_ADDRESS);

#define STRUCT_I2C_TRANSACTION(field, string) \
    field(length, uint16_t) \
    field(data, uint8_t, 256)
UJSON_SERDE_STRUCT(I2cTransaction, i2c_transaction_t, STRUCT_I2C_TARGET_ADDRESS);

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_I2C_TARGET_H_
