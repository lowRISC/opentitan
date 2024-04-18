// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_I2C_TARGET_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_I2C_TARGET_H_

#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif
// clang-format off

#define MODULE_ID MAKE_MODULE_ID('j', 'i', 'i')

#define STRUCT_I2C_TARGET_ADDRESS(field, string) \
    field(instance, uint8_t) \
    field(id0, uint8_t) \
    field(mask0, uint8_t) \
    field(id1, uint8_t) \
    field(mask1, uint8_t)
UJSON_SERDE_STRUCT(I2cTargetAddress, i2c_target_address_t, STRUCT_I2C_TARGET_ADDRESS);

// Should be used to begin every I2C transfer.
// Issues a Start, address, command, and optional data and Stop conditions.
// A 0 data_len means there is no data.
#define STRUCT_I2C_TRANSFER_START(field, string) \
    field(length, uint8_t) \
    field(address, uint8_t) \
    field(stop, bool) \
    field(data, uint8_t, 256)
UJSON_SERDE_STRUCT(I2cTransferStart, i2c_transfer_start_t, STRUCT_I2C_TRANSFER_START);

// Should be used to set parameters for i2c tests.
#define STRUCT_I2C_TEST_CONFIG(field, string) \
    field(clock_stretching_delay_millis, uint32_t)
UJSON_SERDE_STRUCT(I2cTestConfig, i2c_test_config_t, STRUCT_I2C_TEST_CONFIG);

#undef MODULE_ID

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_I2C_TARGET_H_
