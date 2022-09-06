// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_I2C_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_I2C_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_i2c.h"

/**
 * Construct an i2c write.
 *
 * @param i2c A i2c dif handle.
 * @param addr The device address for the transaction.
 * @param byte_count The number of bytes to be written.
 * @param data Stream of data bytes to be written.
 * @param skip_stop Skip the stop bit as this may be chained with a read.
 */
void i2c_testutils_wr(dif_i2c_t *i2c, uint8_t addr, uint8_t byte_count,
                      uint8_t *data, bool skip_stop);

/**
 * Construct an i2c read
 *
 * @param i2c A i2c dif handle.
 * @param addr The device address for the transaction.
 * @param byte_count The number of bytes to be read.
 */
void i2c_testutils_rd(dif_i2c_t *i2c, uint8_t addr, uint8_t byte_count);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_I2C_TESTUTILS_H_
