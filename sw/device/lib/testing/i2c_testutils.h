// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_I2C_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_I2C_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_pinmux.h"

/**
 * Construct an I2C write as an I2C host.
 *
 * @param i2c An I2C DIF handle.
 * @param addr The device address for the transaction.
 * @param byte_count The number of bytes to be written.
 * @param data Stream of data bytes to be written.
 * @param skip_stop Skip the stop bit as this may be chained with a read.
 */
void i2c_testutils_wr(const dif_i2c_t *i2c, uint8_t addr, uint8_t byte_count,
                      const uint8_t *data, bool skip_stop);

/**
 * Construct an I2C read as an I2C host.
 *
 * @param i2c An I2C DIF handle.
 * @param addr The device address for the transaction.
 * @param byte_count The number of bytes to be read.
 * @return The result of the operation.
 */
status_t i2c_testutils_rd(const dif_i2c_t *i2c, uint8_t addr,
                          uint8_t byte_count);

/**
 * Check that the target I2C device received the start of a transaction.
 *
 * @param i2c An I2C DIF handle.
 * @param[out] addr The address that was used for the transaction.
 * @return Direction of transaction is signaled as Read and not Write.
 */
bool i2c_testutils_target_check_start(const dif_i2c_t *i2c, uint8_t *addr);

/**
 * Check that the target I2C device received the end of a transaction.
 *
 * @param i2c An I2C DIF handle.
 * @param[out] cont_byte The contents of the acquired restart byte if host has
 *                       signaled a repeated START, can be null if test doesn't
 *                       accept a repeated start.
 * @return Repeated start has signaled that the transaction should continue and
 *         the contents of cont_byte are valid.
 */
bool i2c_testutils_target_check_end(const dif_i2c_t *i2c, uint8_t *cont_byte);

/**
 * Prepare for, and respond to, an I2C read as an I2C device.
 *
 * @param i2c An I2C DIF handle.
 * @param byte_count The number of bytes to be read.
 * @param data Array of data bytes to be sent.
 * @return The result of the operation.
 */
status_t i2c_testutils_target_rd(const dif_i2c_t *i2c, uint8_t byte_count,
                                 const uint8_t *data);

/**
 * Check completion of an I2C read as an I2C device.
 *
 * @param i2c An I2C DIF handle.
 * @param[out] addr Address that received the I2C read.
 * @param[out] cont_byte received continuation byte. Can be null if test
 *                       expects STOP signal.
 * @return Repeated start has signaled that the transaction should continue and
 *         the contents of cont_byte are valid.
 */
bool i2c_testutils_target_check_rd(const dif_i2c_t *i2c, uint8_t *addr,
                                   uint8_t *cont_byte);

/**
 * Prepare for an I2C write as an I2C device.
 *
 * @param i2c A I2C DIF handle.
 * @param byte_count The number of bytes to be written.
 */
void i2c_testutils_target_wr(const dif_i2c_t *i2c, uint8_t byte_count);

/**
 * Check completion of an I2C write as an I2C device.
 *
 * @param i2c A I2C DIF handle.
 * @param byte_count The number of bytes to be written.
 * @param[out] addr Address that received the I2C write.
 * @param[out] bytes Array of bytes to store the result of the write.
 * @param[out] cont_byte Received continuation byte. Can be null if test expects
 *                       STOP signal.
 * @return Repeated START has signaled that the transaction should continue and
 *         the contents of cont_byte are valid.
 */
bool i2c_testutils_target_check_wr(const dif_i2c_t *i2c, uint8_t byte_count,
                                   uint8_t *addr, uint8_t *bytes,
                                   uint8_t *cont_byte);

/**
 * Initialize the pinmux.
 */
void i2c_testutils_connect_i2c_to_pinmux_pins(const dif_pinmux_t *pinmux,
                                              uint8_t kI2cIdx);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_I2C_TESTUTILS_H_
