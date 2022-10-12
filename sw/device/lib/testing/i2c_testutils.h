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

/**
 * Check that the i2c target received the start of a transaction
 *
 * @param i2c A i2c dif handle.
 * @param [out] addr The address that was used for the transaction.
 * @return read Direction of transaction is signaled as Read and not Write
 */
bool i2c_testutils_target_check_start(dif_i2c_t *i2c, uint8_t *addr);

/**
 * Check that the i2c target received the end of a transaction
 *
 * @param i2c A i2c dif handle.
 * @param cont_byte The contents of the acquired restart byte if host has
 * signaled a repeated START, can be null if test
 * doesn't accept a repeated start
 * @return continue
 */
bool i2c_testutils_target_check_end(dif_i2c_t *i2c, uint8_t *cont_byte);

/**
 * Prepare for and respond to an I2C read as a target device
 *
 * @param i2c A i2c dif handle.
 * @param byte_count The number of bytes to be read.
 * @param data Array of data bytes to be sent.
 */
void i2c_testutils_target_rd(dif_i2c_t *i2c, uint8_t byte_count, uint8_t *data);

/**
 * Check completion of an I2C read as a target device
 *
 * @param i2c A i2c dif handle.
 * @param [out] addr Address that received the i2c read.
 * @param [out] cont_byte received continuation byte. Can be null if test
 * expects STOP signal.
 * @return continue Repeated start has signaled that the transaction should
 * continue and the contents of cont_byte are valid.
 */
bool i2c_testutils_target_check_rd(dif_i2c_t *i2c, uint8_t *addr,
                                   uint8_t *cont_byte);

/**
 * Prepare for an I2C write as a target device
 *
 * @param i2c A i2c dif handle.
 * @param byte_count The number of bytes to be written.
 */
void i2c_testutils_target_wr(dif_i2c_t *i2c, uint8_t byte_count);

/**
 * Check completion of an I2C write as a target device
 *
 * @param i2c A i2c dif handle.
 * @param byte_count The number of bytes to be written.
 * @param [out] addr Address that received the i2c write.
 * @param bytes Array of bytes to store the result of the write
 * @param cont_byte received continuation byte. Can be null if test expects STOP
 * signal.
 * @return continue Repeated START has signaled that the transaction should
 * continue and the contents of cont_byte are valid.
 */
bool i2c_testutils_target_check_wr(dif_i2c_t *i2c, uint8_t byte_count,
                                   uint8_t *addr, uint8_t *bytes,
                                   uint8_t *cont_byte);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_I2C_TESTUTILS_H_
