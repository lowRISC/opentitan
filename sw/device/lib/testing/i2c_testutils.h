// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_I2C_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_I2C_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
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
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_write(const dif_i2c_t *i2c, uint8_t addr,
                             uint8_t byte_count, const uint8_t *data,
                             bool skip_stop);

/**
 * Construct and issue an I2C read transaction as an I2C host.
 *
 * @param i2c An I2C DIF handle.
 * @param addr The device address for the transaction.
 * @param byte_count The number of bytes to be read.
 * @return kOk(nak) Where nak indicates whether the device acknowledged the read
 * transaction (false) or not (true), otherwise an error.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_issue_read(const dif_i2c_t *i2c, uint8_t addr,
                                  uint8_t byte_count);

/**
 * Check that the target I2C device received the start of a transaction.
 *
 * @param i2c An I2C DIF handle.
 * @param[out] addr The address that was used for the transaction.
 * @return kOk(dir) Where dir indicates the direction of transaction is signaled
 * as Read(1) and not Write(0), or an error.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_target_check_start(const dif_i2c_t *i2c, uint8_t *addr);

/**
 * Check that the target I2C device received the end of a transaction.
 *
 * @param i2c An I2C DIF handle.
 * @param[out] cont_byte The contents of the acquired restart byte if host has
 *                       signaled a repeated START, can be null if test doesn't
 *                       accept a repeated start.
 * @return kOk(dir) Where dir indicates that repeated start has signaled that
 * the transaction should continue and the contents of cont_byte are valid, or
 * an error.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_target_check_end(const dif_i2c_t *i2c,
                                        uint8_t *cont_byte);

/**
 * Prepare for, and respond to, an I2C read as an I2C device.
 *
 * @param i2c An I2C DIF handle.
 * @param byte_count The number of bytes to be read.
 * @param data Array of data bytes to be sent.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_target_read(const dif_i2c_t *i2c, uint8_t byte_count,
                                   const uint8_t *data);

/**
 * Check completion of an I2C read as an I2C device.
 *
 * @param i2c An I2C DIF handle.
 * @param[out] addr Address that received the I2C read.
 * @param[out] cont_byte received continuation byte. Can be null if test
 *                       expects STOP signal.
 * @return kOk(dir) Where dir indicates that repeated start has signaled that
 * the transaction should continue and the contents of cont_byte are valid, or
 * an error.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_target_check_read(const dif_i2c_t *i2c, uint8_t *addr,
                                         uint8_t *cont_byte);

/**
 * Prepare for an I2C write as an I2C device.
 *
 * @param i2c A I2C DIF handle.
 * @param byte_count The number of bytes to be written.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_target_write(const dif_i2c_t *i2c, uint8_t byte_count);

/**
 * Check completion of an I2C write as an I2C device.
 *
 * @param i2c A I2C DIF handle.
 * @param byte_count The number of bytes to be written.
 * @param[out] addr Address that received the I2C write.
 * @param[out] bytes Array of bytes to stores the result of the write.
 * @param[out] cont_byte Received continuation byte. Can be null if test expects
 *                       STOP signal.
 * @return kOk(dir) Where dir indicates that repeated START has signaled that
 * the transaction should continue and the contents of cont_byte are valid, or
 * an error.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_target_check_write(const dif_i2c_t *i2c,
                                          uint8_t byte_count, uint8_t *addr,
                                          uint8_t *bytes, uint8_t *cont_byte);

/**
 * Define the available platforms which i2c is mapped
 */
typedef enum i2c_pinmux_platform_id {
  I2cPinmuxPlatformIdHyper310 = 0,
  I2cPinmuxPlatformIdDvsim,
  I2cPinmuxPlatformIdCw310Pmod,
  I2cPinmuxPlatformIdCount,
} i2c_pinmux_platform_id_t;

/**
 * Connect the i2c pins to mio pins via pinmux based on the platform the test is
 * running.
 *
 * @param pimmux A pinmux handler.
 * @param kI2cIdx The i2c instance identifier.
 * @param platform The platform which the test is running.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_select_pinmux(const dif_pinmux_t *pinmux,
                                     uint8_t kI2cIdx,
                                     i2c_pinmux_platform_id_t platform);

/**
 * Disconnect the i2c input pins from mio pads and wire it to zero.
 *
 * @param pimmux A pinmux handler.
 * @param i2c_id The i2c instance identifier.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_detach_pinmux(const dif_pinmux_t *pinmux,
                                     uint8_t i2c_id);
/**
 * Return whether the fifo is empty.
 *
 * @param i2c An I2C DIF handle.
 * @return `kOk(dir)` Where `dir` is true if the fifo is empty. Or an error.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_fifo_empty(const dif_i2c_t *i2c);

/**
 * Issue an i2c read transaction, check for a nak and retry until timeout in
 * case of nak or read the fifo in case of ack.
 *
 * @param i2c  An I2C DIF handle.
 * @param addr The device address for the transaction.
 * @param byte_count The number of bytes to be read.
 * @param[out] data Buffer to receive the fifo data.
 * @param timeout Timeout in microseconds.
 * @return Return an error code if fails to read, otherwise `kOk(nak_count)`,
 * where `nak_count` is the number of NAKs received or attempts needed before
 * the success`.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_read(const dif_i2c_t *i2c, uint8_t addr,
                            uint8_t byte_count, uint8_t *data, size_t timeout);

/**
 * Set the i2c timing parameters based on the desired speed mode.
 *
 * @param i2c An I2C DIF handle.
 * @param speed The speed mode.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_set_speed(const dif_i2c_t *i2c, dif_i2c_speed_t speed);

/**
 * Busy spin until the i2c host get idle.
 *
 * @param i2c An I2C DIF handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t i2c_testutils_wait_host_idle(const dif_i2c_t *i2c);

/**
 * Busy spin until the fmt_fifo gets empty meaning that it has finished the all
 * the transactions issued.
 *
 * @param i2c An I2C DIF handle.
 * @return The result of the operation.
 */
status_t i2c_testutils_wait_transaction_finish(const dif_i2c_t *i2c);
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_I2C_TESTUTILS_H_
