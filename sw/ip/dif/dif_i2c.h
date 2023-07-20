// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_I2C_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_I2C_H_

/**
 * @file
 * @brief <a href="/hw/ip/i2c/doc/">I2C</a> Device Interface Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_i2c_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Represents a speed setting for an I2C component: standard, fast, and
 * fast plus, corresponding to 100 kbaud, 400 kbaud, and 1 Mbaud,
 * respectively.
 */
typedef enum dif_i2c_speed {
  /**
   * Standard speed, 100 kilobaud.
   */
  kDifI2cSpeedStandard,
  /**
   * Fast speed, 400 kilobaud.
   */
  kDifI2cSpeedFast,
  /**
   * Fast plus speed, 1 megabaud.
   */
  kDifI2cSpeedFastPlus,
} dif_i2c_speed_t;

/**
 * Timing configuration parameters for I2C.
 *
 * While the I2C device requires ten parameters to describe its timing
 * configuration, the degrees of freedom of those parameters is constrained to
 * the ones in this struct.
 *
 * See `dif_i2c_compute_timing()`
 */
typedef struct dif_i2c_timing_config {
  /**
   * The lowest speed at which an I2C target connected to this host will
   * operate.
   *
   * In other words, this is the maximum speed at which the host can operate
   * without going over what the target devices can handle.
   */
  dif_i2c_speed_t lowest_target_device_speed;
  /**
   * The period of the clock driving this device, in nanoseconds.
   *
   * This value should not be zero, since it is used as a divisor for
   * division.
   */
  uint32_t clock_period_nanos;
  /**
   * The expected time it takes for the I2C bus signal to rise, in nanoseconds.
   *
   * This value is dependent on properties of the hardware's interconnect, and
   * not under actual firmware control.
   */
  uint32_t sda_rise_nanos;
  /**
   * The expected time for the bus signal to fall, similar to `sda_rise_nanos`.
   */
  uint32_t sda_fall_nanos;
  /**
   * The desired period of the SCL line, in nanoseconds.
   *
   * Normally, this should just be `1'000'000 / lowest_target_device_speed`,
   * but the period may be larger if desired.
   *
   * Setting this value to zero will result in the minimum period being used.
   */
  uint32_t scl_period_nanos;
} dif_i2c_timing_config_t;

/**
 * Configuration for the addressing behavior of the I2C, can be disabled or
 * configured to look for multiple addresses by masking certain bits. A mask of
 * 0x7f will match only a single address.
 */
typedef struct dif_i2c_id {
  /**
   * Mask the recieved I2C address before checking for a match. Received Address
   * & mask must equal the programmed address to activate I2C Device. If Address
   * & ~mask != 0, this will not match any addresses. A mask of 0x7f will cause
   * device to only respond to an exact match. The mask is 7 bits and LSB
   * aligned.
   */
  uint8_t mask;
  /**
   * The 7-bit I2C address that should be matched after masking to cause the
   * activated I2C Target device to begin to act in a transaction. Address is
   * LSB aligned.
   */
  uint8_t address;
} dif_i2c_id_t;

/**
 * Runtime configuration for I2C.
 *
 * This struct describes runtime timing parameters. Computing these values is
 * somewhat complicated, so these fields should be initialized using the
 * `dif_i2c_compute_timing()` function. A caller is, however, free to compute
 * these values themselves if they prefer, so long as the I2C spec is
 * respected.
 *
 * These values correspond to those in Table 10 of the I2C spec, and are given
 * in units of input clock cycles.
 */
typedef struct dif_i2c_config {
  uint16_t scl_time_high_cycles;
  uint16_t scl_time_low_cycles;
  uint16_t rise_cycles;
  uint16_t fall_cycles;
  uint16_t start_signal_setup_cycles;
  uint16_t start_signal_hold_cycles;
  uint16_t data_signal_setup_cycles;
  uint16_t data_signal_hold_cycles;
  uint16_t stop_signal_setup_cycles;
  /**
   * This parameter is referred to in the I2C documents as the
   * "bus free time".
   */
  uint16_t stop_signal_hold_cycles;
} dif_i2c_config_t;

/**
 * Represents a valid watermark level for one of the I2C FIFOs.
 */
typedef enum dif_i2c_watermark_level {
  /**
   * A one-byte watermark.
   */
  kDifI2cLevel1Byte = 0,
  /**
   * A four-byte watermark.
   */
  kDifI2cLevel4Byte,
  /**
   * An eight-byte watermark.
   */
  kDifI2cLevel8Byte,
  /**
   * A sixteen-byte watermark.
   */
  kDifI2cLevel16Byte,
  /**
   * A thirty-byte watermark.
   *
   * Note that this watermark is only supported for RX, and not for FMT.
   */
  kDifI2cLevel30Byte,
} dif_i2c_level_t;

/**
 * Flags for a formatted I2C byte, used by the `dif_i2c_write_byte_raw()`
 * function.
 */
typedef struct dif_i2c_fmt_flags {
  /**
   * Causes a start signal to be sent before the byte.
   *
   * If a start has been issued during the current transaction, this will issue
   * a repeated start.
   */
  bool start;
  /**
   * Causes a stop signal to be sent after the byte.
   *
   * This flag cannot be set when both `read` and `read_cont` are set.
   */
  bool stop;
  /**
   * Causes the byte to be interpreted as an unsigned number of bytes to read
   * from the target; 0 is interpreted as 256.
   */
  bool read;
  /**
   * Requires `read` to be set; if so, once the final byte associated with this
   * read is received, it will be acknowledged, allowing the read operation to
   * continue.
   */
  bool read_cont;
  /**
   * By default, the hardware expects an ACK after every byte sent, and raises
   * an exception (surfaced as the `kDifi2cIrqNak` interrupt). This flag
   * disables that behavior.
   *
   * This flag cannot be set along with `read` or `read_cont`.
   */
  bool suppress_nak_irq;
} dif_i2c_fmt_flags_t;

/**
 * The I2C Target device records the following signals with received data
 */
typedef enum dif_i2c_signal {
  /**
   * The associated byte was received with a START signal, and should be the
   * matching address and R/W bit
   */
  kDifI2cSignalStart = 1,
  /**
   * The associated byte was received after a STOP signal, so the transaction is
   * over and the byte is junk
   */
  kDifI2cSignalStop = 2,
  /**
   * The associated byte was received with a repeated START signal and
   * represents the address for the subsequent transaction.
   */
  kDifI2cSignalRepeat = 3,
  /**
   * There's no associated STOP or START signal this is just a byte that's been
   * written to the I2C target in an ongoing transaction
   */
  kDifI2cSignalNone = 0,
} dif_i2c_signal_t;

/**
 * Available formatting codes for `dif_i2c_write_byte_raw()`.
 *
 * Each code describes how to interpret the `byte` parameter, referred to below
 * as "the byte".
 *
 * It is the caller's responsibility to observe the state transitions in the
 * comments below.
 */
typedef enum dif_i2c_fmt {
  /**
   * Start a transaction. This sends a START signal followed by the byte.
   * The byte sent will form (potentially part of) the target address for the
   * transaction.
   *
   * May be followed by any format code.
   */
  kDifI2cFmtStart,
  /**
   * Transmit byte. This simply sends the byte. It may need to be used in
   * conjunction with `Start` to send a multi-byte target address.
   *
   * May be followed by any format code.
   */
  kDifI2cFmtTx,
  /**
   * Transmit byte and stop. This sends the byte, and then sends a stop
   * signal, completing a transaction.
   *
   * Only `Start` may follow this code.
   */
  kDifI2cFmtTxStop,
  /**
   * Request `n` bytes, where `n` is the byte interpreted as an unsigned
   * integer; a byte value of `0` will be interpreted as requesting `256`
   * bytes. This will NAK the last byte.
   *
   * Only `Start` may follow this code (this code does not stop a transaction;
   * see `RxStop`).
   */
  kDifI2cFmtRx,
  /**
   * Request `n` bytes, same as `Rx`, but ACK the last byte so that more data
   * can be requested.
   *
   * May be followed by `RxContinue`, `Rx`, or `RxStop`.
   */
  kDifI2cFmtRxContinue,
  /**
   * Request `n` bytes, same as `Rx`, but, after NAKing the last byte, send a
   * stop signal to end the transaction.
   *
   * Only `Start` may follow this code.
   */
  kDifI2cFmtRxStop,
} dif_i2c_fmt_t;

/**
 * Flags representing the status of an I2C block
 */
typedef struct dif_i2c_status {
  /**
   * Enable Host, I2C block has been initialized and enabled to act as a host,
   * consuming entries from the FMT FIFO to perform I2C transactions, and
   * writing the results of I2C Reads to the RX FIFO
   */
  bool enable_host;
  /**
   * Enable Target, I2C block has been initialized and enabled to act as a
   * target device, using the TX FIFO to respond to I2C Reads and the ACQ FIFO
   * to store data received from I2C Writes
   */
  bool enable_target;
  /**
   * Line Loopback enabled
   */
  bool line_loopback;
  /**
   * Format FIFO is full, SW cannot write commands to transact into the FIFO
   * until I2C host is able to act on the contents.
   */
  bool fmt_fifo_full;
  /**
   * RX FIFO is full, I2C cannot continue to read data until SW reads from the
   * FIFO.
   */
  bool rx_fifo_full;
  /**
   * Format FIFO is empty, I2C host will stop transacting until the FIFO is
   * written to.
   */
  bool fmt_fifo_empty;
  /**
   * RX FIFO Empty, Software has handled all bytes read by the I2C Host.
   */
  bool rx_fifo_empty;
  /**
   * I2C Host is not carrying out a transaction
   */
  bool host_idle;
  /**
   * I2C Device is not carrying out a transaction
   */
  bool target_idle;
  /**
   * TX FIFO Full, I2C device must respond to I2C reads or have the FIFO cleared
   * before SW can write to the FIFO.
   */
  bool tx_fifo_full;
  /**
   * Acquire FIFO is full of data from I2C writes to the target device. Software
   * must handle data before I2C device can continue
   */
  bool acq_fifo_full;
  /**
   * TX FIFO is empty, device is unprepared to respond to I2C Reads until SW
   * writes to FIFO
   */
  bool tx_fifo_empty;
  /**
   * Aquire FIFO is empty and will remain so until I2C Device recieves a Write
   */
  bool acq_fifo_empty;
} dif_i2c_status_t;

/**
 * Get I2C status.
 *
 * @param i2c An I2C handle.
 * @param[out] status I2C status as understood by the block.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_get_status(const dif_i2c_t *i2c, dif_i2c_status_t *status);

/**
 * Computes timing parameters for an I2C host and stores them in `config`.
 *
 * Timing is based on requirements for devices attached to OpenTitan
 *
 * The values returned may be tweaked by callers that require finer control over
 * some of the calculations, such as how the allocation of a lengthened SCL
 * period.
 *
 * @param timing_config Configuration values for producing timing parameters.
 * @param[out] config I2C configuration to which to apply the computed
 * parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_compute_timing(dif_i2c_timing_config_t timing_config,
                                    dif_i2c_config_t *config);

/**
 * Configures I2C with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * @param i2c An I2C handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_configure(const dif_i2c_t *i2c, dif_i2c_config_t config);

/**
 * Resets the state of the RX FIFO, essentially dropping all received bytes for
 * the host.
 *
 * @param i2c An I2c handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_reset_rx_fifo(const dif_i2c_t *i2c);

/**
 * Resets the state of the FMT FIFO, essentially dropping all scheduled
 * operations.
 *
 * @param i2c An I2c handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_reset_fmt_fifo(const dif_i2c_t *i2c);

/**
 * Resets the state of the TX FIFO, essentially dropping all scheduled
 * responses.
 *
 * @param i2c An I2c handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_reset_tx_fifo(const dif_i2c_t *i2c);

/**
 * Resets the state of the ACQ FIFO, essentially dropping all received bytes for
 * the target device.
 *
 * @param i2c An I2c handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_reset_acq_fifo(const dif_i2c_t *i2c);

/**
 * Sets watermarks for the RX and FMT FIFOs, which will fire the respective
 * interrupts when each fifo exceeds, or falls below, the set level.
 *
 * Note that the 30-byte level is only supported for the RX FIFO: trying to use
 * it with the FMT FIFO is an error.
 *
 * @param i2c An I2C handle.
 * @param rx_level The desired watermark level for the RX FIFO.
 * @param fmt_level The desired watermark level for the FMT FIFO.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_set_watermarks(const dif_i2c_t *i2c,
                                    dif_i2c_level_t rx_level,
                                    dif_i2c_level_t fmt_level);

/**
 * Enables or disables the "Host I2C" functionality,
 * This function should be called to enable the device
 * once timings, interrupts, and watermarks are all configured.
 *
 * @param i2c An I2C handle.
 * @param state The new toggle state for the host functionality.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_host_set_enabled(const dif_i2c_t *i2c, dif_toggle_t state);

/**
 * Enables or disables the "Device I2C" functionality,
 * This function should be called to enable the device
 * once address, and interrupts are all configured.
 *
 * @param i2c An I2C handle.
 * @param state The new toggle state for the device functionality.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_device_set_enabled(const dif_i2c_t *i2c,
                                        dif_toggle_t state);

/**
 * Enables or disables the Line Loopback functionality,
 * This function should be called to assist debugging by setting the i2c block
 * or host to use received transactions to populate outgoing transactions.
 *
 * @param i2c An I2C handle.
 * @param state The new toggle state for the host functionality.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_line_loopback_set_enabled(const dif_i2c_t *i2c,
                                               dif_toggle_t state);

/**
 * Enables or disables the "override mode". In override mode, software is able
 * to directly control the driven values of the SCL and SDA lines using
 * `dif_i2c_override_drive_pins()`.
 *
 * @param i2c An I2C handle.
 * @param state The new toggle state for override mode.'
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_override_set_enabled(const dif_i2c_t *i2c,
                                          dif_toggle_t state);

/**
 * Drives the SCL and SDA pins to the given values when "override mode" is
 * enabled.
 *
 * @param i2c An I2C handle.
 * @param scl The value to drive SCL to.
 * @param sda The value to drive SDA to.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_override_drive_pins(const dif_i2c_t *i2c, bool scl,
                                         bool sda);

/**
 * Returns oversampling of the last 16 values of the SCL and SDA pins, with the
 * zeroth bit being the most recent.
 *
 * @param i2c An I2C handle.
 * @param[out] scl_samples SCL sample bits; may be `NULL`.
 * @param[out] sda_samples SDA sample bits; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_override_sample_pins(const dif_i2c_t *i2c,
                                          uint16_t *scl_samples,
                                          uint16_t *sda_samples);

/**
 * Returns the current levels, i.e., number of entries, in the FMT, RX, TX and
 * ACQ FIFOs.
 * These values represent the number of entries pending for send by host
 * hardware, entries pending for read by host software, entries pending for send
 * by device hardware, and entries pending for read by device software
 * respectively.
 *
 * @param i2c An I2C handle.
 * @param[out] fmt_fifo_level The number of unsent FMT bytes; may be `NULL`.
 * @param[out] rx_fifo_level The number of unread RX bytes; may be `NULL`.
 * @param[out] tx_fifo_level The number of unread TX bytes; may be `NULL`.
 * @param[out] acq_fifo_level The number of unread ACQ bytes; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_get_fifo_levels(const dif_i2c_t *i2c,
                                     uint8_t *fmt_fifo_level,
                                     uint8_t *rx_fifo_level,
                                     uint8_t *tx_fifo_level,
                                     uint8_t *acq_fifo_level);

/**
 * Pops an entry (a byte) off of the RX FIFO. Passing in `NULL` to the out-param
 * will still trigger a byte pop.
 *
 * @param i2c An I2C handle.
 * @param[out] byte The popped byte; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_read_byte(const dif_i2c_t *i2c, uint8_t *byte);

/**
 * Pushes a raw write entry onto the FMT FIFO, consisting of a byte and format
 * flags. This function can be called in sequence to enqueue an I2C
 * transmission.
 *
 * Callers should prefer `dif_i2c_write_byte()` instead, since that function
 * provides clearer semantics. This function should only really be used for
 * testing or troubleshooting a device.
 *
 * @param i2c An I2C handle.
 * @param byte The value to push onto the FIFO.
 * @param flags The flags to use for this write.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_write_byte_raw(const dif_i2c_t *i2c, uint8_t byte,
                                    dif_i2c_fmt_flags_t flags);

/**
 * Pushes a write entry onto the FMT FIFO, consisting of a byte and a format
 * code. This function can be called in sequence to enqueue an I2C
 * transmission.
 *
 * @param i2c An I2C handle.
 * @param byte The value to push onto the FIFO.
 * @param code The code to use for this write.
 * @param suppress_nak_irq Whether to supress the NAK IRQ for this one byte.
 *        May not be used in combination with `Rx` codes.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_write_byte(const dif_i2c_t *i2c, uint8_t byte,
                                dif_i2c_fmt_t code, bool suppress_nak_irq);

/**
 * Pushes a byte into the TX FIFO to make it available when this I2C block
 * responds to an I2C Read as a target device.
 *
 * @param i2c handle.
 * @param byte to write to FIFO
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_transmit_byte(const dif_i2c_t *i2c, uint8_t byte);

/**
 * Read acquired data from the ACQ FIFO, including record of starts, stops,
 * address and written data
 *
 * @param i2c handle.
 * @param[out] byte, Data received in the transaction, Could be the address or
 * junk
 * @param[out] signal, Signal received in the transaction
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_acquire_byte(const dif_i2c_t *i2c, uint8_t *byte,
                                  dif_i2c_signal_t *signal);

/**
 * Enables clock stretching timeout after a number of I2C block clock cycles
 * when I2C block is configured as host.
 *
 * @param i2c An I2C handle,
 * @param enable the timeout
 * @param cycles How many cycles to wait before timing out
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_enable_clock_stretching_timeout(const dif_i2c_t *i2c,
                                                     dif_toggle_t enable,
                                                     uint32_t cycles);

/**
 * Sets the I2C device to listen for a pair of masked addresses
 *
 * @param i2c handle,
 * @param id0 address and mask pair to listen for can be null
 * @param id1 address and mask pair to listen for can be null
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_set_device_id(const dif_i2c_t *i2c, dif_i2c_id_t *id0,
                                   dif_i2c_id_t *id1);

/**
 * Set host timeout. When OT is acting as target device, set the number of
 * counts after which to trigger a host_timeout interrupt
 *
 * @param i2c handle,
 * @param duration in clock counts
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i2c_set_host_timeout(const dif_i2c_t *i2c, uint32_t duration);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_I2C_H_
