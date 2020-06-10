// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_I2C_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_I2C_H_

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"

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

/*
 * Timing parameters for an I2C device. Actually computing these values is
 * somewhat complicated, so this struct should be assembled using the
 * `dif_i2c_compute_timing()` function. A caller is, however, free to assemble
 * this struct or modify a return value of `dif_i2c_compute_timing()`, so long
 * as the spec is respected.
 *
 * These values correspond to those in Table 10 of the I2C spec, and are given
 * in units of input clock cycles.
 */
typedef struct dif_i2c_timing_params {
  uint16_t scl_time_high;
  uint16_t scl_time_low;
  uint16_t rise_time;
  uint16_t fall_time;
  uint16_t start_signal_setup_time;
  uint16_t start_signal_hold_time;
  uint16_t data_signal_setup_time;
  uint16_t data_signal_hold_time;
  uint16_t stop_signal_setup_time;
  /**
   * Note: This field is referred to in the IP documents as the,
   * "bus free time".
   */
  uint16_t stop_signal_hold_time;
} dif_i2c_timing_params_t;

/**
 * Configuration for computing a value of `dif_i2c_timing_params`, which itself
 * is used to configure an I2C device.
 */
typedef struct dif_i2c_timing_config {
  /**
   * Indicates the lowest speed at which an I2C target connected to this host
   * will operate.
   *
   * In other words, this is the maxiumum speed at which the host can operate
   * without going over what the target devices can handle.
   */
  dif_i2c_speed_t lowest_target_device_speed;
  /**
   * Indicates the period of the clock driving this device, in nanoseconds.
   *
   * This value should not be zero, since it is used as a divisor for
   * division.
   */
  uint32_t clock_period_nanos;
  /**
   * Indicates the expected time it takes for the I2C bus signal to rise, in
   * nanoseconds. This value is dependent on properties of the hardware's
   * interconnect, and not under actual firmware control.
   */
  uint32_t sda_rise_nanos;
  /**
   * Indicates the expected time for the bus singal to fall, similar to
   * `sda_rise_nanos`.
   */
  uint32_t sda_fall_nanos;
  /**
   * Indicates the desired period of the SCL line, in nanoseconds. Normally,
   * this should just be `1'000'000 / lowest_target_device_speed`, but the
   * period may be larger if desired.
   *
   * Setting this value to zero will result in the minimum period being used.
   */
  uint32_t scl_period_nanos;
} dif_i2c_timing_config_t;

/**
 * Represents an I2C device. This struct should only be initialized using
 * `dif_i2c_init()`.
 */
typedef struct dif_i2c { mmio_region_t base_addr; } dif_i2c_t;

typedef enum dif_i2c_result {
  kDifI2cOk = 0,
  kDifI2cBadArg,
  kDifI2cError,
} dif_i2c_result_t;

/**
 * Represents a valid watermark level for one of the I2C FIFOs.
 */
typedef enum dif_i2c_watermark_level {
  kDifI2cLevel1Byte = 0,
  kDifI2cLevel4Byte,
  kDifI2cLevel8Byte,
  kDifI2cLevel16Byte,
  kDifI2cLevel30Byte,
} dif_i2c_level_t;

/**
 * Represents an I2C-related interrupt type.
 */
typedef enum dif_i2c_irq_type {
  /**
   * Fired when the FMT FIFO underflows its watermark.
   */
  kDifI2cIrqTypeFmtWatermarkUnderflow = 0,
  /**
   * Fired when the RX FIFO overflows its watermark.
   */
  kDifI2cIrqTypeRxWatermarkOverflow,
  /**
   * Fired when the FMT FIFO overflows.
   */
  kDifI2cIrqTypeFmtFifoOverflow,
  /**
   * Fired when the RX FIFO overflows.
   */
  kDifI2cIrqTypeRxFifoOverflow,
  /**
   * Fired when there is no ACK in response to an address or data write.
   */
  kDifI2cIrqTypeNak,
  /**
   * Fired when the SCL line seems to have interference.
   */
  kDifI2cIrqTypeSclInterference,
  /**
   * Fired when the SDA line seems to have interference.
   */
  kDifI2cIrqTypeSdaInterference,
  /**
   * Fired when the target streches the clock beyond the allowed period.
   */
  kDifI2cIrqTypeClockStretchTimeout,
  /**
   * Fired when the target does not maintain a stable SDA line.
   */
  kDifI2cIrqTypeSdaUnstable,
} dif_i2c_irq_type_t;

/**
 * Represents an enablement state.
 */
typedef enum dif_i2c_enable {
  kDifI2cEnabled,
  kDifI2cDisabled,
} dif_i2c_enable_t;

/**
 * Computes timing parameters for an I2C device using the input parameters in
 * `config`.
 *
 * The value returned may be tweaked by callers that require finer control over
 * some of the calculations, such as how the allocation of a lengthened SCL
 * period.
 *
 * @param config Configuration values for producing timing parameters.
 * @param out Out-param for the actual timing parameters.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_compute_timing(const dif_i2c_timing_config_t *config,
                                        dif_i2c_timing_params_t *out);

/**
 * Initializes an I2C device using the given timing parameters.
 *
 * `dif_i2c_compute_timing()` can be used to generate default values for the
 * timing parameters based off of a small number of hardware parameters.
 *
 * @oaram base_addr The start of the I2C device register.
 * @param timing Timing parameters to initialize with.
 * @param i2c Out param for the initialized device.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_init(mmio_region_t base_addr,
                              const dif_i2c_timing_params_t *timing,
                              dif_i2c_t *i2c);

/**
 * Resets the state of the RX FIFO, essentially dropping all recieved bytes.
 *
 * @param i2c An I2C devce.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_reset_rx_fifo(const dif_i2c_t *i2c);

/**
 * Resets the state of the FMT FIFO, essentially dropping all scheduled
 * operations.
 *
 * @param i2c An I2C devce.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_reset_fmt_fifo(const dif_i2c_t *i2c);

/**
 * Sets watermarks for for the RX and FMT FIFOs, which will fire the respective
 * interrupts when each fifo exceeds, or falls bekow, the set level.
 *
 * Note that the 30-byte level is only supported for the RX FIFO: trying to use
 * it with the FMT FIFO is an error.
 *
 * @param i2c An I2C device.
 * @param rx_level The desired watermark level for the RX FIFO.
 * @param fmt_level The desired watermark level for the FMT FIFO.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_set_watermarks(const dif_i2c_t *i2c,
                                        dif_i2c_level_t rx_level,
                                        dif_i2c_level_t fmt_level);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param i2c An I2C device.
 * @param type An interrupt type.
 * @param flag_out Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_irq_get(const dif_i2c_t *i2c, dif_i2c_irq_type_t type,
                                 bool *flag_out);

/**
 * Clears a particular interrupt.
 *
 * @param i2c An I2C device.
 * @param type An interrupt type.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_irq_clear(const dif_i2c_t *i2c,
                                   dif_i2c_irq_type_t type);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param i2c An I2C device.
 * @param type An interrupt type.
 * @param state The new enablement state for the interrupt.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_irq_set_enabled(const dif_i2c_t *i2c,
                                         dif_i2c_irq_type_t type,
                                         dif_i2c_enable_t state);

/**
 * Forces a particular interrupt to fire.
 *
 * @param i2c An I2C device.
 * @param type An interrupt type.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_irq_force(const dif_i2c_t *i2c,
                                   dif_i2c_irq_type_t type);

// TODO: Implement IRQ save/restore. (#2371)

/**
 * Enables or disables the "Host I2C" functionality, effectively turning the
 * I2C device on or off. This function should be called to enable the device
 * once timings, interrupts, and watermarks are all configured.
 *
 * @param i2c An I2C device.
 * @param state The enablement state for the host functionality.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_host_set_enabled(const dif_i2c_t *i2c,
                                          dif_i2c_enable_t state);

/**
 * Enables or disables the "override mode". In override mode, software is able
 * to directly control the driven values of the SCL and SDA lines using
 * `dif_i2c_override_drive_pins()`.
 *
 * @param i2c An I2C device.
 * @param state The enablement state for override mode.'
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_override_set_enabled(const dif_i2c_t *i2c,
                                              dif_i2c_enable_t state);

/**
 * Drives the SCL and SDA pins to the given values when "override mode" is
 * enabled.
 *
 * @param i2c An I2C device.
 * @param scl The value to drive SCL to.
 * @param sda The value to drive SDA to.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_override_drive_pins(const dif_i2c_t *i2c, bool scl,
                                             bool sda);

/**
 * Returns oversampling of the last 16 values of the SCL and SDA pins, with the
 * zeroth bit being the most recent.
 *
 * @param i2c An I2C device.
 * @param scl_samples Out-param for SCL sample bits; may be null.
 * @param sda_samples Out-param for SDA sample bits; may be null.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_override_sample_pins(const dif_i2c_t *i2c,
                                              uint16_t *scl_samples,
                                              uint16_t *sda_samples);

/**
 * Returns the current levels, i.e., number of entries, in the FMT and RX FIFOs.
 * These values represent the number of entries pending for send by hardware,
 * and entries pending for read by software, respectively.
 *
 * @param i2c An I2C device.
 * @param fmt_fifo_level Out-param for the number of unsent FMT bytes; may be
 *        null.
 * @param rx_fifo_level Out-param for the number of unread RX bytes; may be
 *        null.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_get_fifo_levels(const dif_i2c_t *i2c,
                                         uint8_t *fmt_fifo_level,
                                         uint8_t *rx_fifo_level);

/**
 * Pops an entry (a byte) off of the RX FIFO. Passing in `NULL` to the out-param
 * will still trigger a byte pop.
 *
 * @param i2c An I2C device.
 * @param byte Out-param for the popped byte; may be null.
 * @return The result of the opeartion.
 */
dif_i2c_result_t dif_i2c_read_byte(const dif_i2c_t *i2c, uint8_t *byte);

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
   * an exception (surfaced as the `kDifi2cIrqTypeNak` interrupt). This flag
   * disables that behavior.
   *
   * This flag cannot be set along with `read` or `read_cont`.
   */
  bool supress_nak_irq;
} dif_i2c_fmt_flags_t;

/**
 * Pushes a raw write entry onto the FMT FIFO, consisting of a byte and format
 * flags. This function can be called in sequence to enqueue an I2C
 * transmission.
 *
 * Callers should prefer `dif_i2c_write_byte()` instead, since that function
 * provides clearer semantics. This function should only really be used for
 * testing or troubleshooting a device.
 *
 * @param i2c An I2C device.
 * @param byte The value to push onto the FIFO.
 * @param flags The flags to use for this write.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_write_byte_raw(const dif_i2c_t *i2c, uint8_t byte,
                                        dif_i2c_fmt_flags_t flags);
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
 * Pushes a write entry onto the FMT FIFO, consisting of a byte and a format
 * code. This function can be called in sequence to enqueue an I2C
 * transmission.
 *
 * @param i2c An I2C device.
 * @param byte The value to push onto the FIFO.
 * @param code The code to use for this write.
 * @param supress_nak_irq Whether to supress the NAK IRQ for this one byte.
 *        May not be used in combination with `Rx` codes.
 * @return The result of the operation.
 */
dif_i2c_result_t dif_i2c_write_byte(const dif_i2c_t *i2c, uint8_t byte,
                                    dif_i2c_fmt_t code, bool supress_nak_irq);

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_I2C_H_
