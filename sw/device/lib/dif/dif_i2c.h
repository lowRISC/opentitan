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

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A toggle state: enabled, or disabled.
 *
 * This enum may be used instead of a `bool` when describing an enabled/disabled
 * state.
 */
typedef enum dif_i2c_toggle {
  /*
   * The "enabled" state.
   */
  kDifI2cToggleEnabled,
  /**
   * The "disabled" state.
   */
  kDifI2cToggleDisabled,
} dif_i2c_toggle_t;

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
 * Hardware instantiation parameters for I2C.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_i2c_params {
  /**
   * The base address for the I2C hardware registers.
   */
  mmio_region_t base_addr;
} dif_i2c_params_t;

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
 * A handle to I2C.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_i2c { dif_i2c_params_t params; } dif_i2c_t;

/**
 * The result of a I2C operation.
 */
typedef enum dif_i2c_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifI2cOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  kDifI2cError = 1,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifI2cBadArg = 2,
} dif_i2c_result_t;

/**
 * Represents an I2C-related interrupt type.
 */
typedef enum dif_i2c_irq {
  /**
   * Fired when the FMT FIFO underflows its watermark.
   */
  kDifI2cIrqFmtWatermarkUnderflow = 0,
  /**
   * Fired when the RX FIFO overflows its watermark.
   */
  kDifI2cIrqRxWatermarkOverflow,
  /**
   * Fired when the FMT FIFO overflows.
   */
  kDifI2cIrqFmtFifoOverflow,
  /**
   * Fired when the RX FIFO overflows.
   */
  kDifI2cIrqRxFifoOverflow,
  /**
   * Fired when there is no ACK in response to an address or data write.
   */
  kDifI2cIrqNak,
  /**
   * Fired when the SCL line seems to have interference.
   */
  kDifI2cIrqSclInterference,
  /**
   * Fired when the SDA line seems to have interference.
   */
  kDifI2cIrqSdaInterference,
  /**
   * Fired when the target stretches the clock beyond the allowed period.
   */
  kDifI2cIrqClockStretchTimeout,
  /**
   * Fired when the target does not maintain a stable SDA line.
   */
  kDifI2cIrqSdaUnstable,
} dif_i2c_irq_t;

/**
 * A snapshot of the entablement state of the interrupts for I2C.
 *
 * This is an opaque type, to be used with the `dif_i2c_irq_disable_all()` and
 * `dif_i2c_irq_restore_all()` functions.
 */
typedef uint32_t dif_i2c_irq_snapshot_t;

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
 * Computes timing parameters for an I2C device and stores them in `config`.
 *
 * The values returned may be tweaked by callers that require finer control over
 * some of the calculations, such as how the allocation of a lengthened SCL
 * period.
 *
 * @param config Configuration values for producing timing parameters.
 * @param[out] out I2C configuration to which to apply the computed parameters.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_compute_timing(dif_i2c_timing_config_t timing_config,
                                        dif_i2c_config_t *config);
/**
 * Creates a new handle for I2C.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param[out] i2c Out param for the initialized handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_init(dif_i2c_params_t params, dif_i2c_t *i2c);

/**
 * Configures I2C with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * @param i2c An I2C handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_configure(const dif_i2c_t *i2c,
                                   dif_i2c_config_t config);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param i2c An I2C handle.
 * @param irq An interrupt type.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_irq_is_pending(const dif_i2c_t *i2c, dif_i2c_irq_t irq,
                                        bool *is_pending);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param i2c An I2C handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_irq_acknowledge(const dif_i2c_t *i2c,
                                         dif_i2c_irq_t irq);

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param i2c An I2C handle.
 * @param irq An interrupt type.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_irq_get_enabled(const dif_i2c_t *i2c,
                                         dif_i2c_irq_t irq,
                                         dif_i2c_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param i2c An I2C handle.
 * @param irq An interrupt type.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_irq_set_enabled(const dif_i2c_t *i2c,
                                         dif_i2c_irq_t irq,
                                         dif_i2c_toggle_t state);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param i2c An I2C handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_irq_force(const dif_i2c_t *i2c, dif_i2c_irq_t irq);

/**
 * Disables all interrupts, optionally snapshotting all toggle state for later
 * restoration.
 *
 * @param i2c An I2C handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_irq_disable_all(const dif_i2c_t *i2c,
                                         dif_i2c_irq_snapshot_t *snapshot);

/**
 * Restores interrupts from the given snapshot.
 *
 * This function can be used with `dif_i2c_irq_disable_all()` to temporary
 * interrupt save-and-restore.
 *
 * @param i2c An I2C handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_irq_restore_all(
    const dif_i2c_t *i2c, const dif_i2c_irq_snapshot_t *snapshot);

/**
 * Resets the state of the RX FIFO, essentially dropping all received bytes.
 *
 * @param i2c An I2c handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_reset_rx_fifo(const dif_i2c_t *i2c);

/**
 * Resets the state of the FMT FIFO, essentially dropping all scheduled
 * operations.
 *
 * @param i2c An I2c handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_reset_fmt_fifo(const dif_i2c_t *i2c);

/**
 * Sets watermarks for for the RX and FMT FIFOs, which will fire the respective
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
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_set_watermarks(const dif_i2c_t *i2c,
                                        dif_i2c_level_t rx_level,
                                        dif_i2c_level_t fmt_level);

/**
 * Enables or disables the "Host I2C" functionality, effectively turning the
 * I2C device on or off. This function should be called to enable the device
 * once timings, interrupts, and watermarks are all configured.
 *
 * @param i2c An I2C handle.
 * @param state The new toggle state for the host functionality.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_host_set_enabled(const dif_i2c_t *i2c,
                                          dif_i2c_toggle_t state);

/**
 * Enables or disables the "override mode". In override mode, software is able
 * to directly control the driven values of the SCL and SDA lines using
 * `dif_i2c_override_drive_pins()`.
 *
 * @param i2c An I2C handle.
 * @param state The new toggle state for override mode.'
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_override_set_enabled(const dif_i2c_t *i2c,
                                              dif_i2c_toggle_t state);

/**
 * Drives the SCL and SDA pins to the given values when "override mode" is
 * enabled.
 *
 * @param i2c An I2C handle.
 * @param scl The value to drive SCL to.
 * @param sda The value to drive SDA to.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_override_drive_pins(const dif_i2c_t *i2c, bool scl,
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
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_override_sample_pins(const dif_i2c_t *i2c,
                                              uint16_t *scl_samples,
                                              uint16_t *sda_samples);

/**
 * Returns the current levels, i.e., number of entries, in the FMT and RX FIFOs.
 * These values represent the number of entries pending for send by hardware,
 * and entries pending for read by software, respectively.
 *
 * @param i2c An I2C handle.
 * @param[out] fmt_fifo_level The number of unsent FMT bytes; may be `NULL`.
 * @param[out] rx_fifo_level The number of unread RX bytes; may be `NULL`.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_get_fifo_levels(const dif_i2c_t *i2c,
                                         uint8_t *fmt_fifo_level,
                                         uint8_t *rx_fifo_level);

/**
 * Pops an entry (a byte) off of the RX FIFO. Passing in `NULL` to the out-param
 * will still trigger a byte pop.
 *
 * @param i2c An I2C handle.
 * @param[out] byte The popped byte; may be `NULL`.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_read_byte(const dif_i2c_t *i2c, uint8_t *byte);

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
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_write_byte_raw(const dif_i2c_t *i2c, uint8_t byte,
                                        dif_i2c_fmt_flags_t flags);

/**
 * Pushes a write entry onto the FMT FIFO, consisting of a byte and a format
 * code. This function can be called in sequence to enqueue an I2C
 * transmission.
 *
 * @param i2c An I2C handle.
 * @param byte The value to push onto the FIFO.
 * @param code The code to use for this write.
 * @param supress_nak_irq Whether to supress the NAK IRQ for this one byte.
 *        May not be used in combination with `Rx` codes.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_i2c_result_t dif_i2c_write_byte(const dif_i2c_t *i2c, uint8_t byte,
                                    dif_i2c_fmt_t code, bool suppress_nak_irq);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_I2C_H_
