// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_RV_TIMER_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_RV_TIMER_H_

/**
 * @file
 * @brief <a href="/hw/ip/rv_timer/doc/">RV Timer</a> Device Interface Functions
 */

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Represents an "enabled" state for a timer.
 */
typedef enum dif_rv_timer_enabled {
  kDifRvTimerDisabled = 0,
  kDifRvTimerEnabled,
} dif_rv_timer_enabled_t;

/**
 * Represents timekeeping parameters for a particular timer.
 */
typedef struct dif_rv_timer_tick_params {
  /**
   * The prescaler value is the period of the timer tick in clock cycles,
   * minus one. That is,
   *
   *   prescale = clock_freq * tick_period - 1
   *
   * with |clock_freq| and |tick_period| given in units of hertz and seconds,
   * respectively.
   *
   * For example, if the clock frequency is 50 MHz, and the desired tick
   * period is is 1 microsecond, i.e, a tick frequency of 1 MHz, then the
   * prescaler should be:
   *
   * (50 * 10^6) * (1 * 10^-6) - 1 = 49
   *
   * However, since |tick_period| is very small, it is much more convenient to
   * work with |tick_freq|, its inverse, which will be an integer number of
   * hertz. In particular,
   *
   *   prescale = (clock_freq / tick_freq) - 1
   *
   * This value is declared as a uint16_t, but only the lowest 12 bits are
   * actually used.
   */
  uint16_t prescale;

  /**
   * The amount to increment the timer counter at each tick.
   */
  uint8_t tick_step;
} dif_rv_timer_tick_params_t;

/**
 * Represents the result of an RV timer operation..
 */
typedef enum dif_rv_timer_result {
  kDifRvTimerOk = 0,
  kDifRvTimerBadArg = 1,
  kDifRvTimerError = 2,
} dif_rv_timer_result_t;

/**
 * Errors returned by `dif_rv_timer_approximate_tick_params()`.
 */
typedef enum dif_rv_timer_approximate_tick_params_result {
  kDifRvTimerApproximateTickParamsOk = kDifRvTimerOk,
  kDifRvTimerApproximateTickParamsBadArg = kDifRvTimerBadArg,
  kDifRvTimerApproximateTickParamsError = kDifRvTimerError,
  /**
   * Indicates that the requested counter frequency cannot be represented
   * without loss in precission.
   */
  kDifRvTimerApproximateTickParamsUnrepresentable,
} dif_rv_timer_approximate_tick_params_result_t;

/**
 * Generates an aproximate `dif_rv_timer_tick_params_t` given the device
 * clock frequency and desired counter frequency (both given in Hertz).
 *
 * For the purposes of this function, "counter frequency" is the frequency
 * at which software would observe a timer counter to increase. If the
 * clock has insufficient resolution, high counter frequencies may set a
 * larger value for `tick_step`. For example, if the clock ticks at 50kHz,
 * but we want a counter that seems to tick every microsecond (1MHz),
 * we can achieve this with a prescale of 0 (so that there is a tick per
 * clock cycle) and a tick step of 20 (since 20 * 50kHz = 1MHz).
 *
 * The return value of this function is only an approximation, and the
 * actual counter frequency ultimately depends on the accuracy of the
 * clock. The function will return an error if it cannot produce an acceptably
 * accurate counter frequency using the given clock resolution.
 *
 * @param clock_freq The device clock frequency, in Hertz.
 * @param counter_freq The desired counter frequency, in Hertz.
 * @param[out] out Tick parameters that will approximately produce the desired
 *         counter frequency.
 * @return The result of the operation.
 */
dif_rv_timer_approximate_tick_params_result_t
dif_rv_timer_approximate_tick_params(uint64_t clock_freq, uint64_t counter_freq,
                                     dif_rv_timer_tick_params_t *out);
/**
 * Configuration for initializing the RISC-V timer device.
 */
typedef struct dif_rv_timer_config {
  /**
   * The number of harts that this device supports time counters for.
   * Must be at least one.
   *
   * This value is determined entirely by the hardware configuration.
   */
  uint32_t hart_count;

  /**
   * The number of comparators (i.e, timers that can be set) associated
   * with each hart. Must be at least one.
   *
   * This value is determined entirely by the hardware configuration.
   */
  uint32_t comparator_count;
} dif_rv_timer_config_t;

/**
 * State for a RISC-V timer, associated with a particular hardware thread.
 *
 * Its member variables should be considered private, and are only provided so
 * that callers can allocate it.
 */
typedef struct dif_rv_timer {
  mmio_region_t base_addr;
  dif_rv_timer_config_t config;
} dif_rv_timer_t;

/**
 * Initialize a RISC-V timer device with the given configuration.
 *
 * This function will deactivate all counters and reset all timers, which should
 * each be configured and turned on manually after this function returns.
 *
 * @param base_addr MMIO region for the device hardware registers.
 * @param config Configuration for initializing a particular timer.
 * @param[out] timer_out The timer device.
 * @return The result of the operation.
 */
dif_rv_timer_result_t dif_rv_timer_init(mmio_region_t base_addr,
                                        dif_rv_timer_config_t config,
                                        dif_rv_timer_t *timer_out);

/**
 * Completely resets a timer device, disabling all IRQs, counters, and
 * comparators.
 *
 * @param timer A timer device.
 * @return The result of the operation.
 */
dif_rv_timer_result_t dif_rv_timer_reset(const dif_rv_timer_t *timer);

/**
 * Configures the tick params for a particular hart's counter.
 *
 * This function should not be called when `hart_id`'s counter is enabled; it is
 * the caller's responsibility to assert this precondition.
 * The function `dif_rv_timer_approximate_tick_params()` can be used to generate
 * tick parameter values.
 *
 * @param timer A timer device.
 * @param hart_id The hart to configure.
 * @param params The timing parameters.
 * @return The result of the operation.
 */
dif_rv_timer_result_t dif_rv_timer_set_tick_params(
    const dif_rv_timer_t *timer, uint32_t hart_id,
    dif_rv_timer_tick_params_t params);

/**
 * Starts or stops a particular hart's counter.
 *
 * While a counter is enabled, the counter value will increase each tick, but
 * its timekeeping values cannot be reconfigured.
 *
 * @param timer A timer device.
 * @param hart_id The hart counter to enable/disable.
 * @param state The new enablement state.
 * @return The result of the operation.
 */
dif_rv_timer_result_t dif_rv_timer_counter_set_enabled(
    const dif_rv_timer_t *timer, uint32_t hart_id,
    dif_rv_timer_enabled_t state);

/**
 * Reads the current value on a particlar hart's timer.
 *
 * @param timer A timer device.
 * @param hart_id The hart counter to read.
 * @param[out] out The counter value.
 * @return The result of the operation.
 */
dif_rv_timer_result_t dif_rv_timer_counter_read(const dif_rv_timer_t *timer,
                                                uint32_t hart_id,
                                                uint64_t *out);

/**
 * Arms the timer to go off once the counter value is greater than
 * or equal to `threshold`, by setting up the given comparator.
 *
 * Beware that the following naive implementation of setting an alarm
 * contains a bug:
 *   uint64_t time;
 *   dif_rv_timer_counter_read(my_timer, kMyHart, &time);
 *   time += kSomeDuration;  // (*)
 *   dif_rv_timer_arm(my_timer, kMyHart, kMyComp, time);
 *
 * If `time` wraps around when performing the addition, an interrupt will be
 * fired immediately upon calling `dif_rv_timer_arm`. Care should be taken to
 * perform saturating addition at (*), so that the interrupt is fired when the
 * timer value wraps around; this way, the interrupt handler can re-arm the
 * timer for the rest of the duration.
 *
 * This function makes no effort to protect the caller from setting alarms in
 * the past that would immediately fire an interrupt. It is the caller's
 * responsibility to read the current counter value and pick a reasonable alarm
 * threshold.
 *
 * @param timer A timer device.
 * @param hart_id The hart counter to arm against.
 * @param comp_id The comparator to set up.
 * @param threshold The value to go off at.
 * @return The result of the operation.
 */
dif_rv_timer_result_t dif_rv_timer_arm(const dif_rv_timer_t *timer,
                                       uint32_t hart_id, uint32_t comp_id,
                                       uint64_t threshold);

/**
 * Enables or disables a particular timer's IRQ. That is, this function controls
 * whether or not an IRQ is fired when the timer reaches its configured
 * threshold.
 *
 * @param timer A timer device.
 * @param hart_id The hart counter associated with the timer.
 * @param comp_id The comparator associated with the timer.
 * @param state The desired status.
 * @return the result of the operation.
 */
dif_rv_timer_result_t dif_rv_timer_irq_enable(const dif_rv_timer_t *timer,
                                              uint32_t hart_id,
                                              uint32_t comp_id,
                                              dif_rv_timer_enabled_t state);

/**
 * Returns whether the IRQ for a particular timer is currently being serviced.
 *
 * @param timer A timer device.
 * @param hart_id The hart counter associated with the timer.
 * @param comp_id The comparator associated with the timer.
 * @param[out] flag_out The interrupt status.
 * @return the result of the operation.
 */
dif_rv_timer_result_t dif_rv_timer_irq_get(const dif_rv_timer_t *timer,
                                           uint32_t hart_id, uint32_t comp_id,
                                           bool *flag_out);

/**
 * Clears the IRQ for a particular timer.
 *
 * @param timer A timer device.
 * @param hart_id The hart counter associated with the timer.
 * @param comp_id The comparator associated with the timer.
 * @return the result of the operation.
 */
dif_rv_timer_result_t dif_rv_timer_irq_clear(const dif_rv_timer_t *timer,
                                             uint32_t hart_id,
                                             uint32_t comp_id);

/**
 * Forces the IRQ for a particular timer to fire.
 *
 * @param timer A timer device.
 * @param hart_id The hart counter associated with the timer.
 * @param comp_id The comparator associated with the timer.
 * @return the result of the operation.
 */
dif_rv_timer_result_t dif_rv_timer_irq_force(const dif_rv_timer_t *timer,
                                             uint32_t hart_id,
                                             uint32_t comp_id);

/**
 * Disables all IRQs for a particular hart.
 *
 * Optionally returns a `state` value containing the previous itnerrupt state.
 * `state` may be NULL. See `dif_rv_timer_irq_restore()`.
 *
 * @param timer a timer device.
 * @param[out] state IRQ state information for use with
 *                   `dif_rv_timer_irq_restore`.
 * @return the result of the operation.
 */
dif_rv_timer_result_t dif_rv_timer_irq_disable(const dif_rv_timer_t *timer,
                                               uint32_t hart_id,
                                               uint32_t *state);

/**
 * Restores IRQ state for a particular hart.
 *
 * @param timer a timer device.
 * @param state IRQ state information to restore.
 * @return the result of the operation.
 */
dif_rv_timer_result_t dif_rv_timer_irq_restore(const dif_rv_timer_t *timer,
                                               uint32_t hart_id,
                                               uint32_t state);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_RV_TIMER_H_
