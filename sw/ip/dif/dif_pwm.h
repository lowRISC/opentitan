// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PWM_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PWM_H_

/**
 * @file
 * @brief <a href="/hw/ip/pwm/doc/">PWM</a> Device Interface Functions
 *
 * The PWM block contains a 16-bit "phase counter" that controls each channel's
 * output signal. The "phase counter" acts as a point of reference for a single
 * PWM "pulse cycle", that is further broken into "beats", depending on the
 * `beats_per_cycle` parameter. Specifically, a "pulse cycle" may contain [2,
 * 2^16] "beats". Within a "pulse cycle", users can configure the duty cycle in
 * number of "beats". Additionally, the duration of a single "beat", is computed
 * by dividing the core clock frequency by `clock_divisor + 1`.
 *
 *       PWM "pulse cycle" defined by 16-bit phase counter
 *  ___________________________________________________________
 *  |                                                         |
 *  v                                                         v
 * |-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-| ... |-|-|-|-|
 *
 * |-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-|-| ... |-|-|-|-|
 * min beat size = 1 phase counter tick --> 2^16 "beats" / "pulse cycle"
 *
 * |---------------------------------------------- ... | ... --|
 *    max beat size = 2^15 phase counter ticks --> 2 "beats" / "pulse cycle"
 */

#include <stdint.h>

#include "sw/device/lib/dif/autogen/dif_pwm_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Helper X macro for defining enums and case statements related to PWM
 * channels. If an additional channel is ever added to the hardware, this list
 * can be updated.
 */
#define DIF_PWM_CHANNEL_LIST(X) \
  X(0)                          \
  X(1)                          \
  X(2)                          \
  X(3)                          \
  X(4)                          \
  X(5)

/**
 * Helper macro for defining a `dif_pwm_channel_t` enumeration constant.
 * @channel_ PWM channel of the enumeration constant.
 */
#define PWM_CHANNEL_ENUM_INIT_(channel_) \
  kDifPwmChannel##channel_ = 1U << channel_,

/**
 * A PWM channel.
 */
typedef enum dif_pwm_channel {
  DIF_PWM_CHANNEL_LIST(PWM_CHANNEL_ENUM_INIT_)
} dif_pwm_channel_t;

#undef PWM_CHANNEL_ENUM_INIT_

/**
 * Runtime configuration for PWM.
 *
 * This struct describes runtime configuration for one-time configuration of the
 * PWM "pulse cycle" and "beat" durations that impact all PWM channels.
 */
typedef struct dif_pwm_config {
  /**
   * The core clock frequency divisor that determines the period of a single
   * "beat" within a PWM "pulse cycle".
   *
   * Valid range: [0, 2^26)
   *
   * A value of zero, configures the "beat" period to the core clock period.
   */
  uint32_t clock_divisor;
  /**
   * The total number of "beats" in a "pulse cycle", including both "on" and
   * "off" beats in a "pulse cycle".
   *
   * Valid range: [2, 2^16]
   *
   * Note: while any value in the range is acceptable, values will be rounded
   * down to closest power-of-two.
   *
   * A "beat" represents a unit of time of the PWM output signal. Higher values
   * provide higher duty cycle resolutions, at the expense of longer "pulse
   * cycles", while lower values provide shorter "pulse cycles", at the expense
   * of lower duty cycle resolutions (since duty cycles are configured in
   * "beats" / "pulse cycle").
   */
  uint32_t beats_per_pulse_cycle;
} dif_pwm_config_t;

/**
 * A PWM channel mode.
 */
typedef enum dif_pwm_mode {
  /**
   * The PWM duty cycle is set by the firmware and remains constant.
   */
  kDifPwmModeFirmware = 0,
  /**
   * The PWM duty cycle linearly sweeps between both primary and secondary
   * firmware-configured values, based on a firmware-configured step size.
   */
  kDifPwmModeHeartbeat = 1,
  /**
   * The PWM duty cycle alternates between both primary and secondary
   * firmware-configured values, based on two firmware-configured durations.
   */
  kDifPwmModeBlink = 2,
} dif_pwm_mode_t;

/**
 * A PWM channel polarity.
 */
typedef enum dif_pwm_polarity {
  /**
   * A PWM signal is active-high.
   */
  kDifPwmPolarityActiveHigh = 0,
  /**
   * A PWM signal is active-low.
   */
  kDifPwmPolarityActiveLow = 1,
} dif_pwm_polarity_t;

/**
 * Runtime configuration for a specific PWM channel.
 *
 * This struct describes runtime configuration for one-time configuration of a
 * specific PWM channel.
 */
typedef struct dif_pwm_channel_config {
  /**
   * Primary duty cycle, in number of "beats" / "pulse cycle".
   *
   * Valid range: [0, beats_per_pulse_cycle)
   *
   * Note: the raw value written to the `A_*` bitfield in each PWM channel's
   *       `DUTY_CYCLE_*` CSR is in units of "phase counter ticks", not "beats".
   *       However, the hardware only takes into account the first `DC_RESN` + 1
   *       MSBs of the raw duty cycle value to determine the number of "beats"
   *       for a given duty cycle. To make this configuration easier, the
   *       software manages the conversion from "beats_per_cycle" to
   *       "phase_counter_ticks" under the hood.
   */
  uint16_t duty_cycle_a;
  /**
   * Secondary duty cycle, in number of "beats" / "pulse cycle", that is only
   * relevant in heartbeat and blink modes.
   *
   * Valid range: [0, beats_per_pulse_cycle)
   *
   * Note: above notes for `duty_cycle_a` apply here too.
   */
  uint16_t duty_cycle_b;
  /**
   * Phase delay at the beginning of a "pulse cycle" to delay the active
   * duty cycle "beats" for, in number of "beats".
   *
   * Valid range: [0, beats_per_pulse_cycle)
   */
  uint16_t phase_delay;
  /**
   * The operation mode to configure the channel in, see `dif_pwm_mode_t`.
   */
  dif_pwm_mode_t mode;
  /**
   * The polarity to configure the channel in, see `dif_pwm_polarity_t`.
   */
  dif_pwm_polarity_t polarity;
  /**
   * One of two blink parameters that only impact the "Heartbeat" and "Blink"
   * operation modes.
   *
   * The meaning of this parameter is different based on the operation mode:
   *     - Heartbeat mode: determines the number of "pulse cycles" between
   *                       increments/decrements to the duty cycle.
   *
   *     - Blink mode: determines the number of "pulse cycles" to pulse at duty
   *                   cycle A, before switching to duty cycle B.
   */
  uint16_t blink_parameter_x;
  /**
   * One of two blink parameters that only impact the "Heartbeat" and "Blink"
   * operation modes.
   *
   * The meaning of this parameter is different based on the operation mode:
   *     - Heartbeat mode: determines the increment/decrement amount in number
   *                       of duty cycle "beats".
   *
   *     - Blink mode: determines the number of "pulse cycles" to pulse at duty
   *                   cycle B, before switching to duty cycle A.
   *
   * Note: the raw value written to the `blink_parameter_x` bitfield in each PWM
   * channel's `BLINK_PARAM_*` CSR is in units of "phase counter ticks", not
   * "beats". However, for ease of configuration, the software manages this
   * conversion under the hood.
   */
  uint16_t blink_parameter_y;
} dif_pwm_channel_config_t;

/**
 * Configures "phase cycle" and "beat" durations of all PWM channels.
 *
 * Since changes to `CLK_DIV` and `DC_RESN` are only allowed when the PWM is
 * disabled, this function has the side effect of temporarily disabling all PWM
 * channels while configurations are updated, before restoring the original
 * enablement state.
 *
 * This function should only need to be called once for the lifetime of
 * `handle`.
 *
 * @param pwm A PWM handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwm_configure(const dif_pwm_t *pwm, dif_pwm_config_t config);

/**
 * Configures a single PWM channel.
 *
 * Since changes to `CLK_DIV` and `DC_RESN` are only allowed when the PWM is
 * disabled, this function has the side effect of temporarily disabling the
 * PWM while configurations are updated, before returning the block to its
 * original enablement state.
 *
 * This function should only need to be called once for each PWM channel that
 * will be used.
 *
 * @param pwm A PWM handle.
 * @param channel A PWM channel to configure.
 * @param config Runtime configuration parameters for the channel.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwm_configure_channel(const dif_pwm_t *pwm,
                                       dif_pwm_channel_t channel,
                                       dif_pwm_channel_config_t config);

/**
 * Sets the enablement state of the PWM phase counter, which controls the
 * enablement of all PWM channels.
 *
 * @param pwm A PWM handle.
 * @param enabled The enablement state to configure the PWM phase counter in.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwm_phase_cntr_set_enabled(const dif_pwm_t *pwm,
                                            dif_toggle_t enabled);

/**
 * Gets the enablement state of the PWM phase counter, which controls the
 * enablement of all PWM channels.
 *
 * @param pwm A PWM handle.
 * @param[out] is_enabled The enablement state of the PWM phase counter.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwm_phase_cntr_get_enabled(const dif_pwm_t *pwm,
                                            dif_toggle_t *is_enabled);

/**
 * Sets the enablement states of one or more PWM channels.
 *
 * @param pwm A PWM handle.
 * @param channels The channels to enable (one or more `dif_pmw_channel_t`s
 *                 ORed together.)
 * @param enabled The enablement state to set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwm_channel_set_enabled(const dif_pwm_t *pwm,
                                         uint32_t channels,
                                         dif_toggle_t enabled);

/**
 * Gets the enablement state of one PWM channel.
 *
 * @param pwm A PWM handle.
 * @param channel The PWM channel to get the enablement state of.
 * @param[out] is_enabled The enablement state of the PWM channel.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwm_channel_get_enabled(const dif_pwm_t *pwm,
                                         dif_pwm_channel_t channel,
                                         dif_toggle_t *is_enabled);

/**
 * Locks PWM configurations.
 *
 * This function is reentrant: calling it while locked will have no effect and
 * return `kDifOk`.
 *
 * @param pwm A PWM handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwm_lock(const dif_pwm_t *pwm);

/**
 * Checks whether PWM configurations are locked.
 *
 * @param pwm A PWM handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwm_is_locked(const dif_pwm_t *pwm, bool *is_locked);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PWM_H_
