// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ADC_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ADC_CTRL_H_

/**
 * @file
 * @brief <a href="/hw/ip/adc_ctrl/doc/">ADC Controller</a> Device Interface
 * Functions
 */

#include "adc_ctrl_regs.h"  // Generated.
#include "sw/device/lib/dif/autogen/dif_adc_ctrl_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Helper X macro for defining enums and case statements related to ADC
 * Controller channels. If an additional channel is ever added to the hardware,
 * this list can be updated.
 */
#define DIF_ADC_CTRL_CHANNEL_LIST(X) \
  X(0)                               \
  X(1)

/**
 * Helper X macro for defining enums and case statements related to ADC
 * Controller filters. If an additional filter is ever added to the hardware,
 * this list can be updated.
 */
#define DIF_ADC_CTRL_FILTER_LIST(X) \
  X(0)                              \
  X(1)                              \
  X(2)                              \
  X(3)                              \
  X(4)                              \
  X(5)                              \
  X(6)                              \
  X(7)

/**
 * Helper macro for defining a `dif_adc_ctrl_channel_t` enumeration constant.
 * @channel_ ADC Controller channel of the enumeration constant.
 */
#define DIF_ADC_CTRL_CHANNEL_ENUM_INIT_(channel_) \
  kDifAdcCtrlChannel##channel_ = channel_,

/**
 * An ADC Controller Channel.
 */
typedef enum dif_adc_ctrl_channel {
  DIF_ADC_CTRL_CHANNEL_LIST(DIF_ADC_CTRL_CHANNEL_ENUM_INIT_)
} dif_adc_ctrl_channel_t;

#undef DIF_ADC_CTRL_CHANNEL_ENUM_INIT_

/**
 * Helper macro for defining a `dif_adc_ctrl_filter_t` enumeration constant.
 * @filter_ ADC Controller filter of the enumeration constant.
 */
#define DIF_ADC_CTRL_FILTER_ENUM_INIT_(filter_) \
  kDifAdcCtrlFilter##filter_ = filter_,

/**
 * An ADC Controller filter.
 *
 * Each channel has a separate instance of each filter. For example, if there
 * are two channels and eight filters, there would be a total of 16 filter
 * instances that may be configured.
 */
typedef enum dif_adc_ctrl_filter {
  DIF_ADC_CTRL_FILTER_LIST(DIF_ADC_CTRL_FILTER_ENUM_INIT_)
} dif_adc_ctrl_filter_t;

#undef DIF_ADC_CTRL_FILTER_ENUM_INIT_

/**
 * Helper macro for defining a `dif_adc_ctrl_irq_cause_t` enumeration constant.
 * @filter_cause_ ADC Controller IRQ filter cause of the enumeration constant.
 */
#define DIF_ADC_CTRL_IRQ_CAUSE_ENUM_INIT_(filter_cause_) \
  kDifAdcCtrlIrqCauseFilter##filter_cause_ = 1U << filter_cause_,

/**
 * An ADC Controller IRQ cause.
 *
 * The ADC Controller can only generate a single interrupt (the `debug_cable`
 * interrupt). However, depending on how the ADC Controller is configured, there
 * are several causes that could trigger this interrupt. These include filter
 * matches (when in Normal Power Scan mode), or sample completion (when in
 * Oneshot mode).
 */
typedef enum dif_adc_ctrl_irq_cause {
  DIF_ADC_CTRL_FILTER_LIST(DIF_ADC_CTRL_IRQ_CAUSE_ENUM_INIT_)
  /**
   * Sample ready cause in Oneshot mode.
   */
  kDifAdcCtrlIrqCauseOneshot = 1U << ADC_CTRL_ADC_INTR_STATUS_ONESHOT_BIT,
  /**
   * All IRQ causes ORed together.
   *
   * This is useful when clearing all IRQ causes at once, to initialize the ADC
   * Controller.
   */
  kDifAdcCtrlIrqCauseAll =
      (1U << (ADC_CTRL_ADC_INTR_STATUS_ONESHOT_BIT + 1)) - 1,
} dif_adc_ctrl_irq_cause_t;

#undef DIF_ADC_CTRL_IRQ_CAUSE_ENUM_INIT_

/**
 * Operation mode of the ADC Controller.
 */
typedef enum dif_adc_ctrl_mode {
  /**
   * Low Power (Continuous) Scan mode.
   *
   * In Low Power Scan mode, the ADC periodically samples enabled channels, and
   * upon matching a set of enabled filters, a set number of times, will
   * transition to Normal Power Scan mode. If no filters are enabled, then the
   * ADC controller will never transition to Normal Power Scan mode.
   */
  kDifAdcCtrlLowPowerScanMode = 0,
  /**
   * Normal Power (Continuous) Scan mode.
   *
   * In Normal Power Scan mode, the ADC samples enabled channels as fast as
   * possible, and upon matching a set of enabled filters, a set number of
   * consecutive times, may trigger a system wakeup and/or IRQ. Similar to Low
   * Power Scan mode, if no filters are enabled, then a system wakeup and/or IRQ
   * will never be triggered.
   */
  kDifAdcCtrlNormalPowerScanMode = 1,
  /**
   * Oneshot mode.
   *
   * In Oneshot mode, an ADC channel is triggered to take a single sample, upon
   * being enabled, and optionally, raises an interrupt upon completion. Unlike
   * the Scan modes, in Oneshot mode, the ADC Controller does not attempt to
   * filter samples. Rather, an IRQ may be raised immediately upon the sample
   * being ready, regardless of what the sample is. After the sample is
   * completed the ADC is powered down, until another sample is triggered,
   * either by toggling the channel's enable bit on and off, or by resetting the
   * sampling FSM.
   */
  kDifAdcCtrlOneshotMode = 2,
} dif_adc_ctrl_mode_t;

/**
 * Runtime configuration for an ADC Controller.
 */
typedef struct dif_adc_ctrl_config {
  /**
   * The sampling mode to configure the ADC Controller in.
   */
  dif_adc_ctrl_mode_t mode;
  /**
   * The time to allow the ADC to power up.
   *
   * Units: always-on clock cycles
   */
  uint8_t power_up_time_aon_cycles;
  /**
   * The sampling period when in Low Power Scan mode, i.e., how often the ADC
   * Controller wakes up the ADC to take a sample.
   *
   * Units: always-on clock cycles
   *
   * Only relevant in Low Power Scan mode.
   */
  uint32_t wake_up_time_aon_cycles;
  /**
   * The number of filter-matching samples to count in Low Power Scan mode
   * before switching to Normal Power Scan mode.
   *
   * Only relevant in Low Power Scan mode.
   */
  uint8_t num_low_power_samples;
  /**
   * The number of filter-matching samples to count in Normal Power Scan mode
   * before triggering a system wakeup and/or interrupt.
   */
  uint16_t num_normal_power_samples;
} dif_adc_ctrl_config_t;

/**
 * Runtime configuration for an ADC Controller filter.
 */
typedef struct dif_adc_ctrl_filter_config {
  /**
   * The ADC Controller filter this configuration applies to.
   */
  dif_adc_ctrl_filter_t filter;
  /**
   * The minimum voltage (inclusive) of the range defined by this filter.
   *
   * Valid range: [0, 1024)
   * Units: 2.148 mV (i.e., range / 2 ^ 10)
   */
  uint16_t min_voltage;
  /**
   * The maximum voltage (inclusive) of the range defined by this filter.
   *
   * Valid range: [0, 1024)
   * Units: 2.148 mV (i.e., range / 2 ^ 10)
   */
  uint16_t max_voltage;
  /**
   * Where a filter hit is classfied as an (inclusive) in-range hit, or
   * (exclusive) out-of-range hit.
   */
  bool in_range;
  /**
   * Whether to generate a system wakeup on a filter match after saturating the
   * `num_normal_power_samples` threshold in Normal Power Scan mode.
   */
  bool generate_wakeup_on_match;
  /**
   * Whether to generate a `debug_cable` interrupt on a filter match after
   * saturating the `num_normal_power_samples` threshold in Normal Power Scan
   * mode.
   */
  bool generate_irq_on_match;
} dif_adc_ctrl_filter_config_t;

/**
 * Configures an ADC Controller.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_configure(const dif_adc_ctrl_t *adc_ctrl,
                                    dif_adc_ctrl_config_t config);

/**
 * Configures a channel filter.
 *
 * This should be invoked for each desired filter _before_ the sampling sequence
 * is enabled via `dif_adc_ctrl_set_enabled()`.
 *
 * This only applies in Low / Normal Power Scan sampling modes.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param channel The channel of the filter to configure.
 * @param config Runtime configuration parameters for the filter.
 * @param enabled The enablement state to configure the filter in.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_configure_filter(const dif_adc_ctrl_t *adc_ctrl,
                                           dif_adc_ctrl_channel_t channel,
                                           dif_adc_ctrl_filter_config_t config,
                                           dif_toggle_t enabled);

/**
 * Sets the enablement state of the ADC Controller.
 *
 * Enabling the ADC Controller powers it up, while disabling the ADC Controller
 * powers it down and resets the sampling FSM. After powering up, sampling
 * begins, regardless of the operation mode.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param enabled The enablement state to configure the ADC Controller in.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_set_enabled(const dif_adc_ctrl_t *adc_ctrl,
                                      dif_toggle_t enabled);

/**
 * Gets the enablement state of the ADC Controller.
 *
 * If the ADC Controller is enabled, it is powered up, or being powered up.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param[out] is_enabled The enablement state of the ADC Controller.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_get_enabled(const dif_adc_ctrl_t *adc_ctrl,
                                      dif_toggle_t *is_enabled);

/**
 * Sets the enablement state of the specified filter for the specified channel.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param channel The channel the filter resides in.
 * @param filter The filter to set the enablement state of.
 * @param enabled The enablement state to configure the filter in.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_filter_set_enabled(const dif_adc_ctrl_t *adc_ctrl,
                                             dif_adc_ctrl_channel_t channel,
                                             dif_adc_ctrl_filter_t filter,
                                             dif_toggle_t enabled);

/**
 * Gets the enablement state of the specified filter for the specified channel.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param channel The channel the filter resides in.
 * @param filter The filter to get the enablement state of.
 * @param[out] is_enabled The enablement state of the filter.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_filter_get_enabled(const dif_adc_ctrl_t *adc_ctrl,
                                             dif_adc_ctrl_channel_t channel,
                                             dif_adc_ctrl_filter_t filter,
                                             dif_toggle_t *enabled);

/**
 * Get the sampled value from the specified channel that triggered the IRQ.
 *
 * Values are 10-bits in the range from 0V to 2.2V. Based on this, the
 * resolution (and units) of the sample are in increments of 2.148mV.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param channel The channel to read the sample from.
 * @param[out] value The value of the sample.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_get_triggered_value(const dif_adc_ctrl_t *adc_ctrl,
                                              dif_adc_ctrl_channel_t channel,
                                              uint16_t *value);

/**
 * Get the latest sampled value from the specified channel.
 *
 * Since in Normal Power Scan mode, sampling continues even after an IRQ has
 * been raised, the value returned by this function may be different than the
 * value returned by `dif_adc_ctrl_get_irq_value()`.
 *
 * Values are 10-bits in the range from 0V to 2.2V. Based on this, the
 * resolution (and units) of the sample are in increments of 2.148mV.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param channel The channel to read the sample from.
 * @param[out] value The value of the sample.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_get_latest_value(const dif_adc_ctrl_t *adc_ctrl,
                                           dif_adc_ctrl_channel_t channel,
                                           uint16_t *value);

/**
 * Reset all ADC Controller FSMs and counters, and if enabled, begin sampling
 * sequence.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_reset(const dif_adc_ctrl_t *adc_ctrl);

/**
 * Gets the cause(s) of a `debug_cable` IRQ.
 *
 * IRQs can be triggered by filter matches in Normal Power Scan mode (after
 * saturating the `num_normal_power_samples` threshold), or after a single
 * sample capture in Oneshot mode.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param[out] causes The causes of the IRQ (one or more
 *                    `dif_adc_ctrl_irq_cause_t`s ORed together).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_irq_get_causes(const dif_adc_ctrl_t *adc_ctrl,
                                         uint32_t *causes);

/**
 * Clears the cause(s) of a `debug_cable` IRQ.
 *
 * TODO(lowRISC/opentitan:#11354): future releases of the HW should hide the
 * filter and interrupt status registers behind the standardized IRQ registers.
 * For now, the autogenerated `dif_adc_ctrl_irq_acknowledge[_all]()` DIF may be
 * used to clear the main IRQ status register, while this DIF may be used to
 * clear the local cause / filter status registers.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param causes The causes of the IRQ (one or more `dif_adc_ctrl_irq_cause_t`s
 *               ORed together).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_irq_clear_causes(const dif_adc_ctrl_t *adc_ctrl,
                                           uint32_t causes);

/**
 * Sets the enablement of generating system wakeups on a filter match.
 *
 * Only relevant in Normal Power Scan mode (and Low Power Scan mode, which can
 * transition to Normal Power Scan mode).
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param filter A filter to enable wakeup triggering for.
 * @param enabled The enablement state to set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_filter_match_wakeup_set_enabled(
    const dif_adc_ctrl_t *adc_ctrl, dif_adc_ctrl_filter_t filter,
    dif_toggle_t enabled);

/**
 * Gets the enablement of generating system wakeups on a filter match.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param filter A filter to enable wakeup triggering for.
 * @param[out] is_enabled The enablement state retrieved.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_filter_match_wakeup_get_enabled(
    const dif_adc_ctrl_t *adc_ctrl, dif_adc_ctrl_filter_t filter,
    dif_toggle_t *is_enabled);

/**
 * Sets the enablement of generating a `debug_cable` IRQ for given cause(s).
 *
 * Causes can be filter matches (in Normal Power Scan mode), or when a sample is
 * complete (in Oneshot mode).
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param causes Causes (one or more `dif_adc_ctrl_irq_cause_t`s ORed together)
 *               to generate the `debug_cable` IRQ for.
 * @param enabled The enablement state to set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_irq_cause_set_enabled(const dif_adc_ctrl_t *adc_ctrl,
                                                uint32_t causes,
                                                dif_toggle_t enabled);

/**
 * Gets the causes that will generate a `debug_cable` IRQ.
 *
 * @param adc_ctrl An adc_ctrl handle.
 * @param[out] enabled_causes Causes (one or more `dif_adc_ctrl_irq_cause_t`s
 *                            ORed together) that will generate the
 *                            `debug_cable` IRQ.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_adc_ctrl_irq_cause_get_enabled(const dif_adc_ctrl_t *adc_ctrl,
                                                uint32_t *enabled_causes);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ADC_CTRL_H_
