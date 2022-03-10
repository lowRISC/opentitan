// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PATTGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PATTGEN_H_

/**
 * @file
 * @brief <a href="/hw/ip/pattgen/doc/">Pattern Generator</a> Device Interface
 * Functions
 */

#include <stdint.h>

#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_pattgen_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Helper X macro for defining enums and case statements related to Pattern
 * Generator channels. If an additional channel is ever added to the hardware,
 * this list can be updated.
 */
#define DIF_PATTGEN_CHANNEL_LIST(X) \
  X(0)                              \
  X(1)

/**
 * Helper macro for defining a `dif_pattgen_channel_t` enumeration constant.
 * @channel_ Pattern Generator channel of the enumeration constant.
 */
#define PATTGEN_CHANNEL_ENUM_INIT_(channel_) \
  kDifPattgenChannel##channel_ = channel_,

/**
 * A Pattern Generator channel.
 */
typedef enum dif_pattgen_channel {
  DIF_PATTGEN_CHANNEL_LIST(PATTGEN_CHANNEL_ENUM_INIT_)
} dif_pattgen_channel_t;

#undef PATTGEN_CHANNEL_ENUM_INIT_

/**
 * The polarity of a Pattern Generator channel.
 */
typedef enum dif_pattgen_polarity {
  /**
   * Low polarity indicates the output data signal (PDA) changes on a falling
   * output clock (PCL) edge.
   */
  kDifPattgenPolarityLow = 0,
  /**
   * High polarity indicates the output data signal (PDA) changes on a rising
   * output clock (PCL) edge.
   */
  kDifPattgenPolarityHigh = 1,
  /**
   * Number of polarity values, used for argument validation.
   */
  kDifPattgenPolarityCount = 2,
} dif_pattgen_polarity_t;

/**
 * Runtime configuration for a Pattern Generator channel.
 */
typedef struct dif_pattgen_channel_config {
  /**
   * The polarity of the channel.
   */
  dif_pattgen_polarity_t polarity;
  /**
   * The I/O clock divisor that determines the frequency of channel's clock.
   *
   * Specifically, the output clock frequency (f_pcl) is computed from the I/O
   * clock frequency (f_io_clk):
   *
   *            f_pcl = f_io_clk / (2 * (clock_divisor + 1))
   */
  uint32_t clock_divisor;
  /**
   * The lower 32-bits of the seed pattern.
   *
   * Some bits may go unused depending on the value of `seed_pattern_length`.
   */
  uint32_t seed_pattern_lower_word;
  /**
   * The upper 32-bits of the seed pattern.
   *
   * Some, or all, bits may go unused depending on the value of
   * `seed_pattern_length`.
   */
  uint32_t seed_pattern_upper_word;
  /**
   * The length of the seed pattern.
   *
   * Units: bits
   * Valid range: [1, 64]
   */
  uint8_t seed_pattern_length;
  /**
   * The number of times to repeat the pattern.
   *
   * Valid range: [1, 1024]
   */
  uint16_t num_pattern_repetitions;
} dif_pattgen_channel_config_t;

/**
 * Configures a Pattern Generator channel.
 *
 * This should be called once for each channel to be configured.
 *
 * Since writes to channel configuration registers have no effect when the
 * channel is enabled, this function will return `kDifError` if the channel is
 * enabled.
 *
 * @param pattgen A Pattern Generator handle.
 * @param channel The channel to configure.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pattgen_configure_channel(const dif_pattgen_t *pattgen,
                                           dif_pattgen_channel_t channel,
                                           dif_pattgen_channel_config_t config);

/**
 * Sets the enablement state of a Pattern Generator channel.
 *
 * @param pattgen A Pattern Generator handle.
 * @param channel The channel to set the enablement state of.
 * @param enabled The enablement state to configure the channel in.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pattgen_channel_set_enabled(const dif_pattgen_t *pattgen,
                                             dif_pattgen_channel_t channel,
                                             dif_toggle_t enabled);

/**
 * Gets the enablement state of a Pattern Generator channel.
 *
 * @param pattgen A Pattern Generator handle.
 * @param channel The channel to get the enablement state of.
 * @param[out] is_enabled The enablement state of the channel.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pattgen_channel_get_enabled(const dif_pattgen_t *pattgen,
                                             dif_pattgen_channel_t channel,
                                             dif_toggle_t *is_enabled);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PATTGEN_H_
