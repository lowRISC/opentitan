// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PINMUX_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PINMUX_H_

/**
 * @file
 * @brief <a href="/hw/ip/pinmux/doc/">Pin Multiplexer</a> Device Interface
 * Functions
 */

/**
 * Pin Multiplexer connects peripheral input/output signals to the Padring MIO
 * pad input/output signals.
 *
 * Every peripheral input signal is fed into a multiplexer, where selects
 * determine which Padring MIO pad input or constants should be connected to it.
 *
 * Every Padring MIO pad output signal is fed into a multiplexer, where selects
 * determine which peripheral output or constants should be connected to it.
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_pinmux_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Pin Multiplexer Padring pad kinds.
 *
 * A pad can be a Multiplexed (MIO) or Dedicated (DIO).
 */
typedef enum dif_pinmux_pad_kind {
  /**
   * Multiplexed Input/Output pad. Connected to a peripheral input or output
   * via a multiplexer matrix inside the a Pin Multiplexer.
   */
  kDifPinmuxPadKindMio = 0,
  /**
   * Dedicated Input/Output pad. Connected directly to a peripheral input
   * or output, bypassing the multiplexer matrix.
   */
  kDifPinmuxPadKindDio,
  kDifPinmuxPadKindCount,
} dif_pinmux_pad_kind_t;

/**
 * Pin Multiplexer functionality locking.
 *
 * Represents a target functionality to be locked for a given
 * pad/peripheral input.
 */
typedef enum dif_pinmux_lock_target {
  /**
   * Lock MIO pad input select for a given peripheral input. This means that
   * the peripheral input connection can no longer be changed.
   */
  kDifPinmuxLockTargetInsel = 0,
  /**
   * Lock peripheral output select for a given MIO pad output. This means
   * that the MIO pad output connection can no longer be changed.
   */
  kDifPinmuxLockTargetOutsel,
  /**
   * Lock the sleep mode configuration for a given MIO pad.
   */
  kDifPinmuxLockTargetMioSleep,
  /**
   * Lock the sleep mode configuration for a given DIO pad.
   */
  kDifPinmuxLockTargetDioSleep,
  /**
   * Lock physical characteristics configuration for a given MIO pad.
   */
  kDifPinmuxLockTargetMioPadAttr,
  /**
   * Lock physical characteristics configuration for a given DIO pad.
   */
  kDifPinmuxLockTargetDioPadAttr,
  /**
   * Lock wake-up detector configuration for a given detector.
   */
  kDifPinmuxLockTargetWakeupDetector,

} dif_pinmux_lock_target_t;

/**
 * Pin Multiplexer generic index.
 *
 * The meaning of this index changes between APIs, and must be documented in
 * the corresponding function description.
 */
typedef uint32_t dif_pinmux_index_t;

/**
 * Pad slew rate value.
 *
 * This selects between available slew rate values, where the largest number
 * produces the fastest slew rate. See the device's data sheet for the
 * particular mapping.
 */
typedef uint8_t dif_pinmux_pad_slew_rate_t;

/**
 * Pad drive strength value.
 *
 * This selects between available drive strength values, where the largest
 * number produces the highest drive strength. See the device's data sheet for
 * the particular mapping.
 */
typedef uint8_t dif_pinmux_pad_drive_strength_t;

/**
 * Pad attribute flag values
 *
 * This `enum` is a bitfield, meaning that it is allowed to pass combined value
 * of multiple individual attributes.
 *
 * Some attributes have defined meanings, others are implementation defined. Not
 * all pads will support all attributes, or attribute combinations. The Pin
 * Multiplexer DIF checks for conflicting or unsupported attributes provided by
 * the Write-Any Read-Legal (WARL) semantics of the underlying hardware. If the
 * combination of attributes is not supported - some/all of these attributes
 * will still be disabled (relevant bit unset in the attribute field).
 *
 * IMPORTANT:
 * - Functions are used to toggle these attributes, must signal an error if at
 *   least one of the attributes in the bitfield could not be toggled.
 */
typedef enum dif_pinmux_pad_attr_flags {
  kDifPinmuxPadAttrInvertLevel = 1 << 0,
  kDifPinmuxPadAttrVirtualOpenDrain = 1 << 1,
  kDifPinmuxPadAttrPullResistorEnable = 1 << 2,
  kDifPinmuxPadAttrPullResistorUp = 1 << 3,
  kDifPinmuxPadAttrKeeper = 1 << 4,
  kDifPinmuxPadAttrSchmittTrigger = 1 << 5,
  kDifPinmuxPadAttrOpenDrain = 1 << 6,
} dif_pinmux_pad_attr_flags_t;

/**
 * Pin multiplexer padring pad attributes.
 */
typedef struct dif_pinmux_pad_attr {
  /**
   * Slew rate attribute. A greater number produces a faster slew rate.
   */
  dif_pinmux_pad_slew_rate_t slew_rate;
  /**
   * Drive strength pad attribute. A greater number produces a stronger drive.
   */
  dif_pinmux_pad_drive_strength_t drive_strength;
  /**
   * A bit map of single-bit attribute flags. See dif_pinmux_pad_attr_flags_t
   * for the mapping and definitions.
   */
  dif_pinmux_pad_attr_flags_t flags;
} dif_pinmux_pad_attr_t;

/**
 * A sleep mode for a Padring DIO/MIO pad.
 *
 * This determines the behaviour of a pad in deep sleep state.
 *
 * NOTE:
 * After the chip has come back from deep sleep, the mode of the pad
 * persists until it is explicitly cleared by `dif_pinmux_sleep_clear_state`.
 * Calling `dif_pinmux_sleep_enable` will configure the pad mode for
 * the next deep sleep, however it will not change the current mode.
 */
typedef enum dif_pinmux_sleep_mode {
  /**
   * The pad is driven actively to zero.
   */
  kDifPinmuxSleepModeLow = 0,
  /**
   * The pad is driven actively to one.
   */
  kDifPinmuxSleepModeHigh,
  /**
   * The pad is left undriven. Note that the actual driving behaviour will
   * depend on the pull-up/-down configuration.
   */
  kDifPinmuxSleepModeHighZ,
  /**
   * Keep last driven value (including high-Z).
   */
  kDifPinmuxSleepModeKeep,
  kDifPinmuxSleepModeCount,
} dif_pinmux_sleep_mode_t;

/**
 * A Pin Multiplexer wake-up detection mode (edge triggered).
 */
typedef enum dif_pinmux_wakeup_mode {
  /**
   * Trigger a wakeup request when observing a positive edge.
   */
  kDifPinmuxWakeupModePositiveEdge = 0,
  /**
   * Trigger a wakeup request when observing a negative edge.
   */
  kDifPinmuxWakeupModeNegativeEdge,
  /**
   * Trigger a wakeup request when observing an edge in any direction.
   */
  kDifPinmuxWakeupModeAnyEdge,
  /**
   * Trigger a wakeup request when pin is driven HIGH for a certain amount of
   * always-on clock cycles as configured in
   * `dif_pinmux_wakeup_timed_config_t`, `counter_threshold` field.
   */
  kDifPinmuxWakeupModeTimedHigh,
  /**
   * Trigger a wakeup request when pin is driven LOW for a certain amount of
   * always-on clock cycles as configured in
   * `dif_pinmux_wakeup_timed_config_t`, `counter_threshold` field.
   */
  kDifPinmuxWakeupModeTimedLow,
  kDifPinmuxWakeupModeCount,
} dif_pinmux_wakeup_mode_t;

/**
 * A Pin Multiplexer common wake-up configuration between different modes.
 */
typedef struct dif_pinmux_wakeup_config {
  /**
   * Signal filter - signal must be stable for 4 always-on clock cycles
   * before the value is being forwarded. Can be used for debouncing.
   */
  dif_toggle_t signal_filter;
  /**
   * Pad type (MIO or DIO) to enable the wake-up detection for.
   */
  dif_pinmux_pad_kind_t pad_type;
  /**
   * Selects a specific pad. In the case of MIO, the pad select index is the
   * same as used for `dif_pinmux_input_select`, meaning that index 0 and 1 just
   * select constant 0, and the MIO pads live at indices >= 2. In the case of
   * DIO pads, the pad select index corresponds 1:1 to the DIO pad to be
   * selected.
   */
  dif_pinmux_index_t pad_select;
  /**
   * Wake-up detection mode.
   */
  dif_pinmux_wakeup_mode_t mode;
  /**
   * Counter threshold for `kDifPinmuxWakeupModeTimedLow` and
   * `kDifPinmuxWakeupModeTimedHigh` wake-up detector modes. The threshold is in
   * terms of always-on clock cycles.
   */
  uint8_t counter_threshold;
} dif_pinmux_wakeup_config_t;

/**
 * Locks out Pin Multiplexer functionality based on the `target` and `index`.
 *
 * This function allows for a fine grained locking of the Pin Multiplexer
 * parts. `index` changes meaning dependent on the `target`. For example, when
 * `target` is `kDifPinmuxLockTargetInsel`, `index` represents a peripheral
 * input for which the MIO input select functionality should be locked.
 *
 * NOTE:
 * Locking an already locked register will succeed with the `kDifOk`
 * return code.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param index Exact meaning is determined by the `target`, however, it
 *              represents one of the following: peripheral input index,
 *              MIO pad index, DIO pad index or a wakeup detector index.
 * @param target Target functionality to be locked.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_lock(const dif_pinmux_t *pinmux,
                             dif_pinmux_index_t index,
                             dif_pinmux_lock_target_t target);

/**
 * Obtains the Pin Multiplexer Pad lock status based on `target` and `index`.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param index Exact meaning is determined by the `target`, however, it
 *              represents one of the following: peripheral input index,
 *              MIO pad index, DIO pad index or a wakeup detector index.
 * @param target Target functionality to be locked.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_is_locked(const dif_pinmux_t *pinmux,
                                  dif_pinmux_index_t index,
                                  dif_pinmux_lock_target_t target,
                                  bool *is_locked);

/**
 * Sets a connection between a peripheral input and a MIO pad input.
 *
 * A peripheral input can be connected to any available MIO pad input.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param peripheral_input A Peripheral input index.
 * @param insel Input connection select - a MIO pad input to be connected to
 *              a peripheral input.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_input_select(const dif_pinmux_t *pinmux,
                                     dif_pinmux_index_t peripheral_input,
                                     dif_pinmux_index_t insel);

/**
 * Sets a connection between a MIO pad output and peripheral output.
 *
 * A MIO pad output can be connected to any available peripheral output.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param mio_pad_output Padring MIO output index.
 * @param outsel Peripheral output connection select - a Peripheral output to be
 *               connected to a MIO pad output.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_output_select(const dif_pinmux_t *pinmux,
                                      dif_pinmux_index_t mio_pad_output,
                                      dif_pinmux_index_t outsel);

/**
 * Writes attributes for a pad.
 *
 * This function completely overwrites the existing configuration of a pad, and
 * has both enable and disable semantics.
 *
 * Not all pads implement all attributes and some combinations cannot be
 * enabled together. This function returns a `kDifBadArg` error in case of
 * invalid `attrs_in`.
 * Conflicting attributes will be discarded by the hardware, and can be
 * identified by comparing `attrs_in` to `attrs_out`.
 *
 * IMPORTANT:
 * See `dif_pinmux_pad_attr` for information on which attributes are compulsory
 * and which invariants are mutually exclusive.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param pad Pad index to write the attributes for.
 * @param type Pad type (MIO or DIO).
 * @param attrs_in Attribute values to write.
 * @param attrs_out[out] The actual attributes written and accepted by the
 *                       hardware.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_pad_write_attrs(const dif_pinmux_t *pinmux,
                                        dif_pinmux_index_t pad,
                                        dif_pinmux_pad_kind_t type,
                                        dif_pinmux_pad_attr_t attrs_in,
                                        dif_pinmux_pad_attr_t *attrs_out);

/**
 * Get attributes for a pad.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param pad Pad index to obtain the attributes for.
 * @param type Pad type (MIO or DIO).
 * @param attrs[out] Obtained attributes.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_pad_get_attrs(const dif_pinmux_t *pinmux,
                                      dif_pinmux_index_t pad,
                                      dif_pinmux_pad_kind_t type,
                                      dif_pinmux_pad_attr_t *attrs);

/**
 * Enables deep sleep mode of a particular pad.
 *
 * NOTE:
 * After the chip has come back from deep sleep, the mode of a pad persists
 * until is explicitly cleared by `dif_pinmux_pad_sleep_clear_state`. Calling
 * `dif_pinmux_pad_sleep_enable` will configure a pad mode for the next deep
 * sleep, however it will not change the current mode.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param pad Pad index.
 * @param type Pad type (MIO or DIO).
 * @param mode Pad deep sleep mode.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_pad_sleep_enable(const dif_pinmux_t *pinmux,
                                         dif_pinmux_index_t pad,
                                         dif_pinmux_pad_kind_t type,
                                         dif_pinmux_sleep_mode_t mode);

/**
 * Disables deep sleep mode of a particular pad.
 *
 * NOTE:
 * After the chip has come back from deep sleep, the mode of a pad persists
 * until is explicitly cleared by `dif_pinmux_pad_sleep_clear_state`. Calling
 * `dif_pinmux_pad_sleep_enable` will configure a pad mode for the next deep
 * sleep, however it will not change the current mode.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param pad Pad index.
 * @param type Pad type (MIO or DIO).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_pad_sleep_disable(const dif_pinmux_t *pinmux,
                                          dif_pinmux_index_t pad,
                                          dif_pinmux_pad_kind_t type);

/**
 * Returns the state of a particular pad.
 *
 * When the pad is in deep sleep mode, the mode persists until is explicitly
 * cleared via `dif_pinmux_pad_sleep_clear_state`.
 *
 * @param padmux A Pin Multiplexer handle.
 * @param pad Pad index.
 * @param type Padring pad type (MIO or DIO).
 * @param[out] in_sleep_mode Pad state, `true` when in deep sleep mode.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_pad_sleep_get_state(const dif_pinmux_t *pinmux,
                                            dif_pinmux_index_t pad,
                                            dif_pinmux_pad_kind_t type,
                                            bool *in_sleep_mode);

/**
 * Clears deep sleep mode for a particular pad.
 *
 * When deep sleep mode is enabled for a pad, and the device has entered deep
 * sleep mode; upon wake-up, the deep sleep status of this pad can only be
 * cleared by calling this function. Re-configuring this pad will only take
 * effect during the next deep sleep.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param pad Pad index.
 * @param type Padring pad type (MIO or DIO).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_pad_sleep_clear_state(const dif_pinmux_t *pinmux,
                                              dif_pinmux_index_t pad,
                                              dif_pinmux_pad_kind_t type);

/**
 * Enables wake-up mode detection for a particular detector.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param detector A detector index.
 * @param config A wake-up detector configuration.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_wakeup_detector_enable(
    const dif_pinmux_t *pinmux, dif_pinmux_index_t detector,
    dif_pinmux_wakeup_config_t config);

/**
 * Disables wake-up detection for a particular detector.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param detector A detector index.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_wakeup_detector_disable(const dif_pinmux_t *pinmux,
                                                dif_pinmux_index_t detector);

/**
 * Clears the wake-up cause information.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_wakeup_cause_clear(const dif_pinmux_t *pinmux);

/**
 * Retrieves the detectors that have detected wake-up patterns.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param detector_map[out] A bit map representing detectors that have detected
 * wake-up patterns.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_wakeup_cause_get(const dif_pinmux_t *pinmux,
                                         uint32_t *detector_map);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PINMUX_H_
