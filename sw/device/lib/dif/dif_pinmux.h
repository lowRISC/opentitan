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
typedef enum dif_pinmux_toggle {
  /**
   * The "enabled" state.
   */
  kDifPinmuxToggleEnabled,
  /**
   * The "disabled" state.
   */
  kDifPinmuxToggleDisabled,
} dif_pinmux_toggle_t;

/**
 * Hardware instantiation parameters for a Pin Multiplexer.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_pinmux_params {
  /**
   * The base address for the a Pin Multiplexer hardware registers.
   */
  mmio_region_t base_addr;
} dif_pinmux_params_t;

/**
 * A handle to a Pin Multiplexer.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_pinmux {
  dif_pinmux_params_t params;
} dif_pinmux_t;

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
 * Pin multiplexer Padring pad attributes.
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
 *
 * - Related attribute invariants are mutually exclusive, and calling functions
 *   that are used to toggle these attributes must signal a respective `BadArg`
 *   error if more than one is specified. These include: `Pull*`, `Drive*` and
 *   `SlewRate*` family of attributes.
 *
 * - Compulsory attributes must be specified, and calling functions that are
 *   used to toggle these attributes must signal a respective `BadArg` error
 *   if such attribute is not specified. These include: `Drive*` and `SlewRate*`
 *   family of attributes.
 */
typedef enum dif_pinmux_pad_attr {
  kDifPinmuxPadAttrNone = 0,
  kDifPinmuxPadAttrIOInvert = 1 << 0,
  kDifPinmuxPadAttrVirtOpenDrain = 1 << 1,
  kDifPinmuxPadAttrPullDown = 1 << 2,
  kDifPinmuxPadAttrPullUp = 1 << 3,
  kDifPinmuxPadAttrKeeper = 1 << 4,
  kDifPinmuxPadAttrDriveWeakest = 1 << 5,
  kDifPinmuxPadAttrDriveWeak = 1 << 6,
  kDifPinmuxPadAttrDriveStrong = 1 << 7,
  kDifPinmuxPadAttrDriveStrongest = 1 << 8,
  kDifPinmuxPadAttrSchmittTrigger = 1 << 9,
  kDifPinmuxPadAttrSlewRateSlow = 1 << 10,
  kDifPinmuxPadAttrSlewRateFast = 1 << 11,
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
} dif_pinmux_sleep_mode_t;

/**
 * A Pin Multiplexer common wake-up configuration between different modes.
 */
typedef struct dif_pinmux_wakeup_config {
  /**
   * Signal filter - signal must be stable for 4 always-on clock cycles
   * before the value is being forwarded. can be used for debouncing.
   */
  dif_pinmux_toggle_t signal_filter;
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
} dif_pinmux_wakeup_config_t;

/**
 * A Pin Multiplexer wake-up detection mode (edge triggered).
 */
typedef enum dif_pinmux_wakeup_mode_edge {
  /**
   * Trigger a wakeup request when observing a positive edge.
   */
  kDifPinmuxWakeupModeEdgePositive = 0,
  /**
   * Trigger a wakeup request when observing a negative edge.
   */
  kDifPinmuxWakeupModeEdgeNegative,
  /**
   * Trigger a wakeup request when observing an edge in any direction.
   */
  kDifPinmuxWakeupModeEdge,
} dif_pinmux_wakeup_mode_edge_t;

/**
 * A Pin Multiplexer edge triggered wake-up mode configuration.
 */
typedef struct dif_pinmux_wakeup_edge_config {
  /**
   * Wake-up detection mode.
   */
  dif_pinmux_wakeup_mode_edge_t mode;
  /**
   * Common configuration between different wake-up modes.
   */
  dif_pinmux_wakeup_config_t common;
} dif_pinmux_wakeup_edge_config_t;

/**
 * Pin Multiplexer wake-up detection mode (timed).
 */
typedef enum dif_pinmux_wakeup_mode_timed {
  /**
   * Trigger a wakeup request when pin is driven HIGH for a certain amount of
   * always-on clock cycles as configured in
   * `dif_pinmux_wakeup_timed_config_t`, `counter_threshold` field.
   */
  kDifPinmuxWakeupModeTimedHigh = 0,
  /**
   * Trigger a wakeup request when pin is driven LOW for a certain amount of
   * always-on clock cycles as configured in
   * `dif_pinmux_wakeup_timed_config_t`, `counter_threshold` field.
   */
  kDifPinmuxWakeupModeTimedLow,
} dif_pinmux_wakeup_mode_timed_t;

/**
 * A Pin Multiplexer timed wake-up mode configuration.
 */
typedef struct dif_pinmux_wakeup_timed_config {
  /**
   * Wake-up detection mode.
   */
  dif_pinmux_wakeup_mode_timed_t mode;
  /**
   * Counter threshold for `kDifPinmuxWakeupModeTimedLow` and
   * `kDifPinmuxWakeupModeTimedHigh` wake-up detector modes. The threshold is in
   * terms of always-on clock cycles.
   */
  uint8_t counter_threshold;
  /**
   * Common configuration between different wake-up modes.
   */
  dif_pinmux_wakeup_config_t common;
} dif_pinmux_wakeup_timed_config_t;

/**
 * The result of a Pin Multiplexer operation.
 */
typedef enum dif_pinmux_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifPinmuxOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  kDifPinmuxError = 1,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifPinmuxBadArg = 2,
} dif_pinmux_result_t;

/**
 * Creates a new handle for a Pin Multiplexer.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param[out] pinmux Out param for the initialized handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pinmux_result_t dif_pinmux_init(dif_pinmux_params_t params,
                                    dif_pinmux_t *pinmux);

/**
 * Locks out Pin Multiplexer functionality based on the `target` and `index`.
 *
 * This function allows for a fine grained locking of the Pin Multiplexer
 * parts. `index` changes meaning dependent on the `target`. For example, when
 * `target` is `kDifPinmuxLockTargetInsel`, `index` represents a peripheral
 * input for which the MIO input select functionality should be locked.
 *
 * NOTE:
 * Locking an already locked register will succeed with the `kDifPinmuxOk`
 * return code.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param index Exact meaning is determined by the `target`, however, it
 *              represents one of the following: peripheral input index,
 *              MIO pad index, DIO pad index or a wakeup detector index.
 * @param target Target functionality to be locked.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pinmux_result_t dif_pinmux_lock(const dif_pinmux_t *pinmux,
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
DIF_WARN_UNUSED_RESULT
dif_pinmux_result_t dif_pinmux_is_locked(const dif_pinmux_t *pinmux,
                                         dif_pinmux_index_t index,
                                         dif_pinmux_lock_target_t target,
                                         bool *is_locked);

/**
 * The result of a Pin Multiplexer input or output select operations.
 */
typedef enum dif_pinmux_select_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifPinmuxSelectOk = kDifPinmuxOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifPinmuxSelectError = kDifPinmuxError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifPinmuxSelectBadArg = kDifPinmuxBadArg,

  /**
   * Indicates that the operation is not permitted (locked).
   */
  kDifPinmuxSelectLocked,
} dif_pinmux_select_result_t;

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
DIF_WARN_UNUSED_RESULT
dif_pinmux_select_result_t dif_pinmux_input_select(
    const dif_pinmux_t *pinmux, dif_pinmux_index_t peripheral_input,
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
DIF_WARN_UNUSED_RESULT
dif_pinmux_select_result_t dif_pinmux_output_select(
    const dif_pinmux_t *pinmux, dif_pinmux_index_t mio_pad_output,
    dif_pinmux_index_t outsel);

/**
 * Pin Multiplexer Padring pad attributes write error codes.
 */
typedef enum dif_pinmux_pad_write_attrs_result {
  kDifPinmuxPadWriteAttrsOk = kDifPinmuxOk,
  kDifPinmuxPadWriteAttrsError = kDifPinmuxError,
  kDifPinmuxPadWriteAttrsBadArg = kDifPinmuxBadArg,
  /**
   * Peripheral is locked and attributes cannot be changed. Only a read has been
   * performed and this error is recoverable but any operation that writes to
   * the registers will fail.
   */
  kDifPinmuxPadWriteAttrsLocked,
  /**
   * Attribute change failed because it would result in conflicting attributes
   * with another already enabled attribute. The change can be re-attempted with
   * different bits. This could also occur if the attribute register already
   * contained a conflicting set of attributes (e.g. because they have been
   * written outside of the DIF with conflicting values).
   */
  kDifPinmuxPadWriteAttrsConflict,
} dif_pinmux_pad_write_attrs_result_t;

/**
 * Writes attributes for a pad.
 *
 * This function completely overwrites the existing configuration of a pad, and
 * has both enable and disable semantics.
 *
 * Not all pads implement all attributes and some combinations cannot be
 * enabled together. This function returns a
 * `kDifPinmuxPadWriteAttrsConflict` error in case of invalid `attrs_in`.
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
 * @param attrs_in Attributes to write. A set bit writes an attribute, a
 *                 clear bit leaves it in its existing state.
 * @param attrs_out[out] The actual attributes written and accepted by the
 *                       hardware.
 * @return The result of the operation.
 */
dif_pinmux_pad_write_attrs_result_t dif_pinmux_pad_write_attrs(
    const dif_pinmux_t *pinmux, dif_pinmux_index_t pad,
    dif_pinmux_pad_kind_t type, dif_pinmux_pad_attr_t attrs_in,
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
dif_pinmux_result_t dif_pinmux_pad_get_attrs(const dif_pinmux_t *pinmux,
                                             dif_pinmux_index_t pad,
                                             dif_pinmux_pad_kind_t type,
                                             dif_pinmux_pad_attr_t *attrs);

/**
 * The result of a Pin Multiplexer enable/disable operations.
 */
typedef enum dif_pinmux_toggle_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifPinmuxToggleOk = kDifPinmuxOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifPinmuxToggleError = kDifPinmuxError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifPinmuxToggleBadArg = kDifPinmuxBadArg,

  /**
   * Indicates that the operation is not permitted (locked).
   */
  kDifPinmuxToggleLocked,
} dif_pinmux_toggle_result_t;

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
DIF_WARN_UNUSED_RESULT
dif_pinmux_toggle_result_t dif_pinmux_pad_sleep_enable(
    const dif_pinmux_t *pinmux, dif_pinmux_index_t pad,
    dif_pinmux_pad_kind_t type, dif_pinmux_sleep_mode_t mode);

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
DIF_WARN_UNUSED_RESULT
dif_pinmux_toggle_result_t dif_pinmux_pad_sleep_disable(
    const dif_pinmux_t *pinmux, dif_pinmux_index_t pad,
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
DIF_WARN_UNUSED_RESULT
dif_pinmux_result_t dif_pinmux_pad_sleep_get_state(const dif_pinmux_t *pinmux,
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
DIF_WARN_UNUSED_RESULT
dif_pinmux_result_t dif_pinmux_pad_sleep_clear_state(
    const dif_pinmux_t *pinmux, dif_pinmux_index_t pad,
    dif_pinmux_pad_kind_t type);

/**
 * Enables edge triggered wake-up mode detection for a particular detector.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param detector A detector index.
 * @param config A wake-up detector configuration.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pinmux_toggle_result_t dif_pinmux_wakeup_detector_enable_edge(
    const dif_pinmux_t *pinmux, dif_pinmux_index_t detector,
    dif_pinmux_wakeup_edge_config_t config);

/**
 * Enables edge timed wake-up mode detection for a particular detector.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param detector A detector index.
 * @param config A wake-up detector configuration.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pinmux_toggle_result_t dif_pinmux_wakeup_detector_enable_timed(
    const dif_pinmux_t *pinmux, dif_pinmux_index_t detector,
    dif_pinmux_wakeup_timed_config_t config);

/**
 * Disables wake-up detection for a particular detector.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param detector A detector index.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pinmux_toggle_result_t dif_pinmux_wakeup_detect_disable(
    const dif_pinmux_t *pinmux, dif_pinmux_index_t detector);

/**
 * Clears the wake-up cause information.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pinmux_result_t dif_pinmux_wakeup_cause_clear(const dif_pinmux_t *pinmux);

/**
 * Retrieves the index of a detector that has triggered a wake-up event.
 *
 * @param pinmux A Pin Multiplexer handle.
 * @param detector[out] A detector index.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pinmux_result_t dif_pinmux_wakeup_cause_get(const dif_pinmux_t *pinmux,
                                                dif_pinmux_index_t *detector);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PINMUX_H_
