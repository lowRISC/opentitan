// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SYSRST_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SYSRST_CTRL_H_

/**
 * @file
 * @brief <a href="/hw/ip/sysrst_ctrl/doc/">System Reset Controller</a> Device
 * Interface Functions
 */

#include "sw/device/lib/dif/autogen/dif_sysrst_ctrl_autogen.h"
#include "sysrst_ctrl_regs.h"  // Generated.

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A System Reset Controller key combination.
 */
typedef enum dif_sysrst_ctrl_key_combo {
  /**
   * Key combination 0.
   */
  kDifSysrstCtrlKeyCombo0 = 1U << 0,
  /**
   * Key combination 1.
   */
  kDifSysrstCtrlKeyCombo1 = 1U << 1,
  /**
   * Key combination 2.
   */
  kDifSysrstCtrlKeyCombo2 = 1U << 2,
  /**
   * Key combination 3.
   */
  kDifSysrstCtrlKeyCombo3 = 1U << 3,
  /**
   * All key combination ORed together.
   *
   * This is useful when clearing all key combination IRQ causes at once, e.g.,
   * when initializing the System Reset Controller.
   */
  kDifSysrstCtrlKeyComboAll = (1U << 4) - 1,
} dif_sysrst_ctrl_key_combo_t;

/**
 * System Reset Controller keys that can form a key combination.
 */
typedef enum dif_sysrst_ctrl_key {
  /**
   * Key 0.
   */
  kDifSysrstCtrlKey0 = 1U << 0,
  /**
   * Key 1.
   */
  kDifSysrstCtrlKey1 = 1U << 1,
  /**
   * Key 2.
   */
  kDifSysrstCtrlKey2 = 1U << 2,
  /**
   * Power button key.
   */
  kDifSysrstCtrlKeyPowerButton = 1U << 3,
  /**
   * AC power preset key.
   */
  kDifSysrstCtrlKeyAcPowerPresent = 1U << 4,
  /**
   * All keys ORed together.
   */
  kDifSysrstCtrlKeyAll = (1U << 5) - 1,
} dif_sysrst_ctrl_key_t;

/**
 * System Reset Controller key combination detection actions.
 */
typedef enum dif_sysrst_ctrl_key_combo_action {
  /**
   * Disable / disconnect battery.
   */
  kDifSysrstCtrlKeyComboActionBatteryDisable = 1U << 0,
  /**
   * Issue an interrupt to the processor.
   */
  kDifSysrstCtrlKeyComboActionInterrupt = 1U << 1,
  /**
   * Assert the embedded controller reset for a specified duration.
   */
  kDifSysrstCtrlKeyComboActionEcReset = 1U << 2,
  /**
   * Issue a reset request to the reset manager block.
   */
  kDifSysrstCtrlKeyComboActionSelfReset = 1U << 3,
  /**
   * All actions.
   */
  kDifSysrstCtrlKeyComboActionAll = (1U << 4) - 1,
} dif_sysrst_ctrl_key_combo_action_t;

/**
 * Runtime configuration for the System Reset Controller key combination
 * detection feature.
 */
typedef struct dif_sysrst_ctrl_key_combo_config {
  /**
   * The keys that comprise the key combination to detect (i.e., one or more
   * `dif_sysrst_ctrl_key_t`s ORed together).
   */
  uint32_t keys;
  /**
   * The duration the key combination should be pressed to trigger an action.
   *
   * Units: increments of 5us; [0, 2^32) represents [0, 60) seconds.
   */
  uint32_t detection_time_threshold;
  /**
   * The actions to trigger after detecting the key press combination (one or
   * more `dif_sysrst_ctrl_key_combo_action_t`s ORed together).
   */
  uint32_t actions;
  /**
   * The embedded controller's reset pulse width.
   *
   * Note: only applicable if the `kDifSysrstCtrlKeyComboActionEcReset` action
   * is enabled for the key combination.
   *
   * Units: increments of 5us; [0, 2^16) represents [10, 200) milliseconds.
   */
  uint16_t embedded_controller_reset_duration;
} dif_sysrst_ctrl_key_combo_config_t;

/**
 * System Reset Controller input signal changes that may be detected.
 */
typedef enum dif_sysrst_ctrl_input_change {
  /**
   * Power button input signal high-to-low.
   */
  kDifSysrstCtrlInputPowerButtonH2L = 1U << 0,
  /**
   * Key 0 input signal high-to-low.
   */
  kDifSysrstCtrlInputKey0H2L = 1U << 1,
  /**
   * Key 1 input signal high-to-low.
   */
  kDifSysrstCtrlInputKey1H2L = 1U << 2,
  /**
   * Key 2 input signal high-to-low.
   */
  kDifSysrstCtrlInputKey2H2L = 1U << 3,
  /**
   * AC power present input signal high-to-low.
   */
  kDifSysrstCtrlInputAcPowerPresetH2L = 1U << 4,
  /**
   * Embedded controller reset input signal high-to-low.
   */
  kDifSysrstCtrlInputEcResetH2L = 1U << 5,
  /**
   * Flash write protect input signal high-to-low.
   */
  kDifSysrstCtrlInputFlashWriteProtectH2L = 1U << 6,
  /**
   * Power button input signal low-to-high.
   */
  kDifSysrstCtrlInputPowerButtonL2H = 1U << 7,
  /**
   * Key 0 input signal low-to-high.
   */
  kDifSysrstCtrlInputKey0L2H = 1U << 8,
  /**
   * Key 1 input signal low-to-high.
   */
  kDifSysrstCtrlInputKey1L2H = 1U << 9,
  /**
   * Key 2 input signal low-to-high.
   */
  kDifSysrstCtrlInputKey2L2H = 1U << 10,
  /**
   * AC power present input signal low-to-high.
   */
  kDifSysrstCtrlInputAcPowerPresetL2H = 1U << 11,
  /**
   * Embedded controller reset input signal low-to-high.
   */
  kDifSysrstCtrlInputEcResetL2H = 1U << 12,
  /**
   * Flash write protect input signal low-to-high.
   */
  kDifSysrstCtrlInputFlashWriteProtectL2H = 1U << 13,
  /**
   * All input signal transitions.
   */
  kDifSysrstCtrlInputAll = ((1U << 14) - 1),
} dif_sysrst_ctrl_input_change_t;

/**
 * System Reset Controller key interrupt sources.
 */
typedef enum dif_sysrst_ctrl_key_intr_src {
  /**
   * Power button input signal high-to-low.
   */
  kDifSysrstCtrlKeyIntrStatusInputPowerButtonH2L =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_PWRB_H2L_BIT,
  /**
   * Key 0 input signal high-to-low.
   */
  kDifSysrstCtrlKeyIntrStatusInputKey0H2L =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_KEY0_IN_H2L_BIT,
  /**
   * Key 1 input signal high-to-low.
   */
  kDifSysrstCtrlKeyIntrStatusInputKey1H2L =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_KEY1_IN_H2L_BIT,
  /**
   * Key 2 input signal high-to-low.
   */
  kDifSysrstCtrlKeyIntrStatusInputKey2H2L =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_KEY2_IN_H2L_BIT,
  /**
   * AC power present input signal high-to-low.
   */
  kDifSysrstCtrlKeyIntrStatusInputAcPowerPresetH2L =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_AC_PRESENT_H2L_BIT,
  /**
   * Embedded controller reset input signal high-to-low.
   */
  kDifSysrstCtrlKeyIntrStatusInputEcResetH2L =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_EC_RST_L_H2L_BIT,
  /**
   * Flash write protect input signal high-to-low.
   */
  kDifSysrstCtrlKeyIntrStatusInputFlashWriteProtectH2L =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_FLASH_WP_L_H2L_BIT,
  /**
   * Power button input signal low-to-high.
   */
  kDifSysrstCtrlKeyIntrStatusInputPowerButtonL2H =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_PWRB_L2H_BIT,
  /**
   * Key 0 input signal low-to-high.
   */
  kDifSysrstCtrlKeyIntrStatusInputKey0L2H =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_KEY0_IN_L2H_BIT,
  /**
   * Key 1 input signal low-to-high.
   */
  kDifSysrstCtrlKeyIntrStatusInputKey1L2H =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_KEY1_IN_L2H_BIT,
  /**
   * Key 2 input signal low-to-high.
   */
  kDifSysrstCtrlKeyIntrStatusInputKey2L2H =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_KEY2_IN_L2H_BIT,
  /**
   * AC power present input signal low-to-high.
   */
  kDifSysrstCtrlKeyIntrStatusInputAcPowerPresetL2H =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_AC_PRESENT_L2H_BIT,
  /**
   * Embedded controller reset input signal low-to-high.
   */
  kDifSysrstCtrlKeyIntrStatusInputEcResetL2H =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_EC_RST_L_L2H_BIT,
  /**
   * Flash write protect input signal low-to-high.
   */
  kDifSysrstCtrlKeyIntrStatusInputFlashWriteProtectL2H =
      1U << SYSRST_CTRL_KEY_INTR_STATUS_FLASH_WP_L_L2H_BIT,
} dif_sysrst_ctrl_key_intr_src_t;

/**
 * System Reset Controller combo interrupt sources.
 */
typedef enum dif_sysrst_ctrl_combo_intr_src {
  /**
   * Power button input signal high-to-low.
   */
  kDifSysrstCtrlComboIntrStatusCombo0H2L =
      1U << SYSRST_CTRL_COMBO_INTR_STATUS_COMBO0_H2L_BIT,
  /**
   * Key 0 input signal high-to-low.
   */
  kDifSysrstCtrlComboIntrStatusCombo1H2L =
      1U << SYSRST_CTRL_COMBO_INTR_STATUS_COMBO1_H2L_BIT,
  /**
   * Key 1 input signal high-to-low.
   */
  kDifSysrstCtrlComboIntrStatusCombo2H2L =
      1U << SYSRST_CTRL_COMBO_INTR_STATUS_COMBO2_H2L_BIT,
  /**
   * Key 2 input signal high-to-low.
   */
  kDifSysrstCtrlComboIntrStatusCombo3H2L =
      1U << SYSRST_CTRL_COMBO_INTR_STATUS_COMBO3_H2L_BIT,
} dif_sysrst_ctrl_combo_intr_src_t;

/**
 * Runtime configuration for the System Reset Controller input signal change
 * detection feature.
 */
typedef struct dif_sysrst_ctrl_input_change_config {
  /**
   * A combination of input signal changes to detect (one or more
   * `dif_sysrst_ctrl_input_change_t`s ORed together).
   */
  uint32_t input_changes;
  /**
   * The time to allow the input signal to stabilize before reevaluating its
   * value to decide whether to trigger an interrupt.
   *
   * Units: increments of 5us; [0, 2^16) represents [0, 200) milliseconds.
   */
  uint16_t debounce_time_threshold;
} dif_sysrst_ctrl_input_change_config_t;

/**
 * Runtime configuration for the System Reset Controller key signal
 * auto-override feature.
 *
 * Upon detection of a Power Button high-to-low transition, the signals from
 * generic keys 0 through 2 may be overriden with specified values.
 */
typedef struct dif_sysrst_ctrl_auto_override_config {
  /**
   * The time to allow the Power Button signal to stabilize before reevaluating
   * its value to decide whether it was pressed.
   *
   * Units: increments of 5us; [0, 2^16) represents [0, 200) milliseconds.
   */
  uint16_t debounce_time_threshold;
  /**
   * Whether to override the key 0 signal.
   */
  dif_toggle_t override_key_0;
  /**
   * The value to override onto the key 0 signal.
   */
  bool key_0_override_value;
  /**
   * Whether to override the key 1 signal.
   */
  dif_toggle_t override_key_1;
  /**
   * The value to override onto the key 1 signal.
   */
  bool key_1_override_value;
  /**
   * Whether to override the key 2 signal.
   */
  dif_toggle_t override_key_2;
  /**
   * The value to override onto the key 2 signal.
   */
  bool key_2_override_value;
} dif_sysrst_ctrl_auto_override_config_t;

/**
 * System Reset Controller pins that can be inverted, read, or overridden.
 */
typedef enum dif_sysrst_ctrl_pin {
  /**
   * Key 0 input.
   */
  kDifSysrstCtrlPinKey0In = 1U << 0,
  /**
   * Key 0 output.
   */
  kDifSysrstCtrlPinKey0Out = 1U << 1,
  /**
   * Key 1 input.
   */
  kDifSysrstCtrlPinKey1In = 1U << 2,
  /**
   * Key 1 output.
   */
  kDifSysrstCtrlPinKey1Out = 1U << 3,
  /**
   * Key 2 input.
   */
  kDifSysrstCtrlPinKey2In = 1U << 4,
  /**
   * Key 2 output.
   */
  kDifSysrstCtrlPinKey2Out = 1U << 5,
  /**
   * Power button input.
   */
  kDifSysrstCtrlPinPowerButtonIn = 1U << 6,
  /**
   * Power button output.
   */
  kDifSysrstCtrlPinPowerButtonOut = 1U << 7,
  /**
   * AC power preset input.
   */
  kDifSysrstCtrlPinAcPowerPresentIn = 1U << 8,
  /**
   * Battery disable output.
   */
  kDifSysrstCtrlPinBatteryDisableOut = 1U << 9,
  /**
   * Lid open input.
   */
  kDifSysrstCtrlPinLidOpenIn = 1U << 10,
  /**
   * Z3 Wakeup output.
   */
  kDifSysrstCtrlPinZ3WakeupOut = 1U << 11,
  /**
   * Embedded controller reset inout.
   */
  kDifSysrstCtrlPinEcResetInOut = 1U << 12,
  /**
   * Flash write protect inout.
   */
  kDifSysrstCtrlPinFlashWriteProtectInOut = 1U << 13,
  /**
   * All non open drain pins.
   */
  kDifSysrstCtrlPinAllNonOpenDrain = (1U << 12) - 1,
} dif_sysrst_ctrl_pin_t;

/**
 * Runtime configuration for the System Reset Controller output pin override
 * feature.
 */
typedef struct dif_sysrst_ctrl_pin_config_t {
  /**
   * The enablement of the output pin's override feature.
   */
  dif_toggle_t enabled;
  /**
   * Whether to allow overriding the output pin with a value of 0.
   */
  bool allow_zero;
  /**
   * Whether to allow overriding the output pin with a value of 1.
   */
  bool allow_one;
  /**
   * The override value to write.
   *
   * Note: writing a non-allowable value will cause
   * `dif_sysrst_ctrl_output_pin_override_configure()` to return `kDifBadArg`.
   */
  bool override_value;
} dif_sysrst_ctrl_pin_config_t;

/**
 * Runtime configuration for the System Reset Controller ultra-low-power (ULP)
 * wakeup feature.
 *
 * When enabled, detection of any of the following conditions:
 *
 * 1. HIGH level on the AC Power present signal, or
 * 2. HIGH --> LOW transition on the Power Button signal, or
 * 3. LOW --> HIGH transition on the Lid Open signal,
 *
 * will cause the System Reset Controller to assert the Z3 Wakeup output signal
 * and trigger an interrupt, which will also issue a wakeup request to the power
 * manager.
 */
typedef struct dif_sysrst_ctrl_ulp_wakeup_config_t {
  /**
   * The enablement of the ULP wakeup feature.
   */
  dif_toggle_t enabled;
  /**
   * The time to allow the AC Power present signal to stabilize before
   * reevaluating its value to decide whether it was activated.
   *
   * Units: increments of 5us; [0, 2^16) represents [10, 200) milliseconds.
   */
  uint16_t ac_power_debounce_time_threshold;
  /**
   * The time to allow the Lid Open signal to stabilize before reevaluating its
   * value to decide whether it was activated.
   *
   * Units: increments of 5us; [0, 2^16) represents [10, 200) milliseconds.
   */
  uint16_t lid_open_debounce_time_threshold;
  /**
   * The time to allow the Power Button signal to stabilize before reevaluating
   * its value to decide whether it was pressed.
   *
   * Units: increments of 5us; [0, 2^16) represents [10, 200) milliseconds.
   */
  uint16_t power_button_debounce_time_threshold;
} dif_sysrst_ctrl_ulp_wakeup_config_t;

/**
 * Configures a System Reset Controller's key combination detection feature.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param key_combo Key combination to configure.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_key_combo_detect_configure(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_key_combo_t key_combo,
    dif_sysrst_ctrl_key_combo_config_t config);

/**
 * Configures a System Reset Controller's input signal change detection feature.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_input_change_detect_configure(
    const dif_sysrst_ctrl_t *sysrst_ctrl,
    dif_sysrst_ctrl_input_change_config_t config);

/**
 * Configures a System Reset Controller's output pin override feature.
 *
 * Note, only output (or inout) pins may be overriden, i.e., set to a specific
 * value. Attempting to configure the override feature for input pins will
 * return `kDifBadArg`.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param output_pin Output pin to configure.
 * @param config Output pin override configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_output_pin_override_configure(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t output_pin,
    dif_sysrst_ctrl_pin_config_t config);

/**
 * Configures a System Reset Controller's key signal auto-override feature.
 *
 * Upon detection of a Power Button high-to-low transition, the signals from
 * generic keys 0 through 2 may be overriden with specified values.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param config Runtime configuration parameters.
 * @param enabled Whether to enable the feature or not.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_auto_override_configure(
    const dif_sysrst_ctrl_t *sysrst_ctrl,
    dif_sysrst_ctrl_auto_override_config_t config, dif_toggle_t enabled);

/**
 * Configures a System Reset Controller's ultra-low-power (ULP) wakeup feature.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_ulp_wakeup_configure(
    const dif_sysrst_ctrl_t *sysrst_ctrl,
    dif_sysrst_ctrl_ulp_wakeup_config_t config);

/**
 * Sets the enablement state of a System Reset Controller's ultra-low-power
 * (ULP) wakeup feature.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param enabled The enablement state to configure the ULP wakeup feature in.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_ulp_wakeup_set_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_toggle_t enabled);

/**
 * Gets the enablement state of a System Reset Controller's ultra-low-power
 * (ULP) wakeup feature.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param[out] is_enabled The enablement state of the ULP wakeup feature.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_ulp_wakeup_get_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_toggle_t *is_enabled);

/**
 * Sets the inversion state a System Reset Controller's input and output pins.
 *
 * Note, only input and output (NOT inout) pins may be inverted. Attempting
 * to set the inversion state of inout pins will return `kDifBadArg`.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param pins The input and output pins to set the inverted state of (i.e., one
 *             or more `dif_sysrst_ctrl_pin_t`s ORed together).
 * @param inverted The inverted state to configure for the pins.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_pins_set_inverted(
    const dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t pins, bool inverted);

/**
 * Gets the inversion state a System Reset Controller's input and output pins.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param[out] inverted_pins The input and output pins that are inverted (i.e.,
 *                           one or more `dif_sysrst_ctrl_pin_t`s ORed
 *                           together).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_pins_get_inverted(
    const dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t *inverted_pins);

/**
 * Sets allowable override values for a System Reset Controller's output pin.
 *
 * Note, only output (or inout) pins may be overriden, i.e., set to a specific
 * value. Attempting to set the allowable override values for input pins will
 * return `kDifBadArg`.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param pin The output pin whose allowable override values should be set.
 * @param allow_zero Whether to allow overriding the pin's value to 0.
 * @param allow_one Whether to allow overriding the pin's value to 1.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_output_pin_override_set_allowed(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    bool allow_zero, bool allow_one);

/**
 * Gets allowable override values for a System Reset Controller's output pin.
 *
 * Note, only output (or inout) pins may be overriden, i.e., set to a specific
 * value. Attempting to get the allowable override values for input pins will
 * return `kDifBadArg`.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param pin The allowable override values to get for an output pin.
 * @param[out] allow_zero Whether overriding the pin's value to 0 is allowed.
 * @param[out] allow_one Whether overriding the pin's value to 1 is allowed.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_output_pin_override_get_allowed(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    bool *allow_zero, bool *allow_one);

/**
 * Sets the enablement of a System Reset Controller's output pin override
 * feature.
 *
 * Note, only output (or inout) pins may be overriden, i.e., set to a specific
 * value. Attempting to set the enablement of the override feature for input
 * pins will return `kDifBadArg`.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param pin The output pin whose override feature should be set.
 * @param enabled The enablement state to configure the override feature in.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_output_pin_override_set_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    dif_toggle_t enabled);

/**
 * Gets the enablement of a System Reset Controller's output pin override
 * feature.
 *
 * Note, only output (or inout) pins may be overriden, i.e., set to a specific
 * value. Attempting to get the enablement of the override feature for input
 * pins will return `kDifBadArg`.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param pin The output pin whose override feature should be set.
 * @param[out] is_enabled The enablement state the override feature is
 * configured in.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_output_pin_override_get_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    dif_toggle_t *is_enabled);

/**
 * Sets the override value of a System Reset Controller's output pin (like
 * writing to a GPIO pin).
 *
 * Note, only output (or inout) pins may be overriden, i.e., set to a specific
 * value. Attempting to set the override value of an input pin will return
 * `kDifBadArg`.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param pin The output pin to override.
 * @param value The override value to set on the pin.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_output_pin_set_override(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    bool value);

/**
 * Gets the override value of a System Reset Controller's output pin (like
 * writing to a GPIO pin).
 *
 * Note, only output (or inout) pins may be overriden, i.e., set to a specific
 * value. Attempting to get the override value of an input pin will return
 * `kDifBadArg`.
 *
 * Additionally, this will return the configured override value of an output pin
 * regardless if the override function is enabled or the override value is
 * allowed.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param pin The output pin to override.
 * @param[out] value The override value set on the pin.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_output_pin_get_override(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    bool *value);

/**
 * Reads a System Reset Controller's input pin (like a GPIO pin).
 *
 * Note, only input (or inout) pins may be read. Attempting to read the value of
 * an output pin will return `kDifBadArg`.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param pin The pin to read.
 * @param[out] value The value set on the pin.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_input_pin_read(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    bool *value);

/**
 * Sets the enablement of a System Reset Controller's key signal auto-override
 * feature.
 *
 * Note, this feature is only available for keys 0, 1, and 2. Attempting to
 * enable the auto-override feature on non-supported keys will return
 * `kDifBadArg`.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param key The key to enable the override feature for.
 * @param enabled Whether to enable the feature or not.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_auto_override_set_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_key_t key,
    dif_toggle_t enabled);

/**
 * Gets the enablement of a System Reset Controller's key signal auto-override
 * feature.
 *
 * Note, this feature is only available for keys 0, 1, and 2. Attempting to
 * check whether the auto-override feature is enabled non-supported keys will
 * return `kDifBadArg`.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param key The key the override feature is enabled for.
 * @param[out] is_enabled Whether the feature is enabled or not.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_auto_override_get_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_key_t key,
    dif_toggle_t *is_enabled);

/**
 * Gets the cause(s) of a key combination detection IRQ.
 *
 * @param sysrst_ctrl An sysrst_ctrl handle.
 * @param[out] causes The causes of the IRQ (one or more
 *             `dif_sysrst_ctrl_key_combo_t`s ORed together).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_key_combo_irq_get_causes(
    const dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t *causes);

/**
 * Clears the cause(s) of a key combination detection IRQ.
 *
 * @param sysrst_ctrl An sysrst_ctrl handle.
 * @param causes The causes of the IRQ (one or more
 *               `dif_sysrst_ctrl_key_combo_t`s ORed together).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_key_combo_irq_clear_causes(
    const dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t causes);

/**
 * Gets the cause(s) of an input signal change detection IRQ.
 *
 * @param sysrst_ctrl An sysrst_ctrl handle.
 * @param[out] causes The causes of the IRQ (one or more
 *             `dif_sysrst_ctrl_input_change_t`s ORed together).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_input_change_irq_get_causes(
    const dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t *causes);

/**
 * Clears the cause(s) of an input signal change detection IRQ.
 *
 * @param sysrst_ctrl An sysrst_ctrl handle.
 * @param causes The causes of the IRQ (one or more
 *               `dif_sysrst_ctrl_input_change_t`s ORed together).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_input_change_irq_clear_causes(
    const dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t causes);

/**
 * Gets the ultra-low-power wakeup status.
 *
 * @param sysrst_ctrl An sysrst_ctrl handle.
 * @param[out] wakeup_detected The ULP wakeup detection state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_ulp_wakeup_get_status(
    const dif_sysrst_ctrl_t *sysrst_ctrl, bool *wakeup_detected);

/**
 * Clears the ultra-low-power wakeup status.
 *
 * @param sysrst_ctrl An sysrst_ctrl handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_ulp_wakeup_clear_status(
    const dif_sysrst_ctrl_t *sysrst_ctrl);

/**
 * Locks System Reset Controller configurations.
 *
 * This function is reentrant: calling it while locked will have no effect and
 * return `kDifOk`.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_lock(const dif_sysrst_ctrl_t *sysrst_ctrl);

/**
 * Checks whether System Reset Controller configurations are locked.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_is_locked(const dif_sysrst_ctrl_t *sysrst_ctrl,
                                       bool *is_locked);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SYSRST_CTRL_H_
