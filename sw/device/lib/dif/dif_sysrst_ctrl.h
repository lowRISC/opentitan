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
} dif_sysrst_ctrl_key_combo_action_t;

/**
 * Runtime configuration for the System Reset Controller key combination
 * detection feature.
 */
typedef struct dif_sysrst_ctrl_key_combo_config {
  /**
   * A key combination to configure.
   */
  dif_sysrst_ctrl_key_combo_t key_combo;
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
  uint32_t embedded_controller_reset_duration;
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
  kDifSysrstCtrlInputPowerButtonL2H = 1U << 8,
  /**
   * Key 0 input signal low-to-high.
   */
  kDifSysrstCtrlInputKey0L2H = 1U << 9,
  /**
   * Key 1 input signal low-to-high.
   */
  kDifSysrstCtrlInputKey1L2H = 1U << 10,
  /**
   * Key 2 input signal low-to-high.
   */
  kDifSysrstCtrlInputKey2L2H = 1U << 11,
  /**
   * AC power present input signal low-to-high.
   */
  kDifSysrstCtrlInputAcPowerPresetL2H = 1U << 12,
  /**
   * Embedded controller reset input signal low-to-high.
   */
  kDifSysrstCtrlInputEcResetL2H = 1U << 13,
  /**
   * Flash write protect input signal low-to-high.
   */
  kDifSysrstCtrlInputFlashWriteProtectL2H = 1U << 14,
} dif_sysrst_ctrl_input_change_t;

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
 * Configures a System Reset Controller's key combination detection feature.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_key_combo_detect_configure(
    const dif_sysrst_ctrl_t *sysrst_ctrl,
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
 * Sets the enablement of a System Reset Controller's key signal auto-override
 * feature.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param enabled Whether to enable the feature or not.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_auto_override_set_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_toggle_t enabled);

/**
 * Gets the enablement of a System Reset Controller's key signal auto-override
 * feature.
 *
 * @param sysrst_ctrl A System Reset Controller handle.
 * @param[out] is_enabled Whether the feature is enabled or not.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sysrst_ctrl_auto_override_get_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_toggle_t *is_enabled);

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
