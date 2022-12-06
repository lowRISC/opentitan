// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_sysrst_ctrl.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sysrst_ctrl_regs.h"  // Generated.

static_assert(SYSRST_CTRL_PARAM_NUM_COMBO == 4,
              "Number of key combinations has changed. Update the "
              "dif_sysrst_ctrl_key_combo_t enum.");
static_assert(SYSRST_CTRL_KEY_INTR_STATUS_FLASH_WP_L_L2H_BIT == 13,
              "Flash write-protect key interrupt bit has changed. Update the "
              "dif_sysrst_ctrl_input_change_irq_get_causes() DIF.");

dif_result_t dif_sysrst_ctrl_key_combo_detect_configure(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_key_combo_t key_combo,
    dif_sysrst_ctrl_key_combo_config_t config) {
  if (sysrst_ctrl == NULL || config.keys > kDifSysrstCtrlKeyAll ||
      config.actions > kDifSysrstCtrlKeyComboActionAll) {
    return kDifBadArg;
  }

  ptrdiff_t combo_select_ctl_reg_offset;
  ptrdiff_t combo_detect_ctl_reg_offset;
  ptrdiff_t combo_action_ctl_reg_offset;

  switch (key_combo) {
    case kDifSysrstCtrlKeyCombo0:
      combo_select_ctl_reg_offset = SYSRST_CTRL_COM_SEL_CTL_0_REG_OFFSET;
      combo_detect_ctl_reg_offset = SYSRST_CTRL_COM_DET_CTL_0_REG_OFFSET;
      combo_action_ctl_reg_offset = SYSRST_CTRL_COM_OUT_CTL_0_REG_OFFSET;
      break;
    case kDifSysrstCtrlKeyCombo1:
      combo_select_ctl_reg_offset = SYSRST_CTRL_COM_SEL_CTL_1_REG_OFFSET;
      combo_detect_ctl_reg_offset = SYSRST_CTRL_COM_DET_CTL_1_REG_OFFSET;
      combo_action_ctl_reg_offset = SYSRST_CTRL_COM_OUT_CTL_1_REG_OFFSET;
      break;
    case kDifSysrstCtrlKeyCombo2:
      combo_select_ctl_reg_offset = SYSRST_CTRL_COM_SEL_CTL_2_REG_OFFSET;
      combo_detect_ctl_reg_offset = SYSRST_CTRL_COM_DET_CTL_2_REG_OFFSET;
      combo_action_ctl_reg_offset = SYSRST_CTRL_COM_OUT_CTL_2_REG_OFFSET;
      break;
    case kDifSysrstCtrlKeyCombo3:
      combo_select_ctl_reg_offset = SYSRST_CTRL_COM_SEL_CTL_3_REG_OFFSET;
      combo_detect_ctl_reg_offset = SYSRST_CTRL_COM_DET_CTL_3_REG_OFFSET;
      combo_action_ctl_reg_offset = SYSRST_CTRL_COM_OUT_CTL_3_REG_OFFSET;
      break;
    default:
      return kDifBadArg;
  }

  if (!mmio_region_read32(sysrst_ctrl->base_addr,
                          SYSRST_CTRL_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  mmio_region_write32(sysrst_ctrl->base_addr, combo_select_ctl_reg_offset,
                      config.keys);
  mmio_region_write32(sysrst_ctrl->base_addr, combo_detect_ctl_reg_offset,
                      config.detection_time_threshold);
  mmio_region_write32(sysrst_ctrl->base_addr, combo_action_ctl_reg_offset,
                      config.actions);

  if (config.actions & kDifSysrstCtrlKeyComboActionEcReset) {
    mmio_region_write32(sysrst_ctrl->base_addr,
                        SYSRST_CTRL_EC_RST_CTL_REG_OFFSET,
                        config.embedded_controller_reset_duration);
  }

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_input_change_detect_configure(
    const dif_sysrst_ctrl_t *sysrst_ctrl,
    dif_sysrst_ctrl_input_change_config_t config) {
  if (sysrst_ctrl == NULL || config.input_changes > kDifSysrstCtrlInputAll) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(sysrst_ctrl->base_addr,
                          SYSRST_CTRL_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_KEY_INTR_CTL_REG_OFFSET,
                      config.input_changes);
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_KEY_INTR_DEBOUNCE_CTL_REG_OFFSET,
                      config.debounce_time_threshold);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_output_pin_override_configure(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t output_pin,
    dif_sysrst_ctrl_pin_config_t config) {
  if (sysrst_ctrl == NULL ||
      (config.override_value == true && config.allow_one == false) ||
      (config.override_value == false && config.allow_zero == false) ||
      !dif_is_valid_toggle(config.enabled)) {
    return kDifBadArg;
  }

  uint32_t pin_out_ctl_bit_index;
  uint32_t pin_out_value_bit_index;
  uint32_t pin_out_allow_0_bit_index;
  uint32_t pin_out_allow_1_bit_index;

  switch (output_pin) {
    case kDifSysrstCtrlPinKey0Out:
      pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_KEY0_OUT_BIT;
      pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_KEY0_OUT_BIT;
      pin_out_allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_KEY0_OUT_0_BIT;
      pin_out_allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_KEY0_OUT_1_BIT;
      break;
    case kDifSysrstCtrlPinKey1Out:
      pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_KEY1_OUT_BIT;
      pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_KEY1_OUT_BIT;
      pin_out_allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_KEY1_OUT_0_BIT;
      pin_out_allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_KEY1_OUT_1_BIT;
      break;
    case kDifSysrstCtrlPinKey2Out:
      pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_KEY2_OUT_BIT;
      pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_KEY2_OUT_BIT;
      pin_out_allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_KEY2_OUT_0_BIT;
      pin_out_allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_KEY2_OUT_1_BIT;
      break;
    case kDifSysrstCtrlPinPowerButtonOut:
      pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_PWRB_OUT_BIT;
      pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_PWRB_OUT_BIT;
      pin_out_allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_PWRB_OUT_0_BIT;
      pin_out_allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_PWRB_OUT_1_BIT;
      break;
    case kDifSysrstCtrlPinBatteryDisableOut:
      pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_BAT_DISABLE_BIT;
      pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_BAT_DISABLE_BIT;
      pin_out_allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_BAT_DISABLE_0_BIT;
      pin_out_allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_BAT_DISABLE_1_BIT;
      break;
    case kDifSysrstCtrlPinZ3WakeupOut:
      pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_Z3_WAKEUP_BIT;
      pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_Z3_WAKEUP_BIT;
      pin_out_allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_Z3_WAKEUP_0_BIT;
      pin_out_allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_Z3_WAKEUP_1_BIT;
      break;
    case kDifSysrstCtrlPinEcResetInOut:
      pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_EC_RST_L_BIT;
      pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_EC_RST_L_BIT;
      pin_out_allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_EC_RST_L_0_BIT;
      pin_out_allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_EC_RST_L_1_BIT;
      break;
    case kDifSysrstCtrlPinFlashWriteProtectInOut:
      pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_FLASH_WP_L_BIT;
      pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_FLASH_WP_L_BIT;
      pin_out_allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_FLASH_WP_L_0_BIT;
      pin_out_allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_FLASH_WP_L_1_BIT;
      break;
    default:
      return kDifBadArg;
  }

  if (!mmio_region_read32(sysrst_ctrl->base_addr,
                          SYSRST_CTRL_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  // Configure output pin control register.
  uint32_t pin_out_ctl_reg = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_PIN_OUT_CTL_REG_OFFSET);
  pin_out_ctl_reg = bitfield_bit32_write(pin_out_ctl_reg, pin_out_ctl_bit_index,
                                         dif_toggle_to_bool(config.enabled));
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_PIN_OUT_CTL_REG_OFFSET, pin_out_ctl_reg);

  // Configure output pin override value register.
  uint32_t pin_out_value_reg = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_PIN_OUT_VALUE_REG_OFFSET);
  pin_out_value_reg = bitfield_bit32_write(
      pin_out_value_reg, pin_out_value_bit_index, config.override_value);
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_PIN_OUT_VALUE_REG_OFFSET, pin_out_value_reg);

  // Configure output pin allowed values register.
  uint32_t pin_out_allowed_values_reg = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_PIN_ALLOWED_CTL_REG_OFFSET);
  pin_out_allowed_values_reg = bitfield_bit32_write(
      pin_out_allowed_values_reg, pin_out_allow_0_bit_index, config.allow_zero);
  pin_out_allowed_values_reg = bitfield_bit32_write(
      pin_out_allowed_values_reg, pin_out_allow_1_bit_index, config.allow_one);
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_PIN_ALLOWED_CTL_REG_OFFSET,
                      pin_out_allowed_values_reg);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_ulp_wakeup_configure(
    const dif_sysrst_ctrl_t *sysrst_ctrl,
    dif_sysrst_ctrl_ulp_wakeup_config_t config) {
  if (sysrst_ctrl == NULL || !dif_is_valid_toggle(config.enabled)) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(sysrst_ctrl->base_addr,
                          SYSRST_CTRL_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  mmio_region_write32(sysrst_ctrl->base_addr, SYSRST_CTRL_ULP_CTL_REG_OFFSET,
                      dif_toggle_to_bool(config.enabled));
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_ULP_AC_DEBOUNCE_CTL_REG_OFFSET,
                      config.ac_power_debounce_time_threshold);
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_ULP_LID_DEBOUNCE_CTL_REG_OFFSET,
                      config.lid_open_debounce_time_threshold);
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_ULP_PWRB_DEBOUNCE_CTL_REG_OFFSET,
                      config.power_button_debounce_time_threshold);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_ulp_wakeup_set_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_toggle_t enabled) {
  if (sysrst_ctrl == NULL || !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  mmio_region_write32(sysrst_ctrl->base_addr, SYSRST_CTRL_ULP_CTL_REG_OFFSET,
                      dif_toggle_to_bool(enabled));

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_ulp_wakeup_get_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_toggle_t *is_enabled) {
  if (sysrst_ctrl == NULL || is_enabled == NULL) {
    return kDifBadArg;
  }

  *is_enabled = dif_bool_to_toggle(mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_ULP_CTL_REG_OFFSET));

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_pins_set_inverted(
    const dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t pins, bool inverted) {
  if (sysrst_ctrl == NULL || pins > kDifSysrstCtrlPinAllNonOpenDrain) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(sysrst_ctrl->base_addr,
                          SYSRST_CTRL_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  uint32_t inverted_pins = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_KEY_INVERT_CTL_REG_OFFSET);

  if (inverted) {
    inverted_pins |= pins;
  } else {
    inverted_pins &= ~pins;
  }

  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_KEY_INVERT_CTL_REG_OFFSET, inverted_pins);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_pins_get_inverted(
    const dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t *inverted_pins) {
  if (sysrst_ctrl == NULL || inverted_pins == NULL) {
    return kDifBadArg;
  }

  *inverted_pins = mmio_region_read32(sysrst_ctrl->base_addr,
                                      SYSRST_CTRL_KEY_INVERT_CTL_REG_OFFSET);

  return kDifOk;
}

static bool get_output_pin_allowed_bit_indices(dif_sysrst_ctrl_pin_t pin,
                                               uint32_t *allow_0_bit_index,
                                               uint32_t *allow_1_bit_index) {
  switch (pin) {
    case kDifSysrstCtrlPinKey0Out:
      *allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_KEY0_OUT_0_BIT;
      *allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_KEY0_OUT_1_BIT;
      break;
    case kDifSysrstCtrlPinKey1Out:
      *allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_KEY1_OUT_0_BIT;
      *allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_KEY1_OUT_1_BIT;
      break;
    case kDifSysrstCtrlPinKey2Out:
      *allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_KEY2_OUT_0_BIT;
      *allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_KEY2_OUT_1_BIT;
      break;
    case kDifSysrstCtrlPinPowerButtonOut:
      *allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_PWRB_OUT_0_BIT;
      *allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_PWRB_OUT_1_BIT;
      break;
    case kDifSysrstCtrlPinBatteryDisableOut:
      *allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_BAT_DISABLE_0_BIT;
      *allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_BAT_DISABLE_1_BIT;
      break;
    case kDifSysrstCtrlPinZ3WakeupOut:
      *allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_Z3_WAKEUP_0_BIT;
      *allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_Z3_WAKEUP_1_BIT;
      break;
    case kDifSysrstCtrlPinEcResetInOut:
      *allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_EC_RST_L_0_BIT;
      *allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_EC_RST_L_1_BIT;
      break;
    case kDifSysrstCtrlPinFlashWriteProtectInOut:
      *allow_0_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_FLASH_WP_L_0_BIT;
      *allow_1_bit_index = SYSRST_CTRL_PIN_ALLOWED_CTL_FLASH_WP_L_1_BIT;
      break;
    default:
      return false;
  }
  return true;
}

dif_result_t dif_sysrst_ctrl_output_pin_override_set_allowed(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    bool allow_zero, bool allow_one) {
  if (sysrst_ctrl == NULL) {
    return kDifBadArg;
  }

  uint32_t allow_0_bit_index;
  uint32_t allow_1_bit_index;
  if (!get_output_pin_allowed_bit_indices(pin, &allow_0_bit_index,
                                          &allow_1_bit_index)) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(sysrst_ctrl->base_addr,
                          SYSRST_CTRL_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  uint32_t allowed_values_reg = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_PIN_ALLOWED_CTL_REG_OFFSET);
  allowed_values_reg =
      bitfield_bit32_write(allowed_values_reg, allow_0_bit_index, allow_zero);
  allowed_values_reg =
      bitfield_bit32_write(allowed_values_reg, allow_1_bit_index, allow_one);
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_PIN_ALLOWED_CTL_REG_OFFSET,
                      allowed_values_reg);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_output_pin_override_get_allowed(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    bool *allow_zero, bool *allow_one) {
  if (sysrst_ctrl == NULL || allow_zero == NULL || allow_one == NULL) {
    return kDifBadArg;
  }

  uint32_t allow_0_bit_index;
  uint32_t allow_1_bit_index;
  if (!get_output_pin_allowed_bit_indices(pin, &allow_0_bit_index,
                                          &allow_1_bit_index)) {
    return kDifBadArg;
  }

  uint32_t allowed_values_reg = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_PIN_ALLOWED_CTL_REG_OFFSET);
  *allow_zero = bitfield_bit32_read(allowed_values_reg, allow_0_bit_index);
  *allow_one = bitfield_bit32_read(allowed_values_reg, allow_1_bit_index);

  return kDifOk;
}

static bool get_output_pin_ctl_bit_index(dif_sysrst_ctrl_pin_t pin,
                                         uint32_t *pin_out_ctl_bit_index) {
  switch (pin) {
    case kDifSysrstCtrlPinKey0Out:
      *pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_KEY0_OUT_BIT;
      break;
    case kDifSysrstCtrlPinKey1Out:
      *pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_KEY1_OUT_BIT;
      break;
    case kDifSysrstCtrlPinKey2Out:
      *pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_KEY2_OUT_BIT;
      break;
    case kDifSysrstCtrlPinPowerButtonOut:
      *pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_PWRB_OUT_BIT;
      break;
    case kDifSysrstCtrlPinBatteryDisableOut:
      *pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_BAT_DISABLE_BIT;
      break;
    case kDifSysrstCtrlPinZ3WakeupOut:
      *pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_Z3_WAKEUP_BIT;
      break;
    case kDifSysrstCtrlPinEcResetInOut:
      *pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_EC_RST_L_BIT;
      break;
    case kDifSysrstCtrlPinFlashWriteProtectInOut:
      *pin_out_ctl_bit_index = SYSRST_CTRL_PIN_OUT_CTL_FLASH_WP_L_BIT;
      break;
    default:
      return false;
  }
  return true;
}

dif_result_t dif_sysrst_ctrl_output_pin_override_set_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    dif_toggle_t enabled) {
  if (sysrst_ctrl == NULL || !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  uint32_t pin_out_ctl_bit_index;
  if (!get_output_pin_ctl_bit_index(pin, &pin_out_ctl_bit_index)) {
    return kDifBadArg;
  }

  uint32_t pin_out_ctl_reg = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_PIN_OUT_CTL_REG_OFFSET);
  pin_out_ctl_reg = bitfield_bit32_write(pin_out_ctl_reg, pin_out_ctl_bit_index,
                                         dif_toggle_to_bool(enabled));
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_PIN_OUT_CTL_REG_OFFSET, pin_out_ctl_reg);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_output_pin_override_get_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    dif_toggle_t *is_enabled) {
  if (sysrst_ctrl == NULL || is_enabled == NULL) {
    return kDifBadArg;
  }

  uint32_t pin_out_ctl_bit_index;
  if (!get_output_pin_ctl_bit_index(pin, &pin_out_ctl_bit_index)) {
    return kDifBadArg;
  }

  uint32_t pin_out_ctl_reg = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_PIN_OUT_CTL_REG_OFFSET);
  *is_enabled = bitfield_bit32_read(pin_out_ctl_reg, pin_out_ctl_bit_index);

  return kDifOk;
}

static bool get_output_pin_value_bit_index(dif_sysrst_ctrl_pin_t pin,
                                           uint32_t *pin_out_value_bit_index) {
  switch (pin) {
    case kDifSysrstCtrlPinKey0Out:
      *pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_KEY0_OUT_BIT;
      break;
    case kDifSysrstCtrlPinKey1Out:
      *pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_KEY1_OUT_BIT;
      break;
    case kDifSysrstCtrlPinKey2Out:
      *pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_KEY2_OUT_BIT;
      break;
    case kDifSysrstCtrlPinPowerButtonOut:
      *pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_PWRB_OUT_BIT;
      break;
    case kDifSysrstCtrlPinBatteryDisableOut:
      *pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_BAT_DISABLE_BIT;
      break;
    case kDifSysrstCtrlPinZ3WakeupOut:
      *pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_Z3_WAKEUP_BIT;
      break;
    case kDifSysrstCtrlPinEcResetInOut:
      *pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_EC_RST_L_BIT;
      break;
    case kDifSysrstCtrlPinFlashWriteProtectInOut:
      *pin_out_value_bit_index = SYSRST_CTRL_PIN_OUT_VALUE_FLASH_WP_L_BIT;
      break;
    default:
      return false;
  }
  return true;
}

dif_result_t dif_sysrst_ctrl_output_pin_set_override(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    bool value) {
  if (sysrst_ctrl == NULL) {
    return kDifBadArg;
  }

  uint32_t pin_out_value_bit_index;
  if (!get_output_pin_value_bit_index(pin, &pin_out_value_bit_index)) {
    return kDifBadArg;
  }

  uint32_t pin_out_value_reg = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_PIN_OUT_VALUE_REG_OFFSET);
  pin_out_value_reg =
      bitfield_bit32_write(pin_out_value_reg, pin_out_value_bit_index, value);
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_PIN_OUT_VALUE_REG_OFFSET, pin_out_value_reg);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_output_pin_get_override(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    bool *value) {
  if (sysrst_ctrl == NULL || value == NULL) {
    return kDifBadArg;
  }

  uint32_t pin_out_value_bit_index;
  if (!get_output_pin_value_bit_index(pin, &pin_out_value_bit_index)) {
    return kDifBadArg;
  }

  uint32_t pin_out_value_reg = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_PIN_OUT_VALUE_REG_OFFSET);
  *value = bitfield_bit32_read(pin_out_value_reg, pin_out_value_bit_index);

  return kDifOk;
}

static bool get_input_pin_value_bit_index(dif_sysrst_ctrl_pin_t pin,
                                          uint32_t *pin_in_value_bit_index) {
  switch (pin) {
    case kDifSysrstCtrlPinKey0In:
      *pin_in_value_bit_index = SYSRST_CTRL_PIN_IN_VALUE_KEY0_IN_BIT;
      break;
    case kDifSysrstCtrlPinKey1In:
      *pin_in_value_bit_index = SYSRST_CTRL_PIN_IN_VALUE_KEY1_IN_BIT;
      break;
    case kDifSysrstCtrlPinKey2In:
      *pin_in_value_bit_index = SYSRST_CTRL_PIN_IN_VALUE_KEY2_IN_BIT;
      break;
    case kDifSysrstCtrlPinPowerButtonIn:
      *pin_in_value_bit_index = SYSRST_CTRL_PIN_IN_VALUE_PWRB_IN_BIT;
      break;
    case kDifSysrstCtrlPinAcPowerPresentIn:
      *pin_in_value_bit_index = SYSRST_CTRL_PIN_IN_VALUE_AC_PRESENT_BIT;
      break;
    case kDifSysrstCtrlPinLidOpenIn:
      *pin_in_value_bit_index = SYSRST_CTRL_PIN_IN_VALUE_LID_OPEN_BIT;
      break;
    case kDifSysrstCtrlPinEcResetInOut:
      *pin_in_value_bit_index = SYSRST_CTRL_PIN_IN_VALUE_EC_RST_L_BIT;
      break;
    case kDifSysrstCtrlPinFlashWriteProtectInOut:
      *pin_in_value_bit_index = SYSRST_CTRL_PIN_IN_VALUE_FLASH_WP_L_BIT;
      break;
    default:
      return false;
  }
  return true;
}

dif_result_t dif_sysrst_ctrl_input_pin_read(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_pin_t pin,
    bool *value) {
  if (sysrst_ctrl == NULL || value == NULL) {
    return kDifBadArg;
  }

  uint32_t pin_in_value_bit_index;
  if (!get_input_pin_value_bit_index(pin, &pin_in_value_bit_index)) {
    return kDifBadArg;
  }

  uint32_t pin_in_value_reg = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_PIN_IN_VALUE_REG_OFFSET);
  *value = bitfield_bit32_read(pin_in_value_reg, pin_in_value_bit_index);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_auto_override_configure(
    const dif_sysrst_ctrl_t *sysrst_ctrl,
    dif_sysrst_ctrl_auto_override_config_t config, dif_toggle_t enabled) {
  if (sysrst_ctrl == NULL || !dif_is_valid_toggle(config.override_key_0) ||
      !dif_is_valid_toggle(config.override_key_1) ||
      !dif_is_valid_toggle(config.override_key_2) ||
      !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(sysrst_ctrl->base_addr,
                          SYSRST_CTRL_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  // Configure Auto Block Debounce Control register.
  uint32_t auto_block_ctl_reg = bitfield_bit32_write(
      0, SYSRST_CTRL_AUTO_BLOCK_DEBOUNCE_CTL_AUTO_BLOCK_ENABLE_BIT,
      dif_toggle_to_bool(enabled));
  auto_block_ctl_reg = bitfield_field32_write(
      auto_block_ctl_reg,
      SYSRST_CTRL_AUTO_BLOCK_DEBOUNCE_CTL_DEBOUNCE_TIMER_FIELD,
      config.debounce_time_threshold);
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_AUTO_BLOCK_DEBOUNCE_CTL_REG_OFFSET,
                      auto_block_ctl_reg);

  // Configure Auto Block Output Control register.
  auto_block_ctl_reg =
      bitfield_bit32_write(0, SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_KEY0_OUT_SEL_BIT,
                           dif_toggle_to_bool(config.override_key_0));
  auto_block_ctl_reg = bitfield_bit32_write(
      auto_block_ctl_reg, SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_KEY0_OUT_VALUE_BIT,
      dif_toggle_to_bool(config.key_0_override_value));
  auto_block_ctl_reg = bitfield_bit32_write(
      auto_block_ctl_reg, SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_KEY1_OUT_SEL_BIT,
      dif_toggle_to_bool(config.override_key_1));
  auto_block_ctl_reg = bitfield_bit32_write(
      auto_block_ctl_reg, SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_KEY1_OUT_VALUE_BIT,
      dif_toggle_to_bool(config.key_1_override_value));
  auto_block_ctl_reg = bitfield_bit32_write(
      auto_block_ctl_reg, SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_KEY2_OUT_SEL_BIT,
      dif_toggle_to_bool(config.override_key_2));
  auto_block_ctl_reg = bitfield_bit32_write(
      auto_block_ctl_reg, SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_KEY2_OUT_VALUE_BIT,
      dif_toggle_to_bool(config.key_2_override_value));
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_REG_OFFSET,
                      auto_block_ctl_reg);

  return kDifOk;
}

static bool get_key_auto_override_en_bit_index(dif_sysrst_ctrl_key_t key,
                                               uint32_t *en_bit_index) {
  switch (key) {
    case kDifSysrstCtrlKey0:
      *en_bit_index = SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_KEY0_OUT_SEL_BIT;
      break;
    case kDifSysrstCtrlKey1:
      *en_bit_index = SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_KEY1_OUT_SEL_BIT;
      break;
    case kDifSysrstCtrlKey2:
      *en_bit_index = SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_KEY2_OUT_SEL_BIT;
      break;
    default:
      return false;
  }
  return true;
}

dif_result_t dif_sysrst_ctrl_auto_override_set_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_key_t key,
    dif_toggle_t enabled) {
  if (sysrst_ctrl == NULL || !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  uint32_t en_bit_index;
  if (!get_key_auto_override_en_bit_index(key, &en_bit_index)) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(sysrst_ctrl->base_addr,
                          SYSRST_CTRL_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  uint32_t auto_block_ctl_reg = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_REG_OFFSET);
  auto_block_ctl_reg = bitfield_bit32_write(auto_block_ctl_reg, en_bit_index,
                                            dif_toggle_to_bool(enabled));
  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_REG_OFFSET,
                      auto_block_ctl_reg);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_auto_override_get_enabled(
    const dif_sysrst_ctrl_t *sysrst_ctrl, dif_sysrst_ctrl_key_t key,
    dif_toggle_t *is_enabled) {
  if (sysrst_ctrl == NULL || is_enabled == NULL) {
    return kDifBadArg;
  }

  uint32_t en_bit_index;
  if (!get_key_auto_override_en_bit_index(key, &en_bit_index)) {
    return kDifBadArg;
  }

  uint32_t auto_block_ctl_reg = mmio_region_read32(
      sysrst_ctrl->base_addr, SYSRST_CTRL_AUTO_BLOCK_OUT_CTL_REG_OFFSET);
  *is_enabled =
      dif_bool_to_toggle(bitfield_bit32_read(auto_block_ctl_reg, en_bit_index));

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_key_combo_irq_get_causes(
    const dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t *causes) {
  if (sysrst_ctrl == NULL || causes == NULL) {
    return kDifBadArg;
  }

  *causes = mmio_region_read32(sysrst_ctrl->base_addr,
                               SYSRST_CTRL_COMBO_INTR_STATUS_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_key_combo_irq_clear_causes(
    const dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t causes) {
  if (sysrst_ctrl == NULL || causes >= (1U << SYSRST_CTRL_PARAM_NUM_COMBO)) {
    return kDifBadArg;
  }

  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_COMBO_INTR_STATUS_REG_OFFSET, causes);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_input_change_irq_get_causes(
    const dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t *causes) {
  if (sysrst_ctrl == NULL || causes == NULL) {
    return kDifBadArg;
  }

  *causes = mmio_region_read32(sysrst_ctrl->base_addr,
                               SYSRST_CTRL_KEY_INTR_STATUS_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_input_change_irq_clear_causes(
    const dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t causes) {
  if (sysrst_ctrl == NULL ||
      causes >= (1U << (SYSRST_CTRL_KEY_INTR_STATUS_FLASH_WP_L_L2H_BIT + 1))) {
    return kDifBadArg;
  }

  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_KEY_INTR_STATUS_REG_OFFSET, causes);
  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_ulp_wakeup_get_status(
    const dif_sysrst_ctrl_t *sysrst_ctrl, bool *wakeup_detected) {
  if (sysrst_ctrl == NULL || wakeup_detected == NULL) {
    return kDifBadArg;
  }

  *wakeup_detected = mmio_region_read32(sysrst_ctrl->base_addr,
                                        SYSRST_CTRL_WKUP_STATUS_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_ulp_wakeup_clear_status(
    const dif_sysrst_ctrl_t *sysrst_ctrl) {
  if (sysrst_ctrl == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(sysrst_ctrl->base_addr,
                      SYSRST_CTRL_WKUP_STATUS_REG_OFFSET, 1);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_lock(const dif_sysrst_ctrl_t *sysrst_ctrl) {
  if (sysrst_ctrl == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(sysrst_ctrl->base_addr, SYSRST_CTRL_REGWEN_REG_OFFSET, 0);

  return kDifOk;
}

dif_result_t dif_sysrst_ctrl_is_locked(const dif_sysrst_ctrl_t *sysrst_ctrl,
                                       bool *is_locked) {
  if (sysrst_ctrl == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  *is_locked = !mmio_region_read32(sysrst_ctrl->base_addr,
                                   SYSRST_CTRL_REGWEN_REG_OFFSET);

  return kDifOk;
}
