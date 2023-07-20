// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pinmux.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/runtime/hart.h"

#include "pinmux_regs.h"  // Generated.

static bool dif_pinmux_get_reg_offset(dif_pinmux_index_t index,
                                      dif_pinmux_pad_kind_t kind,
                                      ptrdiff_t mio_reg_base,
                                      ptrdiff_t dio_reg_base,
                                      ptrdiff_t *reg_offset) {
  uint32_t num_pads;
  ptrdiff_t reg_base;

  switch (kind) {
    case kDifPinmuxPadKindMio:
      num_pads = PINMUX_PARAM_N_MIO_PADS;
      reg_base = mio_reg_base;
      break;
    case kDifPinmuxPadKindDio:
      num_pads = PINMUX_PARAM_N_DIO_PADS;
      reg_base = dio_reg_base;
      break;
    default:
      return false;
  }
  if (index >= num_pads) {
    return false;
  }
  *reg_offset = reg_base + (ptrdiff_t)(index * sizeof(uint32_t));
  return true;
}

static bool dif_pinmux_get_sleep_status_bit(dif_pinmux_pad_kind_t kind,
                                            dif_pinmux_index_t index,
                                            ptrdiff_t *reg_offset,
                                            bitfield_bit32_index_t *bit) {
  uint32_t num_pads;
  ptrdiff_t reg_base;

  switch (kind) {
    case kDifPinmuxPadKindMio:
      num_pads = PINMUX_PARAM_N_MIO_PADS;
      reg_base = PINMUX_MIO_PAD_SLEEP_STATUS_0_REG_OFFSET;
      break;
    case kDifPinmuxPadKindDio:
      num_pads = PINMUX_PARAM_N_DIO_PADS;
      reg_base = PINMUX_DIO_PAD_SLEEP_STATUS_REG_OFFSET;
      break;
    default:
      return false;
  }
  if (index >= num_pads) {
    return false;
  }
  *reg_offset = (ptrdiff_t)index / 32 + reg_base;
  *bit = index % 32;
  return true;
}

static bool dif_pinmux_get_lock_reg_offset(dif_pinmux_index_t index,
                                           dif_pinmux_lock_target_t target,
                                           ptrdiff_t *reg_offset) {
  ptrdiff_t reg_base;
  size_t reg_count;
  switch (target) {
    case kDifPinmuxLockTargetInsel:
      reg_base = PINMUX_MIO_PERIPH_INSEL_REGWEN_0_REG_OFFSET;
      reg_count = PINMUX_MIO_PERIPH_INSEL_REGWEN_MULTIREG_COUNT;
      break;
    case kDifPinmuxLockTargetOutsel:
      reg_base = PINMUX_MIO_OUTSEL_REGWEN_0_REG_OFFSET;
      reg_count = PINMUX_MIO_OUTSEL_REGWEN_MULTIREG_COUNT;
      break;
    case kDifPinmuxLockTargetMioSleep:
      reg_base = PINMUX_MIO_PAD_SLEEP_REGWEN_0_REG_OFFSET;
      reg_count = PINMUX_MIO_PAD_SLEEP_REGWEN_MULTIREG_COUNT;
      break;
    case kDifPinmuxLockTargetDioSleep:
      reg_base = PINMUX_DIO_PAD_SLEEP_REGWEN_0_REG_OFFSET;
      reg_count = PINMUX_DIO_PAD_SLEEP_REGWEN_MULTIREG_COUNT;
      break;
    case kDifPinmuxLockTargetMioPadAttr:
      reg_base = PINMUX_MIO_PAD_ATTR_REGWEN_0_REG_OFFSET;
      reg_count = PINMUX_MIO_PAD_ATTR_REGWEN_MULTIREG_COUNT;
      break;
    case kDifPinmuxLockTargetDioPadAttr:
      reg_base = PINMUX_DIO_PAD_ATTR_REGWEN_0_REG_OFFSET;
      reg_count = PINMUX_DIO_PAD_ATTR_REGWEN_MULTIREG_COUNT;
      break;
    case kDifPinmuxLockTargetWakeupDetector:
      reg_base = PINMUX_WKUP_DETECTOR_REGWEN_0_REG_OFFSET;
      reg_count = PINMUX_WKUP_DETECTOR_REGWEN_MULTIREG_COUNT;
      break;
    default:
      return false;
  }

  if (index >= reg_count) {
    return false;
  }

  *reg_offset = reg_base + (ptrdiff_t)index * (ptrdiff_t)sizeof(uint32_t);
  return true;
}

dif_result_t dif_pinmux_lock(const dif_pinmux_t *pinmux,
                             dif_pinmux_index_t index,
                             dif_pinmux_lock_target_t target) {
  if (pinmux == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t reg_offset;
  if (!dif_pinmux_get_lock_reg_offset(index, target, &reg_offset)) {
    return kDifBadArg;
  }
  mmio_region_write32(pinmux->base_addr, reg_offset, /*value=*/0);
  return kDifOk;
}

dif_result_t dif_pinmux_is_locked(const dif_pinmux_t *pinmux,
                                  dif_pinmux_index_t index,
                                  dif_pinmux_lock_target_t target,
                                  bool *is_locked) {
  if (pinmux == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t reg_offset;
  if (!dif_pinmux_get_lock_reg_offset(index, target, &reg_offset)) {
    return kDifBadArg;
  }

  uint32_t reg_value = mmio_region_read32(pinmux->base_addr, reg_offset);
  *is_locked = !bitfield_bit32_read(reg_value,
                                    PINMUX_MIO_PERIPH_INSEL_REGWEN_0_EN_0_BIT);
  return kDifOk;
}

dif_result_t dif_pinmux_input_select(const dif_pinmux_t *pinmux,
                                     dif_pinmux_index_t peripheral_input,
                                     dif_pinmux_index_t insel) {
  if (pinmux == NULL || peripheral_input >= PINMUX_PARAM_N_MIO_PERIPH_IN ||
      insel >= (2 + PINMUX_PARAM_N_MIO_PADS)) {
    return kDifBadArg;
  }
  bool is_locked;
  dif_result_t result = dif_pinmux_is_locked(
      pinmux, peripheral_input, kDifPinmuxLockTargetInsel, &is_locked);
  if (result != kDifOk) {
    return result;
  }
  if (is_locked) {
    return kDifLocked;
  }
  ptrdiff_t reg_offset =
      PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET + (ptrdiff_t)(peripheral_input << 2);
  uint32_t reg_value =
      bitfield_field32_write(0, PINMUX_MIO_PERIPH_INSEL_0_IN_0_FIELD, insel);
  mmio_region_write32(pinmux->base_addr, reg_offset, reg_value);
  return kDifOk;
}

dif_result_t dif_pinmux_output_select(const dif_pinmux_t *pinmux,
                                      dif_pinmux_index_t mio_pad_output,
                                      dif_pinmux_index_t outsel) {
  if (pinmux == NULL || mio_pad_output >= PINMUX_PARAM_N_MIO_PADS ||
      outsel >= (3 + PINMUX_PARAM_N_MIO_PERIPH_OUT)) {
    return kDifBadArg;
  }
  bool is_locked;
  dif_result_t result = dif_pinmux_is_locked(
      pinmux, mio_pad_output, kDifPinmuxLockTargetOutsel, &is_locked);
  if (result != kDifOk) {
    return result;
  }
  if (is_locked) {
    return kDifLocked;
  }
  ptrdiff_t reg_offset =
      PINMUX_MIO_OUTSEL_0_REG_OFFSET + (ptrdiff_t)(mio_pad_output << 2);
  uint32_t reg_value =
      bitfield_field32_write(0, PINMUX_MIO_OUTSEL_0_OUT_0_FIELD, outsel);
  mmio_region_write32(pinmux->base_addr, reg_offset, reg_value);
  return kDifOk;
}

static dif_pinmux_pad_attr_t dif_pinmux_reg_to_pad_attr(uint32_t reg_value) {
  dif_pinmux_pad_attr_t pad_attrs = {0};
  pad_attrs.slew_rate = (dif_pinmux_pad_slew_rate_t)bitfield_field32_read(
      reg_value, PINMUX_MIO_PAD_ATTR_0_SLEW_RATE_0_FIELD);
  pad_attrs.drive_strength =
      (dif_pinmux_pad_drive_strength_t)bitfield_field32_read(
          reg_value, PINMUX_MIO_PAD_ATTR_0_DRIVE_STRENGTH_0_FIELD);
  if (bitfield_bit32_read(reg_value, PINMUX_MIO_PAD_ATTR_0_INVERT_0_BIT)) {
    pad_attrs.flags |= kDifPinmuxPadAttrInvertLevel;
  }
  if (bitfield_bit32_read(reg_value,
                          PINMUX_MIO_PAD_ATTR_0_VIRTUAL_OD_EN_0_BIT)) {
    pad_attrs.flags |= kDifPinmuxPadAttrVirtualOpenDrain;
  }
  if (bitfield_bit32_read(reg_value, PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT)) {
    pad_attrs.flags |= kDifPinmuxPadAttrPullResistorEnable;
  }
  if (bitfield_bit32_read(reg_value, PINMUX_MIO_PAD_ATTR_0_PULL_SELECT_0_BIT)) {
    pad_attrs.flags |= kDifPinmuxPadAttrPullResistorUp;
  }
  if (bitfield_bit32_read(reg_value, PINMUX_MIO_PAD_ATTR_0_KEEPER_EN_0_BIT)) {
    pad_attrs.flags |= kDifPinmuxPadAttrKeeper;
  }
  if (bitfield_bit32_read(reg_value, PINMUX_MIO_PAD_ATTR_0_SCHMITT_EN_0_BIT)) {
    pad_attrs.flags |= kDifPinmuxPadAttrSchmittTrigger;
  }
  if (bitfield_bit32_read(reg_value, PINMUX_MIO_PAD_ATTR_0_OD_EN_0_BIT)) {
    pad_attrs.flags |= kDifPinmuxPadAttrOpenDrain;
  }
  return pad_attrs;
}

enum { kDifPinmuxPadAttrSpinWaitMicros = 5 };

dif_result_t dif_pinmux_pad_write_attrs(const dif_pinmux_t *pinmux,
                                        dif_pinmux_index_t pad,
                                        dif_pinmux_pad_kind_t type,
                                        dif_pinmux_pad_attr_t attrs_in,
                                        dif_pinmux_pad_attr_t *attrs_out) {
  if (pinmux == NULL || attrs_out == NULL) {
    return kDifBadArg;
  }
  if (attrs_in.drive_strength > PINMUX_MIO_PAD_ATTR_0_DRIVE_STRENGTH_0_MASK ||
      attrs_in.slew_rate > PINMUX_MIO_PAD_ATTR_0_SLEW_RATE_0_MASK) {
    return kDifBadArg;
  }
  ptrdiff_t reg_offset;
  if (!dif_pinmux_get_reg_offset(pad, type, PINMUX_MIO_PAD_ATTR_0_REG_OFFSET,
                                 PINMUX_DIO_PAD_ATTR_0_REG_OFFSET,
                                 &reg_offset)) {
    return kDifBadArg;
  }
  const dif_pinmux_lock_target_t lock_target =
      (type == kDifPinmuxPadKindMio) ? kDifPinmuxLockTargetMioPadAttr
                                     : kDifPinmuxLockTargetDioPadAttr;
  bool is_locked;
  dif_result_t result =
      dif_pinmux_is_locked(pinmux, pad, lock_target, &is_locked);
  if (result != kDifOk) {
    return result;
  }
  if (is_locked) {
    return kDifLocked;
  }

  uint32_t reg_before = mmio_region_read32(pinmux->base_addr, reg_offset);

  uint32_t reg_value = bitfield_field32_write(
      0, PINMUX_MIO_PAD_ATTR_0_SLEW_RATE_0_FIELD, attrs_in.slew_rate);
  reg_value = bitfield_field32_write(
      reg_value, PINMUX_MIO_PAD_ATTR_0_DRIVE_STRENGTH_0_FIELD,
      attrs_in.drive_strength);
  reg_value =
      bitfield_bit32_write(reg_value, PINMUX_MIO_PAD_ATTR_0_INVERT_0_BIT,
                           attrs_in.flags & kDifPinmuxPadAttrInvertLevel);
  reg_value =
      bitfield_bit32_write(reg_value, PINMUX_MIO_PAD_ATTR_0_VIRTUAL_OD_EN_0_BIT,
                           attrs_in.flags & kDifPinmuxPadAttrVirtualOpenDrain);
  reg_value = bitfield_bit32_write(
      reg_value, PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT,
      attrs_in.flags & kDifPinmuxPadAttrPullResistorEnable);
  reg_value =
      bitfield_bit32_write(reg_value, PINMUX_MIO_PAD_ATTR_0_PULL_SELECT_0_BIT,
                           attrs_in.flags & kDifPinmuxPadAttrPullResistorUp);
  reg_value =
      bitfield_bit32_write(reg_value, PINMUX_MIO_PAD_ATTR_0_KEEPER_EN_0_BIT,
                           attrs_in.flags & kDifPinmuxPadAttrKeeper);
  reg_value =
      bitfield_bit32_write(reg_value, PINMUX_MIO_PAD_ATTR_0_SCHMITT_EN_0_BIT,
                           attrs_in.flags & kDifPinmuxPadAttrSchmittTrigger);
  reg_value = bitfield_bit32_write(reg_value, PINMUX_MIO_PAD_ATTR_0_OD_EN_0_BIT,
                                   attrs_in.flags & kDifPinmuxPadAttrOpenDrain);
  mmio_region_write32(pinmux->base_addr, reg_offset, reg_value);

  // Wait for pull enable/disable changes to propagate to the physical pad.
  dif_pinmux_pad_attr_t attrs_before = dif_pinmux_reg_to_pad_attr(reg_before);
  if ((attrs_before.flags & kDifPinmuxPadAttrPullResistorEnable) !=
      (attrs_in.flags & kDifPinmuxPadAttrPullResistorEnable)) {
    busy_spin_micros(kDifPinmuxPadAttrSpinWaitMicros);
  }

  uint32_t read_value = mmio_region_read32(pinmux->base_addr, reg_offset);
  *attrs_out = dif_pinmux_reg_to_pad_attr(read_value);

  if (reg_value != read_value) {
    return kDifError;
  }
  return kDifOk;
}

dif_result_t dif_pinmux_pad_get_attrs(const dif_pinmux_t *pinmux,
                                      dif_pinmux_index_t pad,
                                      dif_pinmux_pad_kind_t type,
                                      dif_pinmux_pad_attr_t *attrs) {
  if (pinmux == NULL || attrs == NULL) {
    return kDifBadArg;
  }
  ptrdiff_t reg_offset;
  if (!dif_pinmux_get_reg_offset(pad, type, PINMUX_MIO_PAD_ATTR_0_REG_OFFSET,
                                 PINMUX_DIO_PAD_ATTR_0_REG_OFFSET,
                                 &reg_offset)) {
    return kDifBadArg;
  }
  uint32_t reg_value = mmio_region_read32(pinmux->base_addr, reg_offset);
  *attrs = dif_pinmux_reg_to_pad_attr(reg_value);
  return kDifOk;
}

dif_result_t dif_pinmux_pad_sleep_enable(const dif_pinmux_t *pinmux,
                                         dif_pinmux_index_t pad,
                                         dif_pinmux_pad_kind_t type,
                                         dif_pinmux_sleep_mode_t mode) {
  if (pinmux == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t en_reg_offset, mode_reg_offset;
  if (!dif_pinmux_get_reg_offset(
          pad, type, PINMUX_MIO_PAD_SLEEP_EN_0_REG_OFFSET,
          PINMUX_DIO_PAD_SLEEP_EN_0_REG_OFFSET, &en_reg_offset)) {
    return kDifBadArg;
  }
  if (!dif_pinmux_get_reg_offset(
          pad, type, PINMUX_MIO_PAD_SLEEP_MODE_0_REG_OFFSET,
          PINMUX_DIO_PAD_SLEEP_MODE_0_REG_OFFSET, &mode_reg_offset)) {
    return kDifBadArg;
  }
  const dif_pinmux_lock_target_t lock_target =
      (type == kDifPinmuxPadKindMio) ? kDifPinmuxLockTargetMioSleep
                                     : kDifPinmuxLockTargetDioSleep;
  bool is_locked;
  dif_result_t result =
      dif_pinmux_is_locked(pinmux, pad, lock_target, &is_locked);
  if (result != kDifOk) {
    return result;
  }
  if (is_locked) {
    return kDifLocked;
  }

  // Sleep Mode Value
  uint32_t reg_value;
  switch (mode) {
    case kDifPinmuxSleepModeLow:
      reg_value = PINMUX_MIO_PAD_SLEEP_MODE_0_OUT_0_VALUE_TIE_LOW;
      break;
    case kDifPinmuxSleepModeHigh:
      reg_value = PINMUX_MIO_PAD_SLEEP_MODE_0_OUT_0_VALUE_TIE_HIGH;
      break;
    case kDifPinmuxSleepModeHighZ:
      reg_value = PINMUX_MIO_PAD_SLEEP_MODE_0_OUT_0_VALUE_HIGH_Z;
      break;
    case kDifPinmuxSleepModeKeep:
      reg_value = PINMUX_MIO_PAD_SLEEP_MODE_0_OUT_0_VALUE_KEEP;
      break;
    default:
      return kDifBadArg;
  }
  mmio_region_write32(pinmux->base_addr, mode_reg_offset, reg_value);

  // Sleep Mode Enable
  reg_value = bitfield_bit32_write(0, PINMUX_MIO_PAD_SLEEP_EN_0_EN_0_BIT, 1);
  mmio_region_write32(pinmux->base_addr, en_reg_offset, reg_value);
  return kDifOk;
}

dif_result_t dif_pinmux_pad_sleep_disable(const dif_pinmux_t *pinmux,
                                          dif_pinmux_index_t pad,
                                          dif_pinmux_pad_kind_t type) {
  if (pinmux == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t en_reg_offset;
  if (!dif_pinmux_get_reg_offset(
          pad, type, PINMUX_MIO_PAD_SLEEP_EN_0_REG_OFFSET,
          PINMUX_DIO_PAD_SLEEP_EN_0_REG_OFFSET, &en_reg_offset)) {
    return kDifBadArg;
  }

  const dif_pinmux_lock_target_t lock_target =
      (type == kDifPinmuxPadKindMio) ? kDifPinmuxLockTargetMioSleep
                                     : kDifPinmuxLockTargetDioSleep;
  bool is_locked;
  dif_result_t result =
      dif_pinmux_is_locked(pinmux, pad, lock_target, &is_locked);
  if (result != kDifOk) {
    return result;
  }
  if (is_locked) {
    return kDifLocked;
  }

  mmio_region_write32(pinmux->base_addr, en_reg_offset, 0);
  return kDifOk;
}

dif_result_t dif_pinmux_pad_sleep_get_state(const dif_pinmux_t *pinmux,
                                            dif_pinmux_index_t pad,
                                            dif_pinmux_pad_kind_t type,
                                            bool *in_sleep_mode) {
  if (pinmux == NULL || in_sleep_mode == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t reg_offset;
  bitfield_bit32_index_t bit;
  if (!dif_pinmux_get_sleep_status_bit(type, pad, &reg_offset, &bit)) {
    return kDifBadArg;
  }

  uint32_t reg_value = mmio_region_read32(pinmux->base_addr, reg_offset);
  *in_sleep_mode = bitfield_bit32_read(reg_value, bit);
  return kDifOk;
}

dif_result_t dif_pinmux_pad_sleep_clear_state(const dif_pinmux_t *pinmux,
                                              dif_pinmux_index_t pad,
                                              dif_pinmux_pad_kind_t type) {
  if (pinmux == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t reg_offset;
  bitfield_bit32_index_t bit;
  if (!dif_pinmux_get_sleep_status_bit(type, pad, &reg_offset, &bit)) {
    return kDifBadArg;
  }

  uint32_t reg_value = mmio_region_read32(pinmux->base_addr, reg_offset);
  reg_value = bitfield_bit32_write(reg_value, bit, 0);
  mmio_region_write32(pinmux->base_addr, reg_offset, reg_value);
  return kDifOk;
}

dif_result_t dif_pinmux_wakeup_detector_enable(
    const dif_pinmux_t *pinmux, dif_pinmux_index_t detector,
    dif_pinmux_wakeup_config_t config) {
  // Disable the detector before changing config, and use that function for
  // some input checking (null pointer, lock status, and detector validity
  // checks).
  dif_result_t result = dif_pinmux_wakeup_detector_disable(pinmux, detector);
  if (result != kDifOk) {
    return result;
  }

  bool set_count = false;
  uint32_t reg_mode_value;
  switch (config.mode) {
    case kDifPinmuxWakeupModePositiveEdge:
      reg_mode_value = PINMUX_WKUP_DETECTOR_0_MODE_0_VALUE_POSEDGE;
      break;
    case kDifPinmuxWakeupModeNegativeEdge:
      reg_mode_value = PINMUX_WKUP_DETECTOR_0_MODE_0_VALUE_NEGEDGE;
      break;
    case kDifPinmuxWakeupModeAnyEdge:
      reg_mode_value = PINMUX_WKUP_DETECTOR_0_MODE_0_VALUE_EDGE;
      break;
    case kDifPinmuxWakeupModeTimedHigh:
      set_count = true;
      reg_mode_value = PINMUX_WKUP_DETECTOR_0_MODE_0_VALUE_TIMEDHIGH;
      break;
    case kDifPinmuxWakeupModeTimedLow:
      set_count = true;
      reg_mode_value = PINMUX_WKUP_DETECTOR_0_MODE_0_VALUE_TIMEDLOW;
      break;
    default:
      return kDifBadArg;
  }

  bool reg_filter_value = dif_toggle_to_bool(config.signal_filter);
  if (!dif_is_valid_toggle(config.signal_filter)) {
    return kDifBadArg;
  }

  bool reg_miodio_value;
  switch (config.pad_type) {
    case kDifPinmuxPadKindMio:
      if (config.pad_select >= (2 + PINMUX_PARAM_N_MIO_PADS)) {
        return kDifBadArg;
      }
      reg_miodio_value = false;
      break;
    case kDifPinmuxPadKindDio:
      if (config.pad_select >= PINMUX_PARAM_N_DIO_PADS) {
        return kDifBadArg;
      }
      reg_miodio_value = true;
      break;
    default:
      return kDifBadArg;
  }

  ptrdiff_t reg_offset = PINMUX_WKUP_DETECTOR_0_REG_OFFSET +
                         (ptrdiff_t)detector * (ptrdiff_t)sizeof(uint32_t);
  uint32_t reg_value = bitfield_field32_write(
      0, PINMUX_WKUP_DETECTOR_0_MODE_0_FIELD, reg_mode_value);
  reg_value = bitfield_bit32_write(
      reg_value, PINMUX_WKUP_DETECTOR_0_FILTER_0_BIT, reg_filter_value);
  reg_value = bitfield_bit32_write(
      reg_value, PINMUX_WKUP_DETECTOR_0_MIODIO_0_BIT, reg_miodio_value);
  mmio_region_write32(pinmux->base_addr, reg_offset, reg_value);

  if (set_count) {
    reg_offset = PINMUX_WKUP_DETECTOR_CNT_TH_0_REG_OFFSET +
                 (ptrdiff_t)detector * (ptrdiff_t)sizeof(uint32_t);
    reg_value = bitfield_field32_write(
        0, PINMUX_WKUP_DETECTOR_CNT_TH_0_TH_0_FIELD, config.counter_threshold);
    mmio_region_write32(pinmux->base_addr, reg_offset, reg_value);
  }

  reg_offset = PINMUX_WKUP_DETECTOR_PADSEL_0_REG_OFFSET +
               (ptrdiff_t)detector * (ptrdiff_t)sizeof(uint32_t);
  reg_value = bitfield_field32_write(
      0, PINMUX_WKUP_DETECTOR_PADSEL_0_SEL_0_FIELD, config.pad_select);
  mmio_region_write32(pinmux->base_addr, reg_offset, reg_value);

  reg_offset = PINMUX_WKUP_DETECTOR_EN_0_REG_OFFSET +
               (ptrdiff_t)detector * (ptrdiff_t)sizeof(uint32_t);
  reg_value = bitfield_bit32_write(0, PINMUX_WKUP_DETECTOR_EN_0_EN_0_BIT, true);
  mmio_region_write32(pinmux->base_addr, reg_offset, reg_value);
  return kDifOk;
}

dif_result_t dif_pinmux_wakeup_detector_disable(const dif_pinmux_t *pinmux,
                                                dif_pinmux_index_t detector) {
  if (pinmux == NULL) {
    return kDifBadArg;
  }
  if (detector >= PINMUX_PARAM_N_WKUP_DETECT) {
    return kDifBadArg;
  }
  bool is_locked;
  dif_result_t result = dif_pinmux_is_locked(
      pinmux, detector, kDifPinmuxLockTargetWakeupDetector, &is_locked);
  if (result != kDifOk) {
    return result;
  }
  if (is_locked) {
    return kDifLocked;
  }

  ptrdiff_t reg_offset = PINMUX_WKUP_DETECTOR_EN_0_REG_OFFSET +
                         (ptrdiff_t)sizeof(uint32_t) * (ptrdiff_t)detector;
  mmio_region_write32(pinmux->base_addr, reg_offset, 0);
  return kDifOk;
}

dif_result_t dif_pinmux_wakeup_cause_clear(const dif_pinmux_t *pinmux) {
  if (pinmux == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(pinmux->base_addr, PINMUX_WKUP_CAUSE_REG_OFFSET, 0);
  return kDifOk;
}

dif_result_t dif_pinmux_wakeup_cause_get(const dif_pinmux_t *pinmux,
                                         uint32_t *detector_map) {
  if (pinmux == NULL) {
    return kDifBadArg;
  }
  *detector_map =
      mmio_region_read32(pinmux->base_addr, PINMUX_WKUP_CAUSE_REG_OFFSET);
  return kDifOk;
}
