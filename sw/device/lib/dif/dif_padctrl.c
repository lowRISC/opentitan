// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stddef.h>

#include "sw/device/lib/dif/dif_padctrl.h"

// Generated.
// Note that if the the number of DIO or MIO pads is such that all attribute can
// fit in one register the PADCTRL_DIO_PADS0_REG_OFFSET and
// PADCTRL_MIO_PADS0_REG_OFFSET #defines from padctrl_regs.h will no longer
// contain '0' and become PADCTRL_DIO_PADS_REG_OFFSET and
// PADCTRL_MIO_PADS_REG_OFFSET respectively which will require altering their
// names in the source below.
#include "padctrl_regs.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"

_Static_assert(PADCTRL_PARAM_NDIOPADS == 15,
               "Padctrl instantiation parameters have changed");
_Static_assert(PADCTRL_PARAM_NMIOPADS == 32,
               "Padctrl instantiation parameters have changed");
_Static_assert(PADCTRL_PARAM_ATTRDW == 8,
               "Padctrl instantiation parameters have changed");
_Static_assert(PADCTRL_MIO_PADS_ATTR_FIELDS_PER_REG ==
                   PADCTRL_DIO_PADS_ATTR_FIELDS_PER_REG,
               "Padctrl instantiation parameters have changed");

/**
 * The width of a padctrl attribute register in bytes.
 */
static const uint32_t kPadctrlRegisterWidthInBytes =
    (PADCTRL_PARAM_REG_WIDTH / 8);

/**
 * Bit mask for a single attribute field in a pad register.
 */
static const uint32_t kPadctrlAttrFieldMask = PADCTRL_MIO_PADS0_ATTR0_MASK;

/**
 * Checks if an attribute field contains conflicting attributes
 */
static bool conflicting_attributes(dif_padctrl_attr_t attrs) {
  // Cannot be both pull up and pull down
  if ((attrs & kDifPadctrlAttrPullDown) && (attrs & kDifPadctrlAttrPullUp)) {
    return true;
  }

  // Cannot combine pull down with open drain
  if ((attrs & kDifPadctrlAttrPullDown) && (attrs & kDifPadctrlAttrOpenDrain)) {
    return true;
  }

  return false;
}

/**
 * Check if a given pad `kind` and `index` refers to a valid pad
 */
static bool is_pad_index_valid(dif_padctrl_pad_kind_t kind,
                               dif_padctrl_pad_index_t index) {
  if (kind == kDifPadctrlPadMio) {
    return index < PADCTRL_PARAM_NMIOPADS;
  } else {
    return index < PADCTRL_PARAM_NDIOPADS;
  }
}

/**
 * Check any bit set in `attrs` corresponds to a valid attribute
 */
static bool attrs_are_valid(dif_padctrl_attr_t attrs) {
  return (attrs & ~kPadctrlAttrFieldMask) == 0;
}

/**
 * Calculate the `bitfield_field32_t` needed to access a pad's attribute field.
 * Assumes the pad is a valid one.
 */
static bitfield_field32_t calc_pad_attr_field(dif_padctrl_pad_kind_t kind,
                                              dif_padctrl_pad_index_t index) {
  return (bitfield_field32_t){
      .index =
          (index % PADCTRL_MIO_PADS_ATTR_FIELDS_PER_REG) * PADCTRL_PARAM_ATTRDW,
      .mask = kPadctrlAttrFieldMask,
  };
}

/**
 * Calculate the register offset for a pad's attribute register. Assumes the pad
 * is a valid one.
 */
static ptrdiff_t calc_pad_attr_reg_offset(dif_padctrl_pad_kind_t kind,
                                          dif_padctrl_pad_index_t index) {
  ptrdiff_t base_register_offset;
  if (kind == kDifPadctrlPadMio) {
    base_register_offset = PADCTRL_MIO_PADS0_REG_OFFSET;
  } else {
    base_register_offset = PADCTRL_DIO_PADS0_REG_OFFSET;
  }

  uint32_t register_index;
  register_index = index / PADCTRL_MIO_PADS_ATTR_FIELDS_PER_REG;

  return base_register_offset + (kPadctrlRegisterWidthInBytes * register_index);
}

/**
 * Returns true if padctrl is locked, assumes `padctrl` argument is valid
 */
static bool padctrl_is_locked(const dif_padctrl_t *padctrl) {
  return !mmio_region_get_bit32(padctrl->base_addr, PADCTRL_REGEN_REG_OFFSET,
                                PADCTRL_REGEN_WEN);
}

/**
 * Pad change types for use with `change_attrs`
 */
typedef enum attr_change_type {
  kAttrChangeEnable,  /**< Enable attributes that have bit set. */
  kAttrChangeDisable, /**< Disable attributes that have bit set. */
  kAttrChangeWrite    /**< Overwrite field with provided bits. */
} attr_change_type_t;

/**
 * Change attributes for a particular pad.
 *
 * @param padctrl Padctrl state data.
 * @param kind What kind of pad is being changed.
 * @param index Which pad is being changed.
 * @param attrs Attribute bits that specify the change.
 * @param change_type What change is applied using the `change_attrs`.
 * @return dif_padctrl_change_attr_result_t.
 */
static dif_padctrl_change_attr_result_t change_attrs(
    const dif_padctrl_t *padctrl, dif_padctrl_pad_kind_t kind,
    dif_padctrl_pad_index_t index, dif_padctrl_attr_t attrs,
    attr_change_type_t change_type) {
  // Check arguments before doing anything.
  if (padctrl == NULL) {
    return kDifPadctrlChangeAttrBadArg;
  }

  if (!is_pad_index_valid(kind, index)) {
    return kDifPadctrlChangeAttrBadArg;
  }

  if (!attrs_are_valid(attrs)) {
    return kDifPadctrlChangeAttrBadArg;
  }

  // Cannot continue with locked padctrl as registers cannot be altered.
  if (padctrl_is_locked(padctrl)) {
    return kDifPadctrlChangeAttrLocked;
  }

  // Calculate which register and which field within it relate to the pad that
  // is the target of the attribute change.
  uint32_t attr_reg_offset = calc_pad_attr_reg_offset(kind, index);

  // Read current attribute register and extract relevant field.
  uint32_t attr_reg_value =
      mmio_region_read32(padctrl->base_addr, attr_reg_offset);
  bitfield_field32_t attr_field = calc_pad_attr_field(kind, index);
  attr_field.value = bitfield_get_field32(attr_reg_value, attr_field);

  // Alter field depending upon change type.
  switch (change_type) {
    case kAttrChangeEnable:
      attr_field.value |= attrs;
      break;
    case kAttrChangeDisable:
      attr_field.value &= ~attrs;
      break;
    case kAttrChangeWrite:
      attr_field.value = attrs;
      break;
    default:
      return kDifPadctrlError;
  }

  // Check if the new setting causes a conflict.
  if (conflicting_attributes(attr_field.value)) {
    return kDifPadctrlChangeAttrConflict;
  }

  // Write back updated value to attribute register.
  uint32_t new_attr_reg_value =
      bitfield_set_field32(attr_reg_value, attr_field);
  mmio_region_write32(padctrl->base_addr, attr_reg_offset, new_attr_reg_value);

  return kDifPadctrlChangeAttrOk;
}

dif_padctrl_result_t dif_padctrl_init(mmio_region_t base_addr,
                                      dif_padctrl_t *padctrl) {
  if (padctrl == NULL) {
    return kDifPadctrlBadArg;
  }

  padctrl->base_addr = base_addr;

  return kDifPadctrlOk;
}

dif_padctrl_reset_result_t dif_padctrl_reset(dif_padctrl_t *padctrl,
                                             dif_padctrl_attr_t reset_attrs) {
  if (padctrl == NULL) {
    return kDifPadctrlResetBadArg;
  }

  if (!attrs_are_valid(reset_attrs)) {
    return kDifPadctrlResetBadArg;
  }

  if (padctrl_is_locked(padctrl)) {
    return kDifPadctrlResetLocked;
  }

  // Form attribute register reset value from reptitions of reset_attrs
  // appropriately shifted and combined.
  uint32_t attr_reg_reset_val = 0;
  for (int i = 0; i < PADCTRL_MIO_PADS_ATTR_FIELDS_PER_REG; ++i) {
    attr_reg_reset_val <<= PADCTRL_PARAM_ATTRDW;
    attr_reg_reset_val |= reset_attrs;
  }

  // Reset all DIO pad attributes to the desired reset value.
  for (int i = 0; i < PADCTRL_DIO_PADS_MULTIREG_COUNT; ++i) {
    ptrdiff_t dio_pads_register_offset =
        PADCTRL_DIO_PADS0_REG_OFFSET + (i * kPadctrlRegisterWidthInBytes);
    mmio_region_write32(padctrl->base_addr, dio_pads_register_offset,
                        attr_reg_reset_val);
  }

  // Reset all MIO pad attributes to the desired reset value.
  for (int i = 0; i < PADCTRL_MIO_PADS_MULTIREG_COUNT; ++i) {
    ptrdiff_t mio_pads_register_offset =
        PADCTRL_MIO_PADS0_REG_OFFSET + (i * kPadctrlRegisterWidthInBytes);
    mmio_region_write32(padctrl->base_addr, mio_pads_register_offset,
                        attr_reg_reset_val);
  }

  return kDifPadctrlResetOk;
}

dif_padctrl_result_t dif_padctrl_lock(dif_padctrl_t *padctrl) {
  if (padctrl == NULL) {
    return kDifPadctrlBadArg;
  }

  mmio_region_write32(padctrl->base_addr, PADCTRL_REGEN_REG_OFFSET, 0);

  return kDifPadctrlOk;
}

dif_padctrl_change_attr_result_t dif_padctrl_enable_attrs(
    const dif_padctrl_t *padctrl, dif_padctrl_pad_kind_t kind,
    dif_padctrl_pad_index_t index, dif_padctrl_attr_t enable_attrs) {
  return change_attrs(padctrl, kind, index, enable_attrs, kAttrChangeEnable);
}

dif_padctrl_change_attr_result_t dif_padctrl_disable_attrs(
    const dif_padctrl_t *padctrl, dif_padctrl_pad_kind_t kind,
    dif_padctrl_pad_index_t index, dif_padctrl_attr_t disable_attrs) {
  return change_attrs(padctrl, kind, index, disable_attrs, kAttrChangeDisable);
}

dif_padctrl_change_attr_result_t dif_padctrl_write_attrs(
    const dif_padctrl_t *padctrl, dif_padctrl_pad_kind_t kind,
    dif_padctrl_pad_index_t index, dif_padctrl_attr_t write_attrs) {
  return change_attrs(padctrl, kind, index, write_attrs, kAttrChangeWrite);
}

dif_padctrl_result_t dif_padctrl_get_attrs(const dif_padctrl_t *padctrl,
                                           dif_padctrl_pad_kind_t kind,
                                           dif_padctrl_pad_index_t index,
                                           dif_padctrl_attr_t *attrs_out) {
  if (padctrl == NULL) {
    return kDifPadctrlBadArg;
  }

  if (attrs_out == NULL) {
    return kDifPadctrlBadArg;
  }

  if (!is_pad_index_valid(kind, index)) {
    return kDifPadctrlBadArg;
  }

  // Calculate which register and which field within it relate to the pad that
  // is the target of the attribute change.
  bitfield_field32_t attr_field = calc_pad_attr_field(kind, index);
  uint32_t attr_reg_offset = calc_pad_attr_reg_offset(kind, index);

  // Read current attribute register and extract relevant field.
  uint32_t attr_reg_value =
      mmio_region_read32(padctrl->base_addr, attr_reg_offset);
  *attrs_out = bitfield_get_field32(attr_reg_value, attr_field);

  return kDifPadctrlOk;
}
