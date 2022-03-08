// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_clkmgr.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_base.h"

#include "clkmgr_regs.h"  // Generated

// TODO: For the moment, CLKMGR_PARAM_NUM_SW_GATEABLE_CLOCKS has to be <= than
// 32, as we only support one enable register for gateable clocks.
// https://github.com/lowRISC/opentitan/issues/4201
static_assert(
    CLKMGR_PARAM_NUM_SW_GATEABLE_CLOCKS <= CLKMGR_PARAM_REG_WIDTH,
    "Expected the number of gateable clocks to be <= the width of a CSR.");

// TODO: For the moment, CLKMGR_PARAM_NUM_HINTABLE_CLOCKS has to be <= than
// 32, as we only support one enable/hint_status register for hintable clocks.
// https://github.com/lowRISC/opentitan/issues/4201
static_assert(
    CLKMGR_PARAM_NUM_HINTABLE_CLOCKS <= CLKMGR_PARAM_REG_WIDTH,
    "Expected the number of hintable clocks to be <= the width of a CSR.");

static bool clkmgr_valid_gateable_clock(dif_clkmgr_gateable_clock_t clock) {
  return clock < CLKMGR_PARAM_NUM_SW_GATEABLE_CLOCKS;
}

static bool clkmgr_valid_hintable_clock(dif_clkmgr_hintable_clock_t clock) {
  return clock < CLKMGR_PARAM_NUM_HINTABLE_CLOCKS;
}

static bool clkmgr_measure_ctrl_regwen(const dif_clkmgr_t *clkmgr) {
  uint32_t measure_ctrl_regwen_val = mmio_region_read32(
      clkmgr->base_addr, CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET);
  return bitfield_bit32_read(measure_ctrl_regwen_val,
                             CLKMGR_MEASURE_CTRL_REGWEN_EN_BIT);
}

dif_result_t dif_clkmgr_jitter_get_enabled(const dif_clkmgr_t *clkmgr,
                                           dif_toggle_t *state) {
  if (clkmgr == NULL || state == NULL) {
    return kDifBadArg;
  }

  multi_bit_bool_t clk_jitter_val =
      mmio_region_read32(clkmgr->base_addr, CLKMGR_JITTER_ENABLE_REG_OFFSET);
  *state = dif_multi_bit_bool_to_toggle(clk_jitter_val);

  return kDifOk;
}

dif_result_t dif_clkmgr_jitter_set_enabled(const dif_clkmgr_t *clkmgr,
                                           dif_toggle_t new_state) {
  multi_bit_bool_t new_jitter_enable_val;
  if (clkmgr == NULL) {
    return kDifBadArg;
  }

  switch (new_state) {
    case kDifToggleEnabled:
      new_jitter_enable_val = kMultiBitBool4True;
      break;
    case kDifToggleDisabled:
      new_jitter_enable_val = kMultiBitBool4False;
      break;
    default:
      return kDifBadArg;
  }
  mmio_region_write32(clkmgr->base_addr, CLKMGR_JITTER_ENABLE_REG_OFFSET,
                      new_jitter_enable_val);
  return kDifOk;
}

dif_result_t dif_clkmgr_gateable_clock_get_enabled(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_gateable_clock_t clock,
    dif_toggle_t *state) {
  if (clkmgr == NULL || state == NULL || !clkmgr_valid_gateable_clock(clock)) {
    return kDifBadArg;
  }

  uint32_t clk_enables_val =
      mmio_region_read32(clkmgr->base_addr, CLKMGR_CLK_ENABLES_REG_OFFSET);
  *state = dif_bool_to_toggle(bitfield_bit32_read(clk_enables_val, clock));

  return kDifOk;
}

dif_result_t dif_clkmgr_gateable_clock_set_enabled(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_gateable_clock_t clock,
    dif_toggle_t new_state) {
  if (clkmgr == NULL || !clkmgr_valid_gateable_clock(clock) ||
      !dif_is_valid_toggle(new_state)) {
    return kDifBadArg;
  }

  bool new_clk_enables_bit = dif_toggle_to_bool(new_state);
  uint32_t clk_enables_val =
      mmio_region_read32(clkmgr->base_addr, CLKMGR_CLK_ENABLES_REG_OFFSET);
  clk_enables_val =
      bitfield_bit32_write(clk_enables_val, clock, new_clk_enables_bit);
  mmio_region_write32(clkmgr->base_addr, CLKMGR_CLK_ENABLES_REG_OFFSET,
                      clk_enables_val);

  return kDifOk;
}

dif_result_t dif_clkmgr_hintable_clock_get_enabled(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock,
    dif_toggle_t *state) {
  if (clkmgr == NULL || state == NULL || !clkmgr_valid_hintable_clock(clock)) {
    return kDifBadArg;
  }

  uint32_t clk_hints_val =
      mmio_region_read32(clkmgr->base_addr, CLKMGR_CLK_HINTS_STATUS_REG_OFFSET);
  *state = dif_bool_to_toggle(bitfield_bit32_read(clk_hints_val, clock));

  return kDifOk;
}

dif_result_t dif_clkmgr_hintable_clock_set_hint(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock,
    dif_toggle_t new_state) {
  if (clkmgr == NULL || !clkmgr_valid_hintable_clock(clock) ||
      !dif_is_valid_toggle(new_state)) {
    return kDifBadArg;
  }

  bool new_clk_hints_bit = dif_toggle_to_bool(new_state);
  uint32_t clk_hints_val =
      mmio_region_read32(clkmgr->base_addr, CLKMGR_CLK_HINTS_REG_OFFSET);
  clk_hints_val = bitfield_bit32_write(clk_hints_val, clock, new_clk_hints_bit);
  mmio_region_write32(clkmgr->base_addr, CLKMGR_CLK_HINTS_REG_OFFSET,
                      clk_hints_val);

  return kDifOk;
}

dif_result_t dif_clkmgr_hintable_clock_get_hint(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock,
    dif_toggle_t *state) {
  if (clkmgr == NULL || state == NULL || !clkmgr_valid_hintable_clock(clock)) {
    return kDifBadArg;
  }

  uint32_t clk_hints_val =
      mmio_region_read32(clkmgr->base_addr, CLKMGR_CLK_HINTS_REG_OFFSET);
  *state = dif_bool_to_toggle(bitfield_bit32_read(clk_hints_val, clock));

  return kDifOk;
}

dif_result_t dif_clkmgr_external_clock_set_enabled(const dif_clkmgr_t *clkmgr,
                                                   bool is_low_speed) {
  uint32_t extclk_ctrl_reg = 0;

  if (clkmgr == NULL) {
    return kDifBadArg;
  }

  extclk_ctrl_reg = bitfield_field32_write(
      extclk_ctrl_reg, CLKMGR_EXTCLK_CTRL_SEL_FIELD, kMultiBitBool4True);
  extclk_ctrl_reg = bitfield_field32_write(
      extclk_ctrl_reg, CLKMGR_EXTCLK_CTRL_HI_SPEED_SEL_FIELD,
      is_low_speed ? kMultiBitBool4False : kMultiBitBool4True);
  mmio_region_write32(clkmgr->base_addr, CLKMGR_EXTCLK_CTRL_REG_OFFSET,
                      extclk_ctrl_reg);
  return kDifOk;
}

dif_result_t dif_clkmgr_measure_ctrl_disable(const dif_clkmgr_t *clkmgr) {
  if (clkmgr == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(clkmgr->base_addr, CLKMGR_MEASURE_CTRL_REGWEN_REG_OFFSET,
                      0);
  return kDifOk;
}

dif_result_t dif_clkmgr_measure_ctrl_get_enable(const dif_clkmgr_t *clkmgr,
                                                dif_toggle_t *state) {
  if (clkmgr == NULL || state == NULL) {
    return kDifBadArg;
  }
  *state = dif_bool_to_toggle(clkmgr_measure_ctrl_regwen(clkmgr));
  return kDifOk;
}

dif_result_t dif_clkmgr_enable_measure_counts(const dif_clkmgr_t *clkmgr,
                                              dif_clkmgr_measure_clock_t clock,
                                              uint32_t lo_threshold,
                                              uint32_t hi_threshold) {
  if (clkmgr == NULL) {
    return kDifBadArg;
  }
  if (!clkmgr_measure_ctrl_regwen(clkmgr)) {
    return kDifLocked;
  }

  uint32_t reg_offset;
  bitfield_bit32_index_t en_index;
  bitfield_field32_t lo_field;
  bitfield_field32_t hi_field;
  switch (clock) {
#define PICK_COUNT_CTRL_FIELDS(kind_)                          \
  reg_offset = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_REG_OFFSET; \
  en_index = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_EN_BIT;       \
  lo_field = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_LO_FIELD;     \
  hi_field = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_HI_FIELD;     \
  break  // No semicolon to force semicolon below.
    case kDifClkmgrMeasureClockIo:
      PICK_COUNT_CTRL_FIELDS(IO);
    case kDifClkmgrMeasureClockIoDiv2:
      PICK_COUNT_CTRL_FIELDS(IO_DIV2);
    case kDifClkmgrMeasureClockIoDiv4:
      PICK_COUNT_CTRL_FIELDS(IO_DIV4);
    case kDifClkmgrMeasureClockMain:
      PICK_COUNT_CTRL_FIELDS(MAIN);
    case kDifClkmgrMeasureClockUsb:
      PICK_COUNT_CTRL_FIELDS(USB);
    default:
      return kDifBadArg;
#undef PICK_COUNT_CTRL_FIELDS
  }

  uint32_t measure_ctrl_reg = 0;
  measure_ctrl_reg = bitfield_bit32_write(measure_ctrl_reg, en_index, 1);
  measure_ctrl_reg =
      bitfield_field32_write(measure_ctrl_reg, lo_field, lo_threshold);
  measure_ctrl_reg =
      bitfield_field32_write(measure_ctrl_reg, hi_field, hi_threshold);
  // Two writes, because these registers are shadowed.
  mmio_region_write32(clkmgr->base_addr, reg_offset, measure_ctrl_reg);
  mmio_region_write32(clkmgr->base_addr, reg_offset, measure_ctrl_reg);

  return kDifOk;
}

dif_result_t dif_clkmgr_disable_measure_counts(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_measure_clock_t clock) {
  if (clkmgr == NULL) {
    return kDifBadArg;
  }
  if (!clkmgr_measure_ctrl_regwen(clkmgr)) {
    return kDifLocked;
  }

  uint32_t reg_offset;
  switch (clock) {
    case kDifClkmgrMeasureClockIo:
      reg_offset = CLKMGR_IO_MEAS_CTRL_SHADOWED_REG_OFFSET;
      break;
    case kDifClkmgrMeasureClockIoDiv2:
      reg_offset = CLKMGR_IO_DIV2_MEAS_CTRL_SHADOWED_REG_OFFSET;
      break;
    case kDifClkmgrMeasureClockIoDiv4:
      reg_offset = CLKMGR_IO_DIV4_MEAS_CTRL_SHADOWED_REG_OFFSET;
      break;
    case kDifClkmgrMeasureClockMain:
      reg_offset = CLKMGR_MAIN_MEAS_CTRL_SHADOWED_REG_OFFSET;
      break;
    case kDifClkmgrMeasureClockUsb:
      reg_offset = CLKMGR_USB_MEAS_CTRL_SHADOWED_REG_OFFSET;
      break;
    default:
      return kDifBadArg;
  }
  // Two writes, because these registers are shadowed.
  mmio_region_write32(clkmgr->base_addr, reg_offset, 0);
  mmio_region_write32(clkmgr->base_addr, reg_offset, 0);
  return kDifOk;
}

dif_result_t dif_clkmgr_recov_err_code_get_codes(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_recov_err_codes_t *codes) {
  if (clkmgr == NULL || codes == NULL) {
    return kDifBadArg;
  }
  *codes =
      mmio_region_read32(clkmgr->base_addr, CLKMGR_RECOV_ERR_CODE_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_clkmgr_recov_err_code_clear_codes(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_recov_err_codes_t codes) {
  if (clkmgr == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(clkmgr->base_addr, CLKMGR_RECOV_ERR_CODE_REG_OFFSET,
                      codes);
  return kDifOk;
}
