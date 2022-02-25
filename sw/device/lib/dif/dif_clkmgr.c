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
