// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"

#include "clkmgr_regs.h"  // Generated

static bool clkmgr_valid_gateable_clock(dif_clkmgr_params_t params,
                                        dif_clkmgr_gateable_clock_t clock) {
  // TODO For the moment, last_gateable_clocks has to be less than 32, as we
  // only support one enable register for gateable clocks.
  // https://github.com/lowRISC/opentitan/issues/4201
  return (clock <= params.last_gateable_clock) &&
         (params.last_gateable_clock < CLKMGR_PARAM_REG_WIDTH);
}

static bool clkmgr_valid_hintable_clock(dif_clkmgr_params_t params,
                                        dif_clkmgr_hintable_clock_t clock) {
  // TODO: For the moment, last_hintable_clocks has to be less than 32, as we
  // only support one enable/hint_status register for hintable clocks.
  // https://github.com/lowRISC/opentitan/issues/4201
  return (clock <= params.last_hintable_clock) &&
         (params.last_hintable_clock < CLKMGR_PARAM_REG_WIDTH);
}

dif_clkmgr_result_t dif_clkmgr_init(dif_clkmgr_params_t params,
                                    dif_clkmgr_t *handle) {
  if (handle == NULL) {
    return kDifClkmgrBadArg;
  }

  // TODO: For the moment, `last_hintable_clock` and `last_gateable_clock` has
  // to be less than 32, as we only support one register of bits for each.
  // https://github.com/lowRISC/opentitan/issues/4201
  if (params.last_gateable_clock >= CLKMGR_PARAM_REG_WIDTH ||
      params.last_hintable_clock >= CLKMGR_PARAM_REG_WIDTH) {
    return kDifClkmgrBadArg;
  }

  handle->params = params;
  return kDifClkmgrOk;
}

dif_clkmgr_result_t dif_clkmgr_gateable_clock_get_enabled(
    const dif_clkmgr_t *handle, dif_clkmgr_gateable_clock_t clock,
    bool *is_enabled) {
  if (handle == NULL || is_enabled == NULL ||
      !clkmgr_valid_gateable_clock(handle->params, clock)) {
    return kDifClkmgrBadArg;
  }

  uint32_t clk_enables_val = mmio_region_read32(handle->params.base_addr,
                                                CLKMGR_CLK_ENABLES_REG_OFFSET);
  *is_enabled = bitfield_bit32_read(clk_enables_val, clock);

  return kDifClkmgrOk;
}

dif_clkmgr_result_t dif_clkmgr_gateable_clock_set_enabled(
    const dif_clkmgr_t *handle, dif_clkmgr_gateable_clock_t clock,
    dif_clkmgr_toggle_t new_state) {
  if (handle == NULL || !clkmgr_valid_gateable_clock(handle->params, clock)) {
    return kDifClkmgrBadArg;
  }

  bool new_clk_enables_bit;
  switch (new_state) {
    case kDifClkmgrToggleEnabled:
      new_clk_enables_bit = true;
      break;
    case kDifClkmgrToggleDisabled:
      new_clk_enables_bit = false;
      break;
    default:
      return kDifClkmgrBadArg;
  }

  uint32_t clk_enables_val = mmio_region_read32(handle->params.base_addr,
                                                CLKMGR_CLK_ENABLES_REG_OFFSET);
  clk_enables_val =
      bitfield_bit32_write(clk_enables_val, clock, new_clk_enables_bit);
  mmio_region_write32(handle->params.base_addr, CLKMGR_CLK_ENABLES_REG_OFFSET,
                      clk_enables_val);

  return kDifClkmgrOk;
}

dif_clkmgr_result_t dif_clkmgr_hintable_clock_get_enabled(
    const dif_clkmgr_t *handle, dif_clkmgr_hintable_clock_t clock,
    bool *is_enabled) {
  if (handle == NULL || is_enabled == NULL ||
      !clkmgr_valid_hintable_clock(handle->params, clock)) {
    return kDifClkmgrBadArg;
  }

  uint32_t clk_hints_val = mmio_region_read32(
      handle->params.base_addr, CLKMGR_CLK_HINTS_STATUS_REG_OFFSET);
  *is_enabled = bitfield_bit32_read(clk_hints_val, clock);

  return kDifClkmgrOk;
}

dif_clkmgr_result_t dif_clkmgr_hintable_clock_set_hint(
    const dif_clkmgr_t *handle, dif_clkmgr_hintable_clock_t clock,
    dif_clkmgr_toggle_t new_state) {
  if (handle == NULL || !clkmgr_valid_hintable_clock(handle->params, clock)) {
    return kDifClkmgrBadArg;
  }

  bool new_clk_hints_bit;
  switch (new_state) {
    case kDifClkmgrToggleEnabled:
      new_clk_hints_bit = true;
      break;
    case kDifClkmgrToggleDisabled:
      new_clk_hints_bit = false;
      break;
    default:
      return kDifClkmgrBadArg;
  }

  uint32_t clk_hints_val =
      mmio_region_read32(handle->params.base_addr, CLKMGR_CLK_HINTS_REG_OFFSET);
  clk_hints_val = bitfield_bit32_write(clk_hints_val, clock, new_clk_hints_bit);
  mmio_region_write32(handle->params.base_addr, CLKMGR_CLK_HINTS_REG_OFFSET,
                      clk_hints_val);

  return kDifClkmgrOk;
}

dif_clkmgr_result_t dif_clkmgr_hintable_clock_get_hint(
    const dif_clkmgr_t *handle, dif_clkmgr_hintable_clock_t clock,
    bool *hinted_is_enabled) {
  if (handle == NULL || hinted_is_enabled == NULL ||
      !clkmgr_valid_hintable_clock(handle->params, clock)) {
    return kDifClkmgrBadArg;
  }

  uint32_t clk_hints_val =
      mmio_region_read32(handle->params.base_addr, CLKMGR_CLK_HINTS_REG_OFFSET);
  *hinted_is_enabled = bitfield_bit32_read(clk_hints_val, clock);

  return kDifClkmgrOk;
}
