// Copyright lowRISC contributors (OpenTitan project).
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

dif_result_t dif_clkmgr_external_clock_is_settled(const dif_clkmgr_t *clkmgr,
                                                  bool *status) {
  if (clkmgr == NULL || status == NULL) {
    return kDifBadArg;
  }
  uint32_t extclk_status_val =
      mmio_region_read32(clkmgr->base_addr, CLKMGR_EXTCLK_STATUS_REG_OFFSET);
  *status = bitfield_field32_read(extclk_status_val,
                                  CLKMGR_EXTCLK_STATUS_ACK_FIELD) ==
            kMultiBitBool4True;

  return kDifOk;
}

dif_result_t dif_clkmgr_jitter_get_enabled(const dif_clkmgr_t *clkmgr,
                                           dif_toggle_t *state) {
  if (clkmgr == NULL || state == NULL) {
    return kDifBadArg;
  }

  multi_bit_bool_t clk_jitter_val =
      mmio_region_read32(clkmgr->base_addr, CLKMGR_JITTER_ENABLE_REG_OFFSET);
  // The documentation states that kMultiBitBool4False disables the jittery
  // clock and all other values enable the jittery clock.
  *state = clk_jitter_val != kMultiBitBool4False;

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

dif_result_t dif_clkmgr_external_clock_set_disabled(
    const dif_clkmgr_t *clkmgr) {
  uint32_t extclk_ctrl_reg = 0;

  if (clkmgr == NULL) {
    return kDifBadArg;
  }

  extclk_ctrl_reg = bitfield_field32_write(
      extclk_ctrl_reg, CLKMGR_EXTCLK_CTRL_SEL_FIELD, kMultiBitBool4False);
  // This value is irrelevant when the external clock is disabled.
  extclk_ctrl_reg = bitfield_field32_write(
      extclk_ctrl_reg, CLKMGR_EXTCLK_CTRL_HI_SPEED_SEL_FIELD,
      kMultiBitBool4True);
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

// The earlgrey and englishbreakfast CSR differences mean they have a
// different number of clock measuremen units. The ideal way to handle
// this difference is just generating the dif code, and we intend to do
// that with multi-top. However, for the time being we need to rely on
// macro trickery, just generating code for a specific measurement if
// there is a #define for the corresponding enable CSR offset.
//
// These macro are a tricky way to implement a macro like the following:
// #define CONDITIONALLY_DO        \ ...
//   #ifdef SOMETHING do_something \ ...
//   #else do_something_else       \ ...
//   #endif
// However, such macros are illegal in C. So the macros below implement
// the conditional using a suggestion presented in
// https://stackoverflow.com/questions/72266480/can-ifdef-be-used-inside-a-macro
//
// The reason we need these macros is to handle differences between earlgrey
// and englishbreakfast without generating the dif code.

// TODO(lowrisc/opentitan#19823): Remove this whole macro trickery once this
// file is generated.
#define CNCAT_IMPL(a_, b_) a_##b_
#define CNCAT(a_, b_) CNCAT_IMPL(a_, b_)
#define CHECK_CLKMGR_IO_MEAS_CTRL_EN_REG_OFFSET ~, ~
#define CHECK_CLKMGR_IO_DIV2_MEAS_CTRL_EN_REG_OFFSET ~, ~
#define CHECK_CLKMGR_IO_DIV4_MEAS_CTRL_EN_REG_OFFSET ~, ~
#define CHECK_CLKMGR_MAIN_MEAS_CTRL_EN_REG_OFFSET ~, ~
#define CHECK_CLKMGR_USB_MEAS_CTRL_EN_REG_OFFSET ~, ~
#define CHECK_IMPL(a_, b_, c_, ...) c_
#define CHECK(tup_) CHECK_IMPL tup_

#define IS_KIND_DEFINED(kind_) \
  CHECK((CNCAT(CHECK_, CLKMGR_##kind_##_MEAS_CTRL_EN_REG_OFFSET), 0, 1))

#define IIF_0(true_exp_, false_exp_) false_exp_
#define IIF_1(true_exp_, false_exp_) true_exp_
#define IIF(condition_, true_exp_, false_exp_) \
  CNCAT(IIF_, condition_)(true_exp_, false_exp_)

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

  uint32_t en_offset = 0;
  uint32_t reg_offset = 0;
  bitfield_field32_t en_field = (bitfield_field32_t){.mask = 0, .index = 0};
  bitfield_field32_t lo_field = (bitfield_field32_t){.mask = 0, .index = 0};
  bitfield_field32_t hi_field = (bitfield_field32_t){.mask = 0, .index = 0};
  switch (clock) {
#define PICK_COUNT_CTRL_FIELDS(kind_)                              \
  IIF(IS_KIND_DEFINED(kind_),                                      \
      en_offset = CLKMGR_##kind_##_MEAS_CTRL_EN_REG_OFFSET;        \
      reg_offset = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_REG_OFFSET; \
      en_field = CLKMGR_##kind_##_MEAS_CTRL_EN_EN_FIELD;           \
      lo_field = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_LO_FIELD;     \
      hi_field = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_HI_FIELD; break, break)

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
  measure_ctrl_reg =
      bitfield_field32_write(measure_ctrl_reg, lo_field, lo_threshold);
  measure_ctrl_reg =
      bitfield_field32_write(measure_ctrl_reg, hi_field, hi_threshold);
  // Two writes, because these registers are shadowed.
  mmio_region_write32(clkmgr->base_addr, (ptrdiff_t)reg_offset,
                      measure_ctrl_reg);
  mmio_region_write32(clkmgr->base_addr, (ptrdiff_t)reg_offset,
                      measure_ctrl_reg);

  uint32_t measure_en_reg = 0;
  measure_en_reg =
      bitfield_field32_write(measure_en_reg, en_field, kMultiBitBool4True);
  mmio_region_write32(clkmgr->base_addr, (ptrdiff_t)en_offset, measure_en_reg);

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

  uint32_t en_offset = 0;
  switch (clock) {
#define PICK_EN_OFFSET(kind_)                               \
  IIF(IS_KIND_DEFINED(kind_),                               \
      en_offset = CLKMGR_##kind_##_MEAS_CTRL_EN_REG_OFFSET; \
      break, break)

    case kDifClkmgrMeasureClockIo:
      PICK_EN_OFFSET(IO);
      break;
    case kDifClkmgrMeasureClockIoDiv2:
      PICK_EN_OFFSET(IO_DIV2);
      break;
    case kDifClkmgrMeasureClockIoDiv4:
      PICK_EN_OFFSET(IO_DIV4);
      break;
    case kDifClkmgrMeasureClockMain:
      PICK_EN_OFFSET(MAIN);
      break;
    case kDifClkmgrMeasureClockUsb:
      PICK_EN_OFFSET(USB);
      break;
    default:
      return kDifBadArg;
#undef PICK_EN_OFFSET
  }
  mmio_region_write32(clkmgr->base_addr, (ptrdiff_t)en_offset,
                      kMultiBitBool4False);
  return kDifOk;
}

dif_result_t dif_clkmgr_measure_counts_get_enable(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_measure_clock_t clock,
    dif_toggle_t *state) {
  if (clkmgr == NULL || state == NULL) {
    return kDifBadArg;
  }

  uint32_t en_offset = 0;
  switch (clock) {
#define PICK_EN_OFFSET(kind_)                               \
  IIF(IS_KIND_DEFINED(kind_),                               \
      en_offset = CLKMGR_##kind_##_MEAS_CTRL_EN_REG_OFFSET; \
      break, break)

    case kDifClkmgrMeasureClockIo:
      PICK_EN_OFFSET(IO);
    case kDifClkmgrMeasureClockIoDiv2:
      PICK_EN_OFFSET(IO_DIV2);
    case kDifClkmgrMeasureClockIoDiv4:
      PICK_EN_OFFSET(IO_DIV4);
    case kDifClkmgrMeasureClockMain:
      PICK_EN_OFFSET(MAIN);
    case kDifClkmgrMeasureClockUsb:
      PICK_EN_OFFSET(USB);
    default:
      return kDifBadArg;
#undef PICK_EN_OFFSET
  }
  multi_bit_bool_t en_val =
      mmio_region_read32(clkmgr->base_addr, (ptrdiff_t)en_offset);
  *state = dif_multi_bit_bool_to_toggle(en_val);

  return kDifOk;
}

dif_result_t dif_clkmgr_measure_counts_get_thresholds(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_measure_clock_t clock,
    uint32_t *min_threshold, uint32_t *max_threshold) {
  if (clkmgr == NULL || min_threshold == NULL || max_threshold == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_offset = 0;
  bitfield_field32_t lo_field = (bitfield_field32_t){.mask = 0, .index = 0};
  bitfield_field32_t hi_field = (bitfield_field32_t){.mask = 0, .index = 0};
  switch (clock) {
#define PICK_THRESHOLD_FIELDS(kind_)                               \
  IIF(IS_KIND_DEFINED(kind_),                                      \
      reg_offset = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_REG_OFFSET; \
      lo_field = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_LO_FIELD;     \
      hi_field = CLKMGR_##kind_##_MEAS_CTRL_SHADOWED_HI_FIELD; break, break)
    case kDifClkmgrMeasureClockIo:
      PICK_THRESHOLD_FIELDS(IO);
    case kDifClkmgrMeasureClockIoDiv2:
      PICK_THRESHOLD_FIELDS(IO_DIV2);
    case kDifClkmgrMeasureClockIoDiv4:
      PICK_THRESHOLD_FIELDS(IO_DIV4);
    case kDifClkmgrMeasureClockMain:
      PICK_THRESHOLD_FIELDS(MAIN);
    case kDifClkmgrMeasureClockUsb:
      PICK_THRESHOLD_FIELDS(USB);
    default:
      return kDifBadArg;
#undef PICK_THRESHOLD_FIELDS
  }
  uint32_t thresholds_val =
      mmio_region_read32(clkmgr->base_addr, (ptrdiff_t)reg_offset);
  *min_threshold = bitfield_field32_read(thresholds_val, lo_field);
  *max_threshold = bitfield_field32_read(thresholds_val, hi_field);

  return kDifOk;
}

#undef CNCAT_IMPL
#undef CNCAT
#undef CHECK_CLKMGR_IO_MEAS_CTRL_EN_REG_OFFSET
#undef CHECK_CLKMGR_IO_DIV2_MEAS_CTRL_EN_REG_OFFSET
#undef CHECK_CLKMGR_IO_DIV4_MEAS_CTRL_EN_REG_OFFSET
#undef CHECK_CLKMGR_MAIN_MEAS_CTRL_EN_REG_OFFSET
#undef CHECK_CLKMGR_USB_MEAS_CTRL_EN_REG_OFFSET
#undef CHECK_IMPL
#undef CHECK
#undef IS_KIND_DEFINED
#undef IIF_0
#undef IIF_1
#undef IIF

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

dif_result_t dif_clkmgr_fatal_err_code_get_codes(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_fatal_err_codes_t *codes) {
  if (clkmgr == NULL || codes == NULL) {
    return kDifBadArg;
  }
  *codes =
      mmio_region_read32(clkmgr->base_addr, CLKMGR_FATAL_ERR_CODE_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_clkmgr_wait_for_ext_clk_switch(const dif_clkmgr_t *clkmgr) {
  if (clkmgr == NULL) {
    return kDifBadArg;
  }
  uint32_t ext_status;
  do {
    ext_status =
        mmio_region_read32(clkmgr->base_addr, CLKMGR_EXTCLK_STATUS_REG_OFFSET);
  } while (ext_status != kMultiBitBool4True);
  return kDifOk;
}
