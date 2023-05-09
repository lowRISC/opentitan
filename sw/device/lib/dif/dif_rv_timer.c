// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rv_timer.h"

#include <assert.h>
#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/math.h"

#include "rv_timer_regs.h"  // Generated.

static_assert(RV_TIMER_PARAM_N_HARTS > 0,
              "RV Timer must support at least one hart.");
static_assert(RV_TIMER_PARAM_N_TIMERS > 0,
              "RV Timer must support at least one timer per hart.");

/**
 * The factor to multiply by to find the registers for the Nth hart.
 *
 * Given the hart N (zero-indexed), its timer registers are found at
 * the memory address
 *   base_addr + ((N + 1) * kHartRegisterSpacing)
 *
 * The function `reg_for_hart()` can be used to compute the offset from
 * `base` for the Nth hart for a particular repeated hardware register.
 */
static const ptrdiff_t kHartRegisterSpacing = 0x100;

/**
 * Returns the MMIO offset for the register `reg_offset`, for the zero-indexed
 * `hart`.
 */
static ptrdiff_t reg_for_hart(uint32_t hart, ptrdiff_t reg_offset) {
  return kHartRegisterSpacing * (ptrdiff_t)hart + reg_offset;
}

/**
 * A naive implementation of the Euclidean algorithm by repeated remainder.
 */
static uint64_t euclidean_gcd(uint64_t a, uint64_t b) {
  while (b != 0) {
    uint64_t old_b = b;
    udiv64_slow(a, b, &b);
    a = old_b;
  }

  return a;
}

dif_result_t dif_rv_timer_approximate_tick_params(
    uint64_t clock_freq, uint64_t counter_freq,
    dif_rv_timer_tick_params_t *out) {
  if (out == NULL) {
    return kDifBadArg;
  }

  // We have the following relation:
  //   counter_freq = clock_freq * (step / (prescale + 1))
  // We can solve for the individual parts as
  //   prescale = clock_freq / gcd - 1
  //   step = counter_freq / gcd
  uint64_t gcd = euclidean_gcd(clock_freq, counter_freq);

  uint64_t prescale = udiv64_slow(clock_freq, gcd, NULL) - 1;
  uint64_t step = udiv64_slow(counter_freq, gcd, NULL);

  if (prescale > RV_TIMER_CFG0_PRESCALE_MASK ||
      step > RV_TIMER_CFG0_STEP_MASK) {
    return kDifBadArg;
  }

  out->prescale = (uint16_t)prescale;
  out->tick_step = (uint8_t)step;

  return kDifOk;
}

dif_result_t dif_rv_timer_set_tick_params(const dif_rv_timer_t *timer,
                                          uint32_t hart_id,
                                          dif_rv_timer_tick_params_t params) {
  if (timer == NULL || hart_id >= RV_TIMER_PARAM_N_HARTS) {
    return kDifBadArg;
  }

  uint32_t config_value = 0;
  config_value = bitfield_field32_write(
      config_value, RV_TIMER_CFG0_PRESCALE_FIELD, params.prescale);
  config_value = bitfield_field32_write(config_value, RV_TIMER_CFG0_STEP_FIELD,
                                        params.tick_step);
  mmio_region_write32(timer->base_addr,
                      reg_for_hart(hart_id, RV_TIMER_CFG0_REG_OFFSET),
                      config_value);

  return kDifOk;
}

dif_result_t dif_rv_timer_counter_set_enabled(const dif_rv_timer_t *timer,
                                              uint32_t hart_id,
                                              dif_toggle_t state) {
  if (timer == NULL || hart_id >= RV_TIMER_PARAM_N_HARTS) {
    return kDifBadArg;
  }

  switch (state) {
    case kDifToggleEnabled:
      mmio_region_nonatomic_set_bit32(timer->base_addr,
                                      RV_TIMER_CTRL_REG_OFFSET, hart_id);
      break;
    case kDifToggleDisabled:
      mmio_region_nonatomic_clear_bit32(timer->base_addr,
                                        RV_TIMER_CTRL_REG_OFFSET, hart_id);
      break;
    default:
      return kDifBadArg;
  }

  return kDifOk;
}

dif_result_t dif_rv_timer_counter_read(const dif_rv_timer_t *timer,
                                       uint32_t hart_id, uint64_t *out) {
  if (timer == NULL || out == NULL || hart_id >= RV_TIMER_PARAM_N_HARTS) {
    return kDifBadArg;
  }

  // We need to read a monotonically increasing, volatile uint64. To do so,
  // we first read the upper half, then the lower half. Then, we check if the
  // upper half reads the same value again. If it doesn't, it means that the
  // lower half overflowed and we need to re-take the measurement.
  while (true) {
    uint32_t upper = mmio_region_read32(
        timer->base_addr,
        reg_for_hart(hart_id, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET));
    uint32_t lower = mmio_region_read32(
        timer->base_addr,
        reg_for_hart(hart_id, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET));

    uint32_t overflow_check = mmio_region_read32(
        timer->base_addr,
        reg_for_hart(hart_id, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET));

    if (upper == overflow_check) {
      *out = (((uint64_t)upper) << 32) | lower;
      return kDifOk;
    }
  }
}

dif_result_t dif_rv_timer_counter_write(const dif_rv_timer_t *timer,
                                        uint32_t hart_id, uint64_t count) {
  if (timer == NULL || hart_id >= RV_TIMER_PARAM_N_HARTS) {
    return kDifBadArg;
  }

  // Disable the counter.
  uint32_t ctrl_reg =
      mmio_region_read32(timer->base_addr, RV_TIMER_CTRL_REG_OFFSET);
  uint32_t ctrl_reg_cleared = bitfield_bit32_write(ctrl_reg, hart_id, false);
  mmio_region_write32(timer->base_addr, RV_TIMER_CTRL_REG_OFFSET,
                      ctrl_reg_cleared);

  // Write the new count.
  uint32_t lower_count = (uint32_t)count;
  uint32_t upper_count = count >> 32;
  mmio_region_write32(timer->base_addr,
                      reg_for_hart(hart_id, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET),
                      lower_count);
  mmio_region_write32(timer->base_addr,
                      reg_for_hart(hart_id, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET),
                      upper_count);

  // Re-enable the counter (if it was previously enabled).
  mmio_region_write32(timer->base_addr, RV_TIMER_CTRL_REG_OFFSET, ctrl_reg);

  return kDifOk;
}

dif_result_t dif_rv_timer_arm(const dif_rv_timer_t *timer, uint32_t hart_id,
                              uint32_t comp_id, uint64_t threshold) {
  if (timer == NULL || hart_id >= RV_TIMER_PARAM_N_HARTS ||
      comp_id >= RV_TIMER_PARAM_N_TIMERS) {
    return kDifBadArg;
  }

  uint32_t lower = (uint32_t)threshold;
  uint32_t upper = threshold >> 32;

  ptrdiff_t lower_reg =
      reg_for_hart(hart_id, RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET) +
      (ptrdiff_t)(sizeof(uint64_t) * comp_id);
  ptrdiff_t upper_reg =
      reg_for_hart(hart_id, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET) +
      (ptrdiff_t)(sizeof(uint64_t) * comp_id);

  // First, set the upper register to the largest value possible without setting
  // off the alarm; this way, we can set the lower register without setting
  // off the alarm.
  mmio_region_write32(timer->base_addr, upper_reg, UINT32_MAX);

  // This can't set off the alarm because of the value we set above.
  mmio_region_write32(timer->base_addr, lower_reg, lower);
  // Finish writing the new value; this may set off an alarm immediately.
  mmio_region_write32(timer->base_addr, upper_reg, upper);

  return kDifOk;
}

dif_result_t dif_rv_timer_reset(const dif_rv_timer_t *timer) {
  if (timer == NULL) {
    return kDifBadArg;
  }

  // Disable all counters.
  mmio_region_write32(timer->base_addr, RV_TIMER_CTRL_REG_OFFSET, 0x0);

  for (uint32_t hart_id = 0; hart_id < RV_TIMER_PARAM_N_HARTS; ++hart_id) {
    // Clear and disable all interrupts.
    ptrdiff_t irq_status =
        reg_for_hart(hart_id, RV_TIMER_INTR_STATE0_REG_OFFSET);
    ptrdiff_t irq_enable =
        reg_for_hart(hart_id, RV_TIMER_INTR_ENABLE0_REG_OFFSET);
    mmio_region_write32(timer->base_addr, irq_enable, 0x0);
    mmio_region_write32(timer->base_addr, irq_status, UINT32_MAX);

    // Reset all comparators to their default all-ones state.
    for (uint32_t comp_id = 0; comp_id < RV_TIMER_PARAM_N_TIMERS; ++comp_id) {
      dif_result_t error =
          dif_rv_timer_arm(timer, hart_id, comp_id, UINT64_MAX);
      if (error != kDifOk) {
        return error;
      }
    }

    // Reset the counter to zero.
    mmio_region_write32(
        timer->base_addr,
        reg_for_hart(hart_id, RV_TIMER_TIMER_V_LOWER0_REG_OFFSET), 0x0);
    mmio_region_write32(
        timer->base_addr,
        reg_for_hart(hart_id, RV_TIMER_TIMER_V_UPPER0_REG_OFFSET), 0x0);
  }

  return kDifOk;
}
