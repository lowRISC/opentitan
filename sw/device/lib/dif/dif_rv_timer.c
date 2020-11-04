// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rv_timer.h"

#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "rv_timer_regs.h"  // Generated.

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
  return kHartRegisterSpacing * hart + reg_offset;
}

dif_rv_timer_result_t dif_rv_timer_init(mmio_region_t base_addr,
                                        dif_rv_timer_config_t config,
                                        dif_rv_timer_t *timer_out) {
  if (timer_out == NULL || config.hart_count < 1 ||
      config.comparator_count < 1) {
    return kDifRvTimerBadArg;
  }

  timer_out->base_addr = base_addr;
  timer_out->config = config;

  return dif_rv_timer_reset(timer_out);
}

/**
 * A naive implementation of the Euclidean algorithm by repeated remainder.
 */
static uint64_t euclidean_gcd(uint64_t a, uint64_t b) {
  // TODO: The below 64-bit divide/remaider should be replaced with more
  // space-efficient polyfills at some point.
  while (b != 0) {
    uint64_t old_b = b;
    b = a % b;
    a = old_b;
  }

  return a;
}

dif_rv_timer_approximate_tick_params_result_t
dif_rv_timer_approximate_tick_params(uint64_t clock_freq, uint64_t counter_freq,
                                     dif_rv_timer_tick_params_t *out) {
  if (out == NULL) {
    return kDifRvTimerApproximateTickParamsBadArg;
  }

  // We have the following relation:
  //   counter_freq = clock_freq * (step / (prescale + 1))
  // We can solve for the individual parts as
  //   prescale = clock_freq / gcd - 1
  //   step = counter_freq / gcd
  uint64_t gcd = euclidean_gcd(clock_freq, counter_freq);

  uint64_t prescale = clock_freq / gcd - 1;
  uint64_t step = counter_freq / gcd;

  if (prescale > RV_TIMER_CFG0_PRESCALE_MASK ||
      step > RV_TIMER_CFG0_STEP_MASK) {
    return kDifRvTimerApproximateTickParamsUnrepresentable;
  }

  out->prescale = (uint16_t)prescale;
  out->tick_step = (uint8_t)step;

  return kDifRvTimerApproximateTickParamsOk;
}

dif_rv_timer_result_t dif_rv_timer_set_tick_params(
    const dif_rv_timer_t *timer, uint32_t hart_id,
    dif_rv_timer_tick_params_t params) {
  if (timer == NULL || hart_id >= timer->config.hart_count) {
    return kDifRvTimerBadArg;
  }

  uint32_t config_value = 0;
  config_value = bitfield_field32_write(
      config_value, RV_TIMER_CFG0_PRESCALE_FIELD, params.prescale);
  config_value = bitfield_field32_write(config_value, RV_TIMER_CFG0_STEP_FIELD,
                                        params.tick_step);
  mmio_region_write32(timer->base_addr,
                      reg_for_hart(hart_id, RV_TIMER_CFG0_REG_OFFSET),
                      config_value);

  return kDifRvTimerOk;
}

dif_rv_timer_result_t dif_rv_timer_counter_set_enabled(
    const dif_rv_timer_t *timer, uint32_t hart_id,
    dif_rv_timer_enabled_t state) {
  if (timer == NULL || hart_id >= timer->config.hart_count) {
    return kDifRvTimerBadArg;
  }

  switch (state) {
    case kDifRvTimerEnabled:
      mmio_region_nonatomic_set_bit32(timer->base_addr,
                                      RV_TIMER_CTRL_REG_OFFSET, hart_id);
      break;
    case kDifRvTimerDisabled:
      mmio_region_nonatomic_clear_bit32(timer->base_addr,
                                        RV_TIMER_CTRL_REG_OFFSET, hart_id);
      break;
    default:
      return kDifRvTimerBadArg;
  }

  return kDifRvTimerOk;
}

dif_rv_timer_result_t dif_rv_timer_counter_read(const dif_rv_timer_t *timer,
                                                uint32_t hart_id,
                                                uint64_t *out) {
  if (timer == NULL || out == NULL || hart_id >= timer->config.hart_count) {
    return kDifRvTimerBadArg;
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
      return kDifRvTimerOk;
    }
  }
}

dif_rv_timer_result_t dif_rv_timer_arm(const dif_rv_timer_t *timer,
                                       uint32_t hart_id, uint32_t comp_id,
                                       uint64_t threshold) {
  if (timer == NULL || hart_id >= timer->config.hart_count ||
      comp_id >= timer->config.comparator_count) {
    return kDifRvTimerBadArg;
  }

  uint32_t lower = threshold;
  uint32_t upper = threshold >> 32;

  ptrdiff_t lower_reg =
      reg_for_hart(hart_id, RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET) +
      (sizeof(uint64_t) * comp_id);
  ptrdiff_t upper_reg =
      reg_for_hart(hart_id, RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET) +
      (sizeof(uint64_t) * comp_id);

  // First, set the upper register to the largest value possible without setting
  // off the alarm; this way, we can set the lower register without setting
  // off the alarm.
  mmio_region_write32(timer->base_addr, upper_reg, UINT32_MAX);

  // This can't set off the alarm because of the value we set above.
  mmio_region_write32(timer->base_addr, lower_reg, lower);
  // Finish writing the new value; this may set off an alarm immediately.
  mmio_region_write32(timer->base_addr, upper_reg, upper);

  return kDifRvTimerOk;
}

/**
 * The number of comparators that the IP instantiation this library is compiled
 * against has. In other words, this tells us how far the statically known IRQ
 * register constants are from the start of the comparators, which influences
 * the computation in `irq_reg_for_hart()`.
 */
static const ptrdiff_t kComparatorsInReggenHeader =
    (RV_TIMER_INTR_ENABLE0_REG_OFFSET - RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET) /
    sizeof(uint64_t);

/**
 * Computes the appropriate register for a particular interrupt register, given
 * a number of comparators.
 *
 * Currently, all IRQ registers are placed after the comparator registers,
 * so the register offsets given by HW are not useable. The offsets need to be
 * compensated for by a factor of `kComparatorsInReggenHeader` double-words..
 *
 * We also do not handle the case when comparator_count > 32, which would cause
 * multiple interrupt registers to be generated.
 */
static ptrdiff_t irq_reg_for_hart(uint32_t hart_id, uint32_t comparators,
                                  ptrdiff_t reg_offset) {
  // Note that it is completely valid for this value to be negative: if this
  // library is built for hardware with a large number of compartors, this value
  // is necessarially negative when used with hardware with a small number of
  // comparators.
  ptrdiff_t extra_comparator_offset =
      sizeof(uint64_t) * (comparators - kComparatorsInReggenHeader);
  return reg_for_hart(hart_id, reg_offset) + extra_comparator_offset;
}

dif_rv_timer_result_t dif_rv_timer_irq_enable(const dif_rv_timer_t *timer,
                                              uint32_t hart_id,
                                              uint32_t comp_id,
                                              dif_rv_timer_enabled_t state) {
  if (timer == NULL || hart_id >= timer->config.hart_count ||
      comp_id >= timer->config.comparator_count) {
    return kDifRvTimerBadArg;
  }

  ptrdiff_t reg = irq_reg_for_hart(hart_id, timer->config.comparator_count,
                                   RV_TIMER_INTR_ENABLE0_REG_OFFSET);

  switch (state) {
    case kDifRvTimerEnabled:
      mmio_region_nonatomic_set_bit32(timer->base_addr, reg, comp_id);
      break;
    case kDifRvTimerDisabled:
      mmio_region_nonatomic_clear_bit32(timer->base_addr, reg, comp_id);
      break;
    default:
      return kDifRvTimerBadArg;
  }

  return kDifRvTimerOk;
}

dif_rv_timer_result_t dif_rv_timer_irq_get(const dif_rv_timer_t *timer,
                                           uint32_t hart_id, uint32_t comp_id,
                                           bool *flag_out) {
  if (timer == NULL || flag_out == NULL ||
      hart_id >= timer->config.hart_count ||
      comp_id >= timer->config.comparator_count) {
    return kDifRvTimerBadArg;
  }

  ptrdiff_t reg = irq_reg_for_hart(hart_id, timer->config.comparator_count,
                                   RV_TIMER_INTR_STATE0_REG_OFFSET);

  *flag_out = mmio_region_get_bit32(timer->base_addr, reg, comp_id);

  return kDifRvTimerOk;
}

dif_rv_timer_result_t dif_rv_timer_irq_clear(const dif_rv_timer_t *timer,
                                             uint32_t hart_id,
                                             uint32_t comp_id) {
  if (timer == NULL || hart_id >= timer->config.hart_count ||
      comp_id >= timer->config.comparator_count) {
    return kDifRvTimerBadArg;
  }

  ptrdiff_t reg = irq_reg_for_hart(hart_id, timer->config.comparator_count,
                                   RV_TIMER_INTR_STATE0_REG_OFFSET);

  mmio_region_write32(timer->base_addr, reg, 1 << comp_id);

  return kDifRvTimerOk;
}

dif_rv_timer_result_t dif_rv_timer_irq_disable(const dif_rv_timer_t *timer,
                                               uint32_t hart_id,
                                               uint32_t *state) {
  if (timer == NULL || hart_id >= timer->config.hart_count) {
    return kDifRvTimerBadArg;
  }

  ptrdiff_t reg = irq_reg_for_hart(hart_id, timer->config.comparator_count,
                                   RV_TIMER_INTR_ENABLE0_REG_OFFSET);

  if (state != NULL) {
    *state = mmio_region_read32(timer->base_addr, reg);
  }

  mmio_region_write32(timer->base_addr, reg, 0);

  return kDifRvTimerOk;
}

dif_rv_timer_result_t dif_rv_timer_irq_restore(const dif_rv_timer_t *timer,
                                               uint32_t hart_id,
                                               uint32_t state) {
  if (timer == NULL || hart_id >= timer->config.hart_count) {
    return kDifRvTimerBadArg;
  }

  ptrdiff_t reg = irq_reg_for_hart(hart_id, timer->config.comparator_count,
                                   RV_TIMER_INTR_ENABLE0_REG_OFFSET);

  mmio_region_write32(timer->base_addr, reg, state);

  return kDifRvTimerOk;
}

dif_rv_timer_result_t dif_rv_timer_irq_force(const dif_rv_timer_t *timer,
                                             uint32_t hart_id,
                                             uint32_t comp_id) {
  if (timer == NULL || hart_id >= timer->config.hart_count ||
      comp_id >= timer->config.comparator_count) {
    return kDifRvTimerBadArg;
  }

  ptrdiff_t reg = irq_reg_for_hart(hart_id, timer->config.comparator_count,
                                   RV_TIMER_INTR_TEST0_REG_OFFSET);

  mmio_region_write32(timer->base_addr, reg, 1 << comp_id);

  return kDifRvTimerOk;
}

dif_rv_timer_result_t dif_rv_timer_reset(const dif_rv_timer_t *timer) {
  if (timer == NULL) {
    return kDifRvTimerBadArg;
  }

  // Disable all counters.
  mmio_region_write32(timer->base_addr, RV_TIMER_CTRL_REG_OFFSET, 0x0);

  for (uint32_t hart_id = 0; hart_id < timer->config.hart_count; ++hart_id) {
    // Clear and disable all interrupts.
    ptrdiff_t irq_status =
        irq_reg_for_hart(hart_id, timer->config.comparator_count,
                         RV_TIMER_INTR_STATE0_REG_OFFSET);
    ptrdiff_t irq_enable =
        irq_reg_for_hart(hart_id, timer->config.comparator_count,
                         RV_TIMER_INTR_ENABLE0_REG_OFFSET);
    mmio_region_write32(timer->base_addr, irq_enable, 0x0);
    mmio_region_write32(timer->base_addr, irq_status, UINT32_MAX);

    // Reset all comparators to their default all-ones state.
    for (uint32_t comp_id = 0; comp_id < timer->config.comparator_count;
         ++comp_id) {
      dif_rv_timer_result_t error =
          dif_rv_timer_arm(timer, hart_id, comp_id, UINT64_MAX);
      if (error != kDifRvTimerOk) {
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

  return kDifRvTimerOk;
}
