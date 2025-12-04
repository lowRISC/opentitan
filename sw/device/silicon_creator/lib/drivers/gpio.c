// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/gpio.h"

#include <stddef.h>

#include "hw/top/dt/dt_gpio.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top/gpio_regs.h"  // Generated.

static_assert(kGpioNumPins <= 32,
              "This implementation assumes that the number of pins is less "
              "than or equal to 32");

static inline uint32_t gpio_base_addr(void) {
  return dt_gpio_primary_reg_block(kDtGpio);
}

/**
 * Perform a masked write to a single bit of a GPIO register.
 *
 * The GPIO device provides masked bit-level atomic writes to its DIRECT_OUT
 * and DIRECT_OE registers. This allows software to modify half of the bits
 * at a time without requiring a read-modify-write. This function is guaranteed
 * to perform only one write since it never needs to access both halves of a
 * register.
 *
 * @param reg_lower_offset Offset of the masked access register that corresponds
 * to the lower half of the actual register.
 * @param reg_upper_offset Offset of the masked access register that corresponds
 * to the upper half of the actual register.
 * @param index Zero-based index of the bit to write to.
 * @param val Value to write.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t gpio_masked_bit_write(ptrdiff_t reg_lower_offset,
                                         ptrdiff_t reg_upper_offset,
                                         uint32_t index, bool val) {
  if (index >= kGpioNumPins) {
    return kErrorGpioInvalidPin;
  }

  // Write to reg_lower_offset if the bit is in the lower half, write to
  // reg_upper_offset otherwise.
  const ptrdiff_t offset = (index < 16) ? reg_lower_offset : reg_upper_offset;
  // Since masked access writes to half of a register, index mod 16 gives the
  // index of the bit in the half-word mask.
  const uint32_t mask = 1u << (index % 16);
  abs_mmio_write32(gpio_base_addr() + (uint32_t)offset,
                   (mask << 16) | (val ? mask : 0u));

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
rom_error_t gpio_read(gpio_pin_t pin, bool *state) {
  if (state == NULL || pin >= kGpioNumPins) {
    return kErrorGpioInvalidPin;
  }

  *state = bitfield_bit32_read(
      abs_mmio_read32(gpio_base_addr() + GPIO_DATA_IN_REG_OFFSET), pin);

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
rom_error_t gpio_write(gpio_pin_t pin, bool state) {
  return gpio_masked_bit_write(GPIO_MASKED_OUT_LOWER_REG_OFFSET,
                               GPIO_MASKED_OUT_UPPER_REG_OFFSET, pin, state);
}

OT_WARN_UNUSED_RESULT
rom_error_t gpio_set_output_mode(gpio_pin_t pin, bool output) {
  return gpio_masked_bit_write(GPIO_MASKED_OE_LOWER_REG_OFFSET,
                               GPIO_MASKED_OE_UPPER_REG_OFFSET, pin, output);
}
