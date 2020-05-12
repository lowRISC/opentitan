// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_gpio.h"

#include "gpio_regs.h"  // Generated.
#include "sw/device/lib/common.h"

/**
 * Gives the mask that corresponds to the given bit index.
 *
 * @param index Bit index in a 32-bit register.
 */
static uint32_t index_to_mask(uint32_t index) { return 1u << index; }

/**
 * Perform a masked write to a GPIO register.
 *
 * The GPIO device provides masked bit-level atomic writes to its DIRECT_OUT
 * and DIRECT_OE registers. This allows software to modify half of the bits
 * at a time without requiring a read-modify-write. Note that depending on the
 * value of the `mask`, this function may perform two writes.
 *
 * For instance, DIRECT_OUT's lower and upper halves can be modified by
 * MASKED_OUT_LOWER and MASKED_OUT_UPPER, respectively. Upper half of
 * MASKED_OUT_LOWER is the mask that determines which bits in the lower half of
 * DIRECT_OUT will be modified, while lower half of MASKED_OUT_LOWER determines
 * their values. MASKED_OUT_UPPER behaves in the same way for modifying the
 * upper half of DIRECT_OUT.
 *
 * @param gpio GPIO instance.
 * @param reg_lower_offset Offset of the masked access register that corresponds
 * to the lower half of the actual register.
 * @param reg_upper_offset Offset of the masked access register that corresponds
 * to the upper half of the actual register.
 * @param mask Mask that identifies the bits to write to.
 * @param val Value to write.
 */
static void gpio_masked_write(const dif_gpio_t *gpio, uint32_t reg_lower_offset,
                              uint32_t reg_upper_offset, uint32_t mask,
                              uint32_t val) {
  const uint32_t mask_lower_half = mask & 0x0000FFFFu;
  const uint32_t mask_upper_half = mask & 0xFFFF0000u;
  if (mask_lower_half != 0) {
    mmio_region_write32(gpio->base_addr, reg_lower_offset,
                        (mask_lower_half << 16) | (val & 0x0000FFFFu));
  }
  if (mask_upper_half != 0) {
    mmio_region_write32(gpio->base_addr, reg_upper_offset,
                        mask_upper_half | ((val & 0xFFFF0000u) >> 16));
  }
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
 * See also `gpio_masked_write()`.
 *
 * @param gpio GPIO instance.
 * @param reg_lower_offset Offset of the masked access register that corresponds
 * to the lower half of the actual register.
 * @param reg_upper_offset Offset of the masked access register that corresponds
 * to the upper half of the actual register.
 * @param index Zero-based index of the bit to write to.
 * @param val Value to write.
 */
static void gpio_masked_bit_write(const dif_gpio_t *gpio,
                                  uint32_t reg_lower_offset,
                                  uint32_t reg_upper_offset, uint32_t index,
                                  bool val) {
  // Write to reg_lower_offset if the bit is in the lower half, write to
  // reg_upper_offset otherwise.
  const ptrdiff_t offset = (index < 16) ? reg_lower_offset : reg_upper_offset;
  // Since masked access writes to half of a register, index mod 16 gives the
  // index of the bit in the half-word mask.
  const uint32_t mask = index_to_mask(index % 16);
  mmio_region_write32(gpio->base_addr, offset,
                      (mask << 16) | (val ? mask : 0u));
}

dif_gpio_result_t dif_gpio_init(const dif_gpio_config_t *config,
                                dif_gpio_t *gpio) {
  if (config == NULL || gpio == NULL) {
    return kDifGpioBadArg;
  }

  // Save internal state in the given `dif_gpio_t` instance.
  gpio->base_addr = config->base_addr;
  // Reset the GPIO device at the given `base_addr`.
  dif_gpio_reset(gpio);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_reset(const dif_gpio_t *gpio) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  mmio_region_write32(gpio->base_addr, GPIO_INTR_ENABLE_REG_OFFSET, 0);
  mmio_region_write32(gpio->base_addr, GPIO_DIRECT_OE_REG_OFFSET, 0);
  mmio_region_write32(gpio->base_addr, GPIO_DIRECT_OUT_REG_OFFSET, 0);
  mmio_region_write32(gpio->base_addr, GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, 0);
  mmio_region_write32(gpio->base_addr, GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, 0);
  mmio_region_write32(gpio->base_addr, GPIO_INTR_CTRL_EN_LVLHIGH_REG_OFFSET, 0);
  mmio_region_write32(gpio->base_addr, GPIO_INTR_CTRL_EN_LVLLOW_REG_OFFSET, 0);
  mmio_region_write32(gpio->base_addr, GPIO_CTRL_EN_INPUT_FILTER_REG_OFFSET, 0);
  // Also clear all pending interrupts
  mmio_region_write32(gpio->base_addr, GPIO_INTR_STATE_REG_OFFSET, 0xFFFFFFFFu);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_all_read(const dif_gpio_t *gpio,
                                    uint32_t *pin_values) {
  if (gpio == NULL || pin_values == NULL) {
    return kDifGpioBadArg;
  }

  *pin_values = mmio_region_read32(gpio->base_addr, GPIO_DATA_IN_REG_OFFSET);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_pin_read(const dif_gpio_t *gpio, uint32_t index,
                                    bool *pin_value) {
  if (gpio == NULL || pin_value == NULL) {
    return kDifGpioBadArg;
  }

  *pin_value =
      mmio_region_get_bit32(gpio->base_addr, GPIO_DATA_IN_REG_OFFSET, index);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_all_write(const dif_gpio_t *gpio, uint32_t val) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  mmio_region_write32(gpio->base_addr, GPIO_DIRECT_OUT_REG_OFFSET, val);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_pin_write(const dif_gpio_t *gpio, uint32_t index,
                                     bool val) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  gpio_masked_bit_write(gpio, GPIO_MASKED_OUT_LOWER_REG_OFFSET,
                        GPIO_MASKED_OUT_UPPER_REG_OFFSET, index, val);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_masked_write(const dif_gpio_t *gpio, uint32_t mask,
                                        uint32_t val) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  gpio_masked_write(gpio, GPIO_MASKED_OUT_LOWER_REG_OFFSET,
                    GPIO_MASKED_OUT_UPPER_REG_OFFSET, mask, val);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_output_mode_all_set(const dif_gpio_t *gpio,
                                               uint32_t val) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  mmio_region_write32(gpio->base_addr, GPIO_DIRECT_OE_REG_OFFSET, val);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_output_mode_pin_set(const dif_gpio_t *gpio,
                                               uint32_t index, bool val) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  gpio_masked_bit_write(gpio, GPIO_MASKED_OE_LOWER_REG_OFFSET,
                        GPIO_MASKED_OE_UPPER_REG_OFFSET, index, val);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_output_mode_masked_set(const dif_gpio_t *gpio,
                                                  uint32_t mask, uint32_t val) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  gpio_masked_write(gpio, GPIO_MASKED_OE_LOWER_REG_OFFSET,
                    GPIO_MASKED_OE_UPPER_REG_OFFSET, mask, val);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_irq_pin_test(const dif_gpio_t *gpio,
                                        uint32_t index) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  mmio_region_write32(gpio->base_addr, GPIO_INTR_TEST_REG_OFFSET,
                      index_to_mask(index));

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_irq_all_read(const dif_gpio_t *gpio,
                                        uint32_t *interrupt_states) {
  if (gpio == NULL || interrupt_states == NULL) {
    return kDifGpioBadArg;
  }

  *interrupt_states =
      mmio_region_read32(gpio->base_addr, GPIO_INTR_STATE_REG_OFFSET);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_irq_pin_read(const dif_gpio_t *gpio, uint32_t index,
                                        bool *interrupt_state) {
  if (gpio == NULL || interrupt_state == NULL) {
    return kDifGpioBadArg;
  }

  *interrupt_state =
      mmio_region_get_bit32(gpio->base_addr, GPIO_INTR_STATE_REG_OFFSET, index);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_irq_pin_clear(const dif_gpio_t *gpio,
                                         uint32_t index) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  mmio_region_write32(gpio->base_addr, GPIO_INTR_STATE_REG_OFFSET,
                      index_to_mask(index));

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_input_noise_filter_masked_enable(
    const dif_gpio_t *gpio, uint32_t mask) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  mmio_region_nonatomic_set_mask32(
      gpio->base_addr, GPIO_CTRL_EN_INPUT_FILTER_REG_OFFSET, mask, 0);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_input_noise_filter_masked_disable(
    const dif_gpio_t *gpio, uint32_t mask) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  mmio_region_nonatomic_clear_mask32(
      gpio->base_addr, GPIO_CTRL_EN_INPUT_FILTER_REG_OFFSET, mask, 0);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_irq_masked_enable(const dif_gpio_t *gpio,
                                             uint32_t mask) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  mmio_region_nonatomic_set_mask32(gpio->base_addr, GPIO_INTR_ENABLE_REG_OFFSET,
                                   mask, 0);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_irq_masked_disable(const dif_gpio_t *gpio,
                                              uint32_t mask) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  mmio_region_nonatomic_clear_mask32(gpio->base_addr,
                                     GPIO_INTR_ENABLE_REG_OFFSET, mask, 0);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_irq_trigger_masked_disable(const dif_gpio_t *gpio,
                                                      uint32_t mask) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  // Disable all interrupt triggers for the given mask
  mmio_region_nonatomic_clear_mask32(
      gpio->base_addr, GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, mask, 0);
  mmio_region_nonatomic_clear_mask32(
      gpio->base_addr, GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, mask, 0);
  mmio_region_nonatomic_clear_mask32(
      gpio->base_addr, GPIO_INTR_CTRL_EN_LVLHIGH_REG_OFFSET, mask, 0);
  mmio_region_nonatomic_clear_mask32(
      gpio->base_addr, GPIO_INTR_CTRL_EN_LVLLOW_REG_OFFSET, mask, 0);

  return kDifGpioOk;
}

dif_gpio_result_t dif_gpio_irq_trigger_masked_config(const dif_gpio_t *gpio,
                                                     uint32_t mask,
                                                     dif_gpio_irq_t config) {
  if (gpio == NULL) {
    return kDifGpioBadArg;
  }

  // Disable all interrupt triggers for the given mask
  dif_gpio_irq_trigger_masked_disable(gpio, mask);

  switch (config) {
    case kDifGpioIrqEdgeRising:
      mmio_region_nonatomic_set_mask32(
          gpio->base_addr, GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, mask, 0);
      break;
    case kDifGpioIrqEdgeFalling:
      mmio_region_nonatomic_set_mask32(
          gpio->base_addr, GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, mask, 0);
      break;
    case kDifGpioIrqLevelLow:
      mmio_region_nonatomic_set_mask32(
          gpio->base_addr, GPIO_INTR_CTRL_EN_LVLLOW_REG_OFFSET, mask, 0);
      break;
    case kDifGpioIrqLevelHigh:
      mmio_region_nonatomic_set_mask32(
          gpio->base_addr, GPIO_INTR_CTRL_EN_LVLHIGH_REG_OFFSET, mask, 0);
      break;
    case kDifGpioIrqEdgeRisingFalling:
      mmio_region_nonatomic_set_mask32(
          gpio->base_addr, GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, mask, 0);
      mmio_region_nonatomic_set_mask32(
          gpio->base_addr, GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, mask, 0);
      break;
    case kDifGpioIrqEdgeRisingLevelLow:
      mmio_region_nonatomic_set_mask32(
          gpio->base_addr, GPIO_INTR_CTRL_EN_RISING_REG_OFFSET, mask, 0);
      mmio_region_nonatomic_set_mask32(
          gpio->base_addr, GPIO_INTR_CTRL_EN_LVLLOW_REG_OFFSET, mask, 0);
      break;
    case kDifGpioIrqEdgeFallingLevelHigh:
      mmio_region_nonatomic_set_mask32(
          gpio->base_addr, GPIO_INTR_CTRL_EN_FALLING_REG_OFFSET, mask, 0);
      mmio_region_nonatomic_set_mask32(
          gpio->base_addr, GPIO_INTR_CTRL_EN_LVLHIGH_REG_OFFSET, mask, 0);
      break;
    default:
      return kDifGpioError;
  }

  return kDifGpioOk;
}
