// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/pinmux.h"

#include "sw/device/lib/base/mmio.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#include "pinmux_regs.h"  // Generated.

#define PINMUX0_BASE_ADDR TOP_EARLGREY_PINMUX_BASE_ADDR

static void init_pinmux_reg(uint32_t reg, uint32_t size, uint32_t num_fields,
                            uint32_t mask, uint32_t start_v) {
  mmio_region_t reg32 = mmio_region_from_addr(reg);
  uint32_t reg_value = 0;
  uint32_t reg_offset = 0;

  for (uint32_t i = 0; i < NUM_MIO; ++i) {
    reg_value |= ((i + start_v) & mask) << (size * (i % num_fields));
    if ((i % num_fields) == (num_fields - 1)) {
      mmio_region_write32(reg32, reg_offset, reg_value);
      reg_value = 0;
      reg_offset += 4;
    }
  }

  mmio_region_write32(reg32, reg_offset, reg_value);
}

void pinmux_init(void) {
  // input: assign MIO0..MIO31 to GPIO0..GPIO31
  init_pinmux_reg(
      PINMUX0_BASE_ADDR + PINMUX_PERIPH_INSEL_0_REG_OFFSET,
      PINMUX_PERIPH_INSEL_0_IN_1_OFFSET, 32 / PINMUX_PERIPH_INSEL_0_IN_1_OFFSET,
      PINMUX_PERIPH_INSEL_0_IN_0_MASK, PINMUX_PERIPH_INSEL_IDX_OFFSET);

  // output: assign GPIO0..GPIO31 to MIO0..MIO31
  init_pinmux_reg(
      PINMUX0_BASE_ADDR + PINMUX_MIO_OUTSEL_0_REG_OFFSET,
      PINMUX_MIO_OUTSEL_0_OUT_1_OFFSET, 32 / PINMUX_MIO_OUTSEL_0_OUT_1_OFFSET,
      PINMUX_MIO_OUTSEL_0_OUT_0_MASK, PINMUX_PERIPH_OUTSEL_IDX_OFFSET);
}
