// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/pinmux.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/common.h"

#define PINMUX0_BASE_ADDR 0x40070000

static void init_pinmux_reg(uint32_t reg, uint32_t size, uint32_t num_fields,
                            uint32_t mask, uint32_t start_v) {
  uint32_t reg_value = 0;
  uint32_t reg_offset = 0;

  for (uint32_t i = 0; i < NUM_MIO; ++i) {
    reg_value |= ((i + start_v) & mask) << (size * (i % num_fields));
    if ((i % num_fields) == (num_fields - 1)) {
      REG32(reg + reg_offset) = reg_value;
      reg_value = 0;
      reg_offset += 4;
    }
  }

  REG32(reg + reg_offset) = reg_value;
}

void pinmux_init(void) {
  // input: assign MIO0..MIO31 to GPIO0..GPIO31
  init_pinmux_reg(PINMUX_PERIPH_INSEL0(0), PINMUX_PERIPH_INSEL0_IN1_OFFSET,
                  32 / PINMUX_PERIPH_INSEL0_IN1_OFFSET,
                  PINMUX_PERIPH_INSEL0_IN0_MASK,
                  PINMUX_PERIPH_INSEL_IDX_OFFSET);

  // output: assign GPIO0..GPIO31 to MIO0..MIO31
  init_pinmux_reg(PINMUX_MIO_OUTSEL0(0), PINMUX_MIO_OUTSEL0_OUT1_OFFSET,
                  32 / PINMUX_MIO_OUTSEL0_OUT1_OFFSET,
                  PINMUX_MIO_OUTSEL0_OUT0_MASK,
                  PINMUX_PERIPH_OUTSEL_IDX_OFFSET);
}
