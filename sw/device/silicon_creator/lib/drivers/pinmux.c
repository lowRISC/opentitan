// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/pinmux.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pinmux_regs.h"  // Generated.

/**
 * A peripheral input and MIO pad to link it to.
 */
typedef struct pinmux_input {
  top_earlgrey_pinmux_peripheral_in_t periph;
  top_earlgrey_pinmux_insel_t pad;
} pinmux_input_t;

/**
 * Peripheral input to MIO pad mappings.
 */
static const pinmux_input_t kPinmuxInputs[] = {
    /**
     * Bootstrap pin.
     */
    {
        .periph = kTopEarlgreyPinmuxPeripheralInGpioGpio17,
        .pad = kTopEarlgreyPinmuxInselIob8,
    },
    /**
     * UART
     */
    {
        .periph = kTopEarlgreyPinmuxPeripheralInUart0Rx,
        .pad = kTopEarlgreyPinmuxInselIoc10,
    },
};

/**
 * An MIO pad and a peripheral output to link it to.
 */
typedef struct pinmux_output {
  top_earlgrey_pinmux_mio_out_t pad;
  top_earlgrey_pinmux_outsel_t periph;
} pinmux_output_t;

/**
 * MIO pad to peripheral output mappings.
 */
static const pinmux_output_t kPinmuxOutputs[] = {
    /**
     * UART
     */
    {.pad = kTopEarlgreyPinmuxMioOutIoc11,
     .periph = kTopEarlgreyPinmuxOutselUart0Tx},
};

void pinmux_init(void) {
  // Set the input pad for each specified peripheral input.
  const uint32_t kInputBase =
      TOP_EARLGREY_PINMUX_AON_BASE_ADDR + PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET;
  for (uint32_t i = 0; i < ARRAYSIZE(kPinmuxInputs); ++i) {
    uint32_t reg = kPinmuxInputs[i].periph * sizeof(uint32_t);
    uint32_t val = kPinmuxInputs[i].pad;
    abs_mmio_write32(kInputBase + reg, val);
  }

  // Set the peripheral output for each specified output pad.
  const uint32_t kOutputBase =
      TOP_EARLGREY_PINMUX_AON_BASE_ADDR + PINMUX_MIO_OUTSEL_0_REG_OFFSET;
  for (uint32_t i = 0; i < ARRAYSIZE(kPinmuxOutputs); ++i) {
    uint32_t reg = kPinmuxOutputs[i].pad * sizeof(uint32_t);
    uint32_t val = kPinmuxOutputs[i].periph;
    abs_mmio_write32(kOutputBase + reg, val);
  }
}
