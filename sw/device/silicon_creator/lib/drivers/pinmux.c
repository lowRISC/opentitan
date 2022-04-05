// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/pinmux.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "pinmux_regs.h"

/**
 * A peripheral input and MIO pad to link it to.
 */
typedef struct pinmux_input {
  top_earlgrey_pinmux_peripheral_in_t periph;
  top_earlgrey_pinmux_insel_t pad;
} pinmux_input_t;

/**
 * An MIO pad and a peripheral output to link it to.
 */
typedef struct pinmux_output {
  top_earlgrey_pinmux_mio_out_t pad;
  top_earlgrey_pinmux_outsel_t periph;
} pinmux_output_t;

/**
 * UART RX pin.
 */
static const pinmux_input_t kInputUart = {
    .periph = kTopEarlgreyPinmuxPeripheralInUart0Rx,
    .pad = kTopEarlgreyPinmuxInselIoc3,
};

/**
 * Bootstrap pin.
 *
 * TODO(#11934): The actual chip will have 3 strapping pins that should be
 * configured as inputs.
 */
static const pinmux_input_t kInputBootstrap = {
    .periph = kTopEarlgreyPinmuxPeripheralInGpioGpio17,
    .pad = kTopEarlgreyPinmuxInselIob8,
};

/**
 * UART TX pin.
 */
static const pinmux_output_t kOutputUart = {
    .pad = kTopEarlgreyPinmuxMioOutIoc4,
    .periph = kTopEarlgreyPinmuxOutselUart0Tx,
};

/**
 * Sets the input pad for the specified peripheral input.
 *
 * @param input A peripheral input and MIO pad to link it to.
 */
static void configure_input(pinmux_input_t input) {
  abs_mmio_write32(TOP_EARLGREY_PINMUX_AON_BASE_ADDR +
                       PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET +
                       input.periph * sizeof(uint32_t),
                   input.pad);
}

/**
 * Sets the peripheral output for each specified output pad.
 *
 * @param output An MIO pad and a peripheral output to link it to.
 */
static void configure_output(pinmux_output_t output) {
  abs_mmio_write32(TOP_EARLGREY_PINMUX_AON_BASE_ADDR +
                       PINMUX_MIO_OUTSEL_0_REG_OFFSET +
                       output.pad * sizeof(uint32_t),
                   output.periph);
}

void pinmux_init(void) {
  uint32_t bootstrap_en = otp_read32(OTP_CTRL_PARAM_ROM_BOOTSTRAP_EN_OFFSET);
  if (launder32(bootstrap_en) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(bootstrap_en, kHardenedBoolTrue);
    configure_input(kInputBootstrap);
  }

  configure_input(kInputUart);
  configure_output(kOutputUart);
}
