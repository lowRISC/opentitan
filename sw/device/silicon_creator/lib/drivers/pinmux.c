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

enum {
  /**
   * Base address of the pinmux registers.
   */
  kBase = TOP_EARLGREY_PINMUX_AON_BASE_ADDR,
};

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
static const pinmux_input_t kInputUart0 = {
    .periph = kTopEarlgreyPinmuxPeripheralInUart0Rx,
    .pad = kTopEarlgreyPinmuxInselIoc3,
};

/**
 * UART TX pin.
 */
static const pinmux_output_t kOutputUart0 = {
    .pad = kTopEarlgreyPinmuxMioOutIoc4,
    .periph = kTopEarlgreyPinmuxOutselUart0Tx,
};

/**
 * SW strap pins.
 *
 */
static const pinmux_input_t kInputSwStrap0 = {
    .periph = kTopEarlgreyPinmuxPeripheralInGpioGpio22,
    .pad = kTopEarlgreyPinmuxInselIoc0,
};
static const pinmux_input_t kInputSwStrap1 = {
    .periph = kTopEarlgreyPinmuxPeripheralInGpioGpio23,
    .pad = kTopEarlgreyPinmuxInselIoc1,
};
static const pinmux_input_t kInputSwStrap2 = {
    .periph = kTopEarlgreyPinmuxPeripheralInGpioGpio24,
    .pad = kTopEarlgreyPinmuxInselIoc2,
};

/**
 * Sets the input pad for the specified peripheral input.
 *
 * @param input A peripheral input and MIO pad to link it to.
 */
static void configure_input(pinmux_input_t input) {
  abs_mmio_write32(kBase + PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET +
                       input.periph * sizeof(uint32_t),
                   input.pad);
}

/**
 * Enables pull-down for the specified pad.
 *
 * @param pad A MIO pad.
 */
static void enable_pull_down(top_earlgrey_pinmux_insel_t pad) {
  uint32_t reg =
      bitfield_bit32_write(0, PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT, true);
  abs_mmio_write32(
      kBase + PINMUX_MIO_PAD_ATTR_0_REG_OFFSET + pad * sizeof(uint32_t), reg);
}

/**
 * Configures the given pin as input and enables the internal pull-down.
 *
 * We enable internal pull-downs since we expect strong pull-ups on the strap
 * pins.
 *
 * @param input A peripheral input and MIO pad to link it to.
 */
static void configure_strap_pin(pinmux_input_t input) {
  configure_input(input);
  enable_pull_down(input.pad);
}

/**
 * Sets the peripheral output for each specified output pad.
 *
 * @param output An MIO pad and a peripheral output to link it to.
 */
static void configure_output(pinmux_output_t output) {
  abs_mmio_write32(
      kBase + PINMUX_MIO_OUTSEL_0_REG_OFFSET + output.pad * sizeof(uint32_t),
      output.periph);
}

void pinmux_init(void) {
  uint32_t bootstrap_en = otp_read32(OTP_CTRL_PARAM_ROM_BOOTSTRAP_EN_OFFSET);
  if (launder32(bootstrap_en) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(bootstrap_en, kHardenedBoolTrue);
    configure_strap_pin(kInputSwStrap0);
    configure_strap_pin(kInputSwStrap1);
    configure_strap_pin(kInputSwStrap2);
  }

  configure_input(kInputUart0);
  configure_output(kOutputUart0);
}
