// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/pinmux.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
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
  top_earlgrey_pinmux_insel_t insel;
  top_earlgrey_muxed_pads_t pad;
} pinmux_input_t;

/**
 * An MIO pad and a peripheral output to link it to.
 */
typedef struct pinmux_output {
  top_earlgrey_pinmux_mio_out_t mio;
  top_earlgrey_pinmux_outsel_t outsel;
  top_earlgrey_muxed_pads_t pad;
} pinmux_output_t;

/**
 * UART RX pin.
 */
static const pinmux_input_t kInputUart0 = {
    .periph = kTopEarlgreyPinmuxPeripheralInUart0Rx,
    .insel = kTopEarlgreyPinmuxInselIoc3,
    .pad = kTopEarlgreyMuxedPadsIoc3,
};

/**
 * UART TX pin.
 */
static const pinmux_output_t kOutputUart0 = {
    .mio = kTopEarlgreyPinmuxMioOutIoc4,
    .outsel = kTopEarlgreyPinmuxOutselUart0Tx,
    .pad = kTopEarlgreyMuxedPadsIoc4,
};

/**
 * SW strap pins.
 */
#define PINMUX_ASSERT_EQ_(a, b) \
  static_assert((a) == (b), "Unexpected software strap configuration.")

PINMUX_ASSERT_EQ_(SW_STRAP_0_PERIPH, kTopEarlgreyPinmuxPeripheralInGpioGpio22);
PINMUX_ASSERT_EQ_(SW_STRAP_0_INSEL, kTopEarlgreyPinmuxInselIoc0);
PINMUX_ASSERT_EQ_(SW_STRAP_0_PAD, kTopEarlgreyMuxedPadsIoc0);
static const pinmux_input_t kInputSwStrap0 = {
    .periph = SW_STRAP_0_PERIPH,
    .insel = SW_STRAP_0_INSEL,
    .pad = SW_STRAP_0_PAD,
};

PINMUX_ASSERT_EQ_(SW_STRAP_1_PERIPH, kTopEarlgreyPinmuxPeripheralInGpioGpio23);
PINMUX_ASSERT_EQ_(SW_STRAP_1_INSEL, kTopEarlgreyPinmuxInselIoc1);
PINMUX_ASSERT_EQ_(SW_STRAP_1_PAD, kTopEarlgreyMuxedPadsIoc1);
static const pinmux_input_t kInputSwStrap1 = {
    .periph = SW_STRAP_1_PERIPH,
    .insel = SW_STRAP_1_INSEL,
    .pad = SW_STRAP_1_PAD,
};

PINMUX_ASSERT_EQ_(SW_STRAP_2_PERIPH, kTopEarlgreyPinmuxPeripheralInGpioGpio24);
PINMUX_ASSERT_EQ_(SW_STRAP_2_INSEL, kTopEarlgreyPinmuxInselIoc2);
PINMUX_ASSERT_EQ_(SW_STRAP_2_PAD, kTopEarlgreyMuxedPadsIoc2);
static const pinmux_input_t kInputSwStrap2 = {
    .periph = SW_STRAP_2_PERIPH,
    .insel = SW_STRAP_2_INSEL,
    .pad = SW_STRAP_2_PAD,
};

/**
 * Sets the input pad for the specified peripheral input.
 *
 * @param input A peripheral input and MIO pad to link it to.
 */
static void configure_input(pinmux_input_t input) {
  abs_mmio_write32(kBase + PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET +
                       input.periph * sizeof(uint32_t),
                   input.insel);
}

/**
 * Enables pull-down for the specified pad.
 *
 * @param pad A MIO pad.
 */
static void enable_pull_down(top_earlgrey_muxed_pads_t pad) {
  uint32_t reg =
      bitfield_bit32_write(0, PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT, true);
  abs_mmio_write32(
      kBase + PINMUX_MIO_PAD_ATTR_0_REG_OFFSET + pad * sizeof(uint32_t), reg);
}

/**
 * Sets the peripheral output for each specified output pad.
 *
 * @param output An MIO pad and a peripheral output to link it to.
 */
static void configure_output(pinmux_output_t output) {
  abs_mmio_write32(
      kBase + PINMUX_MIO_OUTSEL_0_REG_OFFSET + output.mio * sizeof(uint32_t),
      output.outsel);
}

void pinmux_init(void) {
  uint32_t bootstrap_dis =
      otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET);
  if (launder32(bootstrap_dis) != kHardenedBoolTrue) {
    HARDENED_CHECK_NE(bootstrap_dis, kHardenedBoolTrue);
    // Note: attributes should be configured before the pinmux matrix to avoid
    // "undesired electrical behavior and/or contention at the pads".
    enable_pull_down(kInputSwStrap0.pad);
    enable_pull_down(kInputSwStrap1.pad);
    enable_pull_down(kInputSwStrap2.pad);
    // Wait for pull downs to propagate to the physical pads.
    CSR_WRITE(CSR_REG_MCYCLE, 0);
    uint32_t mcycle;
    do {
      CSR_READ(CSR_REG_MCYCLE, &mcycle);
    } while (mcycle < PINMUX_PAD_ATTR_PROP_CYCLES);
    configure_input(kInputSwStrap0);
    configure_input(kInputSwStrap1);
    configure_input(kInputSwStrap2);
  }

  configure_input(kInputUart0);
  configure_output(kOutputUart0);
}
