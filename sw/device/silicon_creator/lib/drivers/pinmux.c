// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/pinmux.h"

#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/lib/sw/device/base/abs_mmio.h"
#include "sw/lib/sw/device/base/csr.h"
#include "sw/lib/sw/device/base/hardened.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/silicon_creator/base/chip.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "otp_ctrl_regs.h"
#include "pinmux_regs.h"

enum {
  /**
   * Base address of the pinmux registers.
   */
  kBase = TOP_DARJEELING_PINMUX_AON_BASE_ADDR,
};

/**
 * A peripheral input and MIO pad to link it to.
 */
typedef struct pinmux_input {
  top_darjeeling_pinmux_peripheral_in_t periph;
  top_darjeeling_pinmux_insel_t insel;
  top_darjeeling_muxed_pads_t pad;
} pinmux_input_t;

/**
 * An MIO pad and a peripheral output to link it to.
 */
typedef struct pinmux_output {
  top_darjeeling_pinmux_mio_out_t mio;
  top_darjeeling_pinmux_outsel_t outsel;
  top_darjeeling_muxed_pads_t pad;
} pinmux_output_t;

/**
 * Enables pull-down for the specified pad.
 *
 * @param pad A MIO pad.
 */
static void enable_pull_down(top_darjeeling_muxed_pads_t pad) {
  uint32_t reg =
      bitfield_bit32_write(0, PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT, true);
  abs_mmio_write32(
      kBase + PINMUX_MIO_PAD_ATTR_0_REG_OFFSET + pad * sizeof(uint32_t), reg);
}

void pinmux_init(void) {
  uint32_t bootstrap_dis =
      otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET);
  if (launder32(bootstrap_dis) != kHardenedBoolTrue) {
    HARDENED_CHECK_NE(bootstrap_dis, kHardenedBoolTrue);
    // Note: attributes should be configured before the pinmux matrix to avoid
    // "undesired electrical behavior and/or contention at the pads".
    enable_pull_down(SW_STRAP_0_PAD);
    enable_pull_down(SW_STRAP_1_PAD);
    enable_pull_down(SW_STRAP_2_PAD);
    // Wait for pull downs to propagate to the physical pads.
    CSR_WRITE(CSR_REG_MCYCLE, 0);
    uint32_t mcycle;
    do {
      CSR_READ(CSR_REG_MCYCLE, &mcycle);
    } while (mcycle < PINMUX_PAD_ATTR_PROP_CYCLES);
  }
}
