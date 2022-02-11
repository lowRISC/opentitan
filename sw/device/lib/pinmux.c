// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/pinmux.h"

#include "sw/device/lib/base/mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pinmux_regs.h"  // Generated.

#define PINMUX0_BASE_ADDR TOP_EARLGREY_PINMUX_AON_BASE_ADDR

#define NUM_GPIO 32

static void init_gpio_regs(uint32_t reg, uint32_t mask, uint32_t start_v) {
  mmio_region_t reg32 = mmio_region_from_addr(reg);
  uint32_t reg_value = start_v;
  uint32_t reg_offset = kTopEarlgreyPinmuxPeripheralInGpioGpio0 << 2;

  // We've got 32 GPIOs
  for (uint32_t i = 0; i < NUM_GPIO; ++i) {
    mmio_region_write32(reg32, reg_offset, reg_value & mask);
    reg_value++;
    reg_offset += 4;
  }
}

void pinmux_init(void) {
  // TODO: This hardcoded configuration is temporary and needs to be
  // replaced by proper initialization code once 1) the pinmux DIF is
  // available, 2) the pinmux and padring design is finalized.

  // input: assign MIO0..MIO31 to GPIO0..GPIO31
  init_gpio_regs(PINMUX0_BASE_ADDR + PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET,
                 PINMUX_MIO_PERIPH_INSEL_0_IN_0_MASK,
                 PINMUX_MIO_PERIPH_INSEL_IDX_OFFSET);

  // output: assign GPIO0..GPIO31 to MIO0..MIO31
  init_gpio_regs(PINMUX0_BASE_ADDR + PINMUX_MIO_OUTSEL_0_REG_OFFSET,
                 PINMUX_MIO_OUTSEL_0_OUT_0_MASK,
                 PINMUX_PERIPH_OUTSEL_IDX_OFFSET);

  // Configure UART0 RX input to connect to MIO pad IOC3
  mmio_region_t reg32 = mmio_region_from_addr(
      PINMUX0_BASE_ADDR + PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET);
  uint32_t reg_value = kTopEarlgreyPinmuxInselIoc3;
  // We've got one insel configuration field per register. Hence, we have to
  // convert the enumeration index into a byte address using << 2.
  uint32_t reg_offset = kTopEarlgreyPinmuxPeripheralInUart0Rx << 2;
  uint32_t mask = PINMUX_MIO_PERIPH_INSEL_0_IN_0_MASK;
  mmio_region_write32(reg32, reg_offset, reg_value & mask);

  // Configure UART0 TX output to connect to MIO pad IOC4
  reg32 =
      mmio_region_from_addr(PINMUX0_BASE_ADDR + PINMUX_MIO_OUTSEL_0_REG_OFFSET);
  reg_value = kTopEarlgreyPinmuxOutselUart0Tx;
  // We've got one insel configuration field per register. Hence, we have to
  // convert the enumeration index into a byte address using << 2.
  reg_offset = kTopEarlgreyPinmuxMioOutIoc4 << 2;
  mask = PINMUX_MIO_OUTSEL_0_OUT_0_MASK;
  mmio_region_write32(reg32, reg_offset, reg_value & mask);

  // Configure UART1 RX input to connect to MIO pad IOC8
  reg32 = mmio_region_from_addr(PINMUX0_BASE_ADDR +
                                PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET);
  reg_value = kTopEarlgreyPinmuxInselIoc8;
  // We've got one insel configuration field per register. Hence, we have to
  // convert the enumeration index into a byte address using << 2.
  reg_offset = kTopEarlgreyPinmuxPeripheralInUart1Rx << 2;
  mask = PINMUX_MIO_PERIPH_INSEL_0_IN_0_MASK;
  mmio_region_write32(reg32, reg_offset, reg_value & mask);

  // Configure UART1 TX output to connect to MIO pad IOC9
  reg32 =
      mmio_region_from_addr(PINMUX0_BASE_ADDR + PINMUX_MIO_OUTSEL_0_REG_OFFSET);
  reg_value = kTopEarlgreyPinmuxOutselUart1Tx;
  // We've got one insel configuration field per register. Hence, we have to
  // convert the enumeration index into a byte address using << 2.
  reg_offset = kTopEarlgreyPinmuxMioOutIoc9 << 2;
  mask = PINMUX_MIO_OUTSEL_0_OUT_0_MASK;
  mmio_region_write32(reg32, reg_offset, reg_value & mask);

  // Configure USBDEV SENSE outputs to be high-Z (IOR0, IOR1)
  reg32 =
      mmio_region_from_addr(PINMUX0_BASE_ADDR + PINMUX_MIO_OUTSEL_0_REG_OFFSET);
  reg_value = kTopEarlgreyPinmuxOutselConstantHighZ;
  mask = PINMUX_MIO_OUTSEL_0_OUT_0_MASK;
  // We've got one insel configuration field per register. Hence, we have to
  // convert the enumeration index into a byte address using << 2.
  reg_offset = kTopEarlgreyPinmuxMioOutIor0 << 2;
  mmio_region_write32(reg32, reg_offset, reg_value & mask);
  // We've got one insel configuration field per register. Hence, we have to
  // convert the enumeration index into a byte address using << 2.
  reg_offset = kTopEarlgreyPinmuxMioOutIor1 << 2;
  mmio_region_write32(reg32, reg_offset, reg_value & mask);
}
