// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/uart.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "uart_regs.h"  // Generated.

static void uart_reset(void) {
  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_CTRL_REG_OFFSET, 0u);

  // Write to the relevant bits clears the FIFOs.
  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, UART_FIFO_CTRL_RXRST_BIT, true);
  reg = bitfield_bit32_write(reg, UART_FIFO_CTRL_TXRST_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_FIFO_CTRL_REG_OFFSET,
                   reg);

  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_OVRD_REG_OFFSET, 0u);
  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_TIMEOUT_CTRL_REG_OFFSET,
                   0u);
  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_ENABLE_REG_OFFSET,
                   0u);
  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_STATE_REG_OFFSET,
                   UINT32_MAX);
}

rom_error_t uart_init(uint32_t precalculated_nco) {
  // Must be called before the first write to any of the UART registers.
  uart_reset();

  // Set baudrate, TX, no parity bits.
  uint32_t reg = 0;
  reg = bitfield_field32_write(reg, UART_CTRL_NCO_FIELD, precalculated_nco);
  reg = bitfield_bit32_write(reg, UART_CTRL_TX_BIT, true);
  reg = bitfield_bit32_write(reg, UART_CTRL_PARITY_EN_BIT, false);
  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_CTRL_REG_OFFSET, reg);

  // Disable interrupts.
  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_ENABLE_REG_OFFSET,
                   0u);
  return kErrorOk;
}

static bool uart_tx_full(void) {
  uint32_t reg =
      abs_mmio_read32(TOP_EARLGREY_UART0_BASE_ADDR + UART_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, UART_STATUS_TXFULL_BIT);
}

static bool uart_tx_idle(void) {
  uint32_t reg =
      abs_mmio_read32(TOP_EARLGREY_UART0_BASE_ADDR + UART_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, UART_STATUS_TXIDLE_BIT);
}

void uart_putchar(uint8_t byte) {
  // If the transmit FIFO is full, wait.
  while (uart_tx_full()) {
  }
  uint32_t reg = bitfield_field32_write(0, UART_WDATA_WDATA_FIELD, byte);
  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_WDATA_REG_OFFSET, reg);

  // If the transmitter is active, wait.
  while (!uart_tx_idle()) {
  }
}

/**
 * Write `len` bytes to the UART TX FIFO.
 */
size_t uart_write(const uint8_t *data, size_t len) {
  size_t total = len;
  while (len) {
    uart_putchar(*data);
    data++;
    len--;
  }
  return total;
}

size_t uart_sink(void *uart, const char *data, size_t len) {
  (void)uart;
  return uart_write((const uint8_t *)data, len);
}
