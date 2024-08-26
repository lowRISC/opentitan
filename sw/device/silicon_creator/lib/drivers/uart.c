// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/uart.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
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

void uart_init(uint32_t precalculated_nco) {
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
}

void uart_enable_receiver(void) {
  uint32_t reg =
      abs_mmio_read32(TOP_EARLGREY_UART0_BASE_ADDR + UART_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, UART_CTRL_RX_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_CTRL_REG_OFFSET, reg);
}

OT_WARN_UNUSED_RESULT
static bool uart_tx_full(void) {
  uint32_t reg =
      abs_mmio_read32(TOP_EARLGREY_UART0_BASE_ADDR + UART_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, UART_STATUS_TXFULL_BIT);
}

OT_WARN_UNUSED_RESULT
static bool uart_rx_empty(void) {
  uint32_t reg =
      abs_mmio_read32(TOP_EARLGREY_UART0_BASE_ADDR + UART_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, UART_STATUS_RXEMPTY_BIT);
}

bool uart_tx_idle(void) {
  uint32_t reg =
      abs_mmio_read32(TOP_EARLGREY_UART0_BASE_ADDR + UART_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, UART_STATUS_TXIDLE_BIT);
}

static void putchar_nonblocking(uint8_t byte) {
  // If the transmit FIFO is full, wait.
  while (uart_tx_full()) {
  }
  uint32_t reg = bitfield_field32_write(0, UART_WDATA_WDATA_FIELD, byte);
  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_WDATA_REG_OFFSET, reg);
}

void uart_putchar(uint8_t byte) {
  putchar_nonblocking(byte);
  // If the transmitter is active, wait.
  while (!uart_tx_idle()) {
  }
}

int uart_getchar(uint32_t timeout_ms) {
  uint8_t ch;
  size_t n = uart_read(&ch, 1, timeout_ms);
  return n ? (int)ch : -1;
}

void uart_write(const void *data, size_t len) {
  const uint8_t *d = (const uint8_t *)data;
  while (len) {
    uart_putchar(*d++);
    len--;
  }
}

void uart_write_hex(uint32_t val, size_t len, uint32_t after) {
  HARDENED_CHECK_LE(len, sizeof(uint32_t));
  static const uint8_t kHexTable[16] = "0123456789abcdef";
  size_t i = len * 8;
  do {
    i -= 4;
    putchar_nonblocking(kHexTable[(val >> i) & 0xF]);
  } while (i > 0);
  uart_write_imm(after);
}

void uart_write_imm(uint64_t imm) {
  while (imm) {
    putchar_nonblocking(imm & 0xFF);
    imm >>= 8;
  }
}

size_t uart_read(uint8_t *data, size_t len, uint32_t timeout_ms) {
  uint64_t time = ibex_mcycle();
  uint64_t deadline = timeout_ms == UINT32_MAX
                          ? UINT64_MAX
                          : time + ibex_time_to_cycles(timeout_ms * 1000);

  size_t n = 0;
  for (n = 0; n < len; ++n) {
    // If the receive FIFO is empty, wait.
    while (uart_rx_empty()) {
      time = ibex_mcycle();
      if (time > deadline)
        return n;
    }
    uint32_t reg =
        abs_mmio_read32(TOP_EARLGREY_UART0_BASE_ADDR + UART_RDATA_REG_OFFSET);
    *data++ = (uint8_t)reg;
  }
  return n;
}

hardened_bool_t uart_break_detect(uint32_t timeout_us) {
  uint64_t time = ibex_mcycle();
  uint64_t deadline = time + ibex_time_to_cycles(timeout_us);
  while (time < deadline) {
    uint32_t val =
        abs_mmio_read32(TOP_EARLGREY_UART0_BASE_ADDR + UART_VAL_REG_OFFSET);
    if (val)
      return kHardenedBoolFalse;
    time = ibex_mcycle();
  }
  return kHardenedBoolTrue;
}

size_t uart_sink(void *uart, const char *data, size_t len) {
  (void)uart;
  uart_write((const uint8_t *)data, len);
  return len;
}
