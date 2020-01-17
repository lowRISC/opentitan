// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_uart.h"

#include <stddef.h>

#include "sw/device/lib/base/mmio.h"
#include "uart_regs.h"  // Generated.

#define UART_RX_FIFO_SIZE_BYTES 32u
#define UART_TX_FIFO_SIZE_BYTES 32u

static bool uart_tx_full(const dif_uart_t *uart) {
  return mmio_region_get_bit32(uart->base_addr, UART_STATUS_REG_OFFSET,
                               UART_STATUS_TXFULL);
}

static bool uart_tx_empty(const dif_uart_t *uart) {
  return mmio_region_get_bit32(uart->base_addr, UART_STATUS_REG_OFFSET,
                               UART_STATUS_TXEMPTY);
}

static bool uart_rx_empty(const dif_uart_t *uart) {
  return mmio_region_get_bit32(uart->base_addr, UART_STATUS_REG_OFFSET,
                               UART_STATUS_RXEMPTY);
}

static uint8_t uart_rx_fifo_read(const dif_uart_t *uart) {
  uint32_t reg = mmio_region_read32(uart->base_addr, UART_RDATA_REG_OFFSET);

  return reg & UART_RDATA_MASK;
}

static void uart_tx_fifo_write(const dif_uart_t *uart, uint8_t byte) {
  uint32_t reg = (byte & UART_WDATA_MASK) << UART_WDATA_OFFSET;
  mmio_region_write32(uart->base_addr, UART_WDATA_REG_OFFSET, reg);
}

/**
 * Get the corresponding interrupt register bit offset. INTR_STATE, INTR_ENABLE
 * and INTR_TEST registers have the same bit offsets, so this routine can be
 * reused.
 */
static ptrdiff_t uart_irq_offset_get(dif_uart_interrupt_t irq_type) {
  ptrdiff_t offset;
  switch (irq_type) {
    case kDifUartInterruptTxWatermark:
      offset = UART_INTR_STATE_TX_WATERMARK;
      break;
    case kDifUartInterruptRxWatermark:
      offset = UART_INTR_STATE_RX_WATERMARK;
      break;
    case kDifUartInterruptTxEmpty:
      offset = UART_INTR_STATE_TX_EMPTY;
      break;
    case kDifUartInterruptRxOverflow:
      offset = UART_INTR_STATE_RX_OVERFLOW;
      break;
    case kDifUartInterruptRxFrameErr:
      offset = UART_INTR_STATE_RX_FRAME_ERR;
      break;
    case kDifUartInterruptRxBreakErr:
      offset = UART_INTR_STATE_RX_BREAK_ERR;
      break;
    case kDifUartInterruptRxTimeout:
      offset = UART_INTR_STATE_RX_TIMEOUT;
      break;
    case kDifUartInterruptRxParityErr:
      offset = UART_INTR_STATE_RX_PARITY_ERR;
      break;
    default:
      __builtin_unreachable();
  }

  return offset;
}

/**
 * Performs fundamental UART configuration.
 */
static bool uart_configure(const dif_uart_t *uart,
                           const dif_uart_config_t *config) {
  if (config->baudrate == 0 || config->clk_freq_hz == 0) {
    return false;
  }

  // Calculation formula: NCO = 2^20 * baud / fclk
  uint64_t nco = ((uint64_t)config->baudrate << 20) / config->clk_freq_hz;
  uint32_t nco_masked = nco & UART_CTRL_NCO_MASK;

  // Requested baudrate is too high for the given clock frequency
  if (nco != nco_masked) {
    return false;
  }

  // Set baudrate, enable RX and TX, configure parity
  uint32_t reg = (nco_masked << UART_CTRL_NCO_OFFSET);
  reg |= (1u << UART_CTRL_TX);
  reg |= (1u << UART_CTRL_RX);
  if (config->parity_enable == kDifUartEnable) {
    reg |= (1u << UART_CTRL_PARITY_EN);
  }
  if (config->parity == kDifUartParityOdd) {
    reg |= (1u << UART_CTRL_PARITY_ODD);
  }
  mmio_region_write32(uart->base_addr, UART_CTRL_REG_OFFSET, reg);

  // Reset RX/TX FIFOs
  reg = (1u << UART_FIFO_CTRL_RXRST);
  reg |= (1u << UART_FIFO_CTRL_TXRST);
  mmio_region_write32(uart->base_addr, UART_FIFO_CTRL_REG_OFFSET, reg);

  // Disable interrupts
  mmio_region_write32(uart->base_addr, UART_INTR_ENABLE_REG_OFFSET, 0u);

  return true;
}

/**
 * Write up to |bytes_requested| number of bytes to the TX FIFO.
 */
static size_t uart_bytes_send(const dif_uart_t *uart, const uint8_t *data,
                              size_t bytes_requested) {
  size_t bytes_written = 0;
  while ((bytes_written < bytes_requested) && !uart_tx_full(uart)) {
    uart_tx_fifo_write(uart, data[bytes_written]);
    ++bytes_written;
  }

  return bytes_written;
}

/**
 * Read up to |bytes_requested| number of bytes from the RX FIFO.
 */
static size_t uart_bytes_receive(const dif_uart_t *uart, size_t bytes_requested,
                                 uint8_t *data) {
  size_t bytes_read = 0;
  while ((bytes_read < bytes_requested) && !uart_rx_empty(uart)) {
    data[bytes_read] = uart_rx_fifo_read(uart);
    ++bytes_read;
  }

  return bytes_read;
}

bool dif_uart_init(mmio_region_t base_addr, const dif_uart_config_t *config,
                   dif_uart_t *uart) {
  if (uart == NULL || config == NULL || base_addr.base == NULL) {
    return false;
  }

  uart->base_addr = base_addr;

  return uart_configure(uart, config);
}

bool dif_uart_configure(const dif_uart_t *uart,
                        const dif_uart_config_t *config) {
  if ((uart == NULL) || (config == NULL)) {
    return false;
  }

  return uart_configure(uart, config);
}

bool dif_uart_watermark_rx_set(const dif_uart_t *uart,
                               dif_uart_watermark_t watermark) {
  if (uart == NULL) {
    return false;
  }

  // Check if the requested watermark is valid, and get a corresponding
  // register definition to be written
  uint32_t rxi_level;
  switch (watermark) {
    case kDifUartWatermarkByte1:
      rxi_level = UART_FIFO_CTRL_RXILVL_RXLVL1;
      break;
    case kDifUartWatermarkByte4:
      rxi_level = UART_FIFO_CTRL_RXILVL_RXLVL4;
      break;
    case kDifUartWatermarkByte8:
      rxi_level = UART_FIFO_CTRL_RXILVL_RXLVL8;
      break;
    case kDifUartWatermarkByte16:
      rxi_level = UART_FIFO_CTRL_RXILVL_RXLVL16;
      break;
    case kDifUartWatermarkByte30:
      rxi_level = UART_FIFO_CTRL_RXILVL_RXLVL30;
      break;
    default:
      return false;
  }

  // Set watermark level
  mmio_region_nonatomic_set_mask32(uart->base_addr, UART_FIFO_CTRL_REG_OFFSET,
                                   rxi_level, UART_FIFO_CTRL_RXILVL_OFFSET);

  return true;
}

bool dif_uart_watermark_tx_set(const dif_uart_t *uart,
                               dif_uart_watermark_t watermark) {
  if (uart == NULL) {
    return false;
  }

  // Check if the requested watermark is valid, and get a corresponding
  // register definition to be written.
  uint32_t txi_level;
  switch (watermark) {
    case kDifUartWatermarkByte1:
      txi_level = UART_FIFO_CTRL_TXILVL_TXLVL1;
      break;
    case kDifUartWatermarkByte4:
      txi_level = UART_FIFO_CTRL_TXILVL_TXLVL4;
      break;
    case kDifUartWatermarkByte8:
      txi_level = UART_FIFO_CTRL_TXILVL_TXLVL8;
      break;
    case kDifUartWatermarkByte16:
      txi_level = UART_FIFO_CTRL_TXILVL_TXLVL16;
      break;
    default:
      // The minimal TX watermark is 1 byte, maximal 16 bytes
      return false;
  }

  // Set watermark level
  mmio_region_nonatomic_set_mask32(uart->base_addr, UART_FIFO_CTRL_REG_OFFSET,
                                   txi_level, UART_FIFO_CTRL_TXILVL_OFFSET);

  return true;
}

bool dif_uart_bytes_send(const dif_uart_t *uart, const uint8_t *data,
                         size_t bytes_requested, size_t *bytes_written) {
  if (uart == NULL || bytes_written == NULL) {
    return false;
  }

  // |bytes_written| is an optional parameter
  size_t res = uart_bytes_send(uart, data, bytes_requested);
  if (bytes_written != NULL) {
    *bytes_written = res;
  }

  return true;
}

bool dif_uart_bytes_receive(const dif_uart_t *uart, size_t bytes_requested,
                            uint8_t *data, size_t *bytes_read) {
  if (uart == NULL) {
    return false;
  }

  // |bytes_read| is an optional parameter
  size_t res = uart_bytes_receive(uart, bytes_requested, data);
  if (bytes_read != NULL) {
    *bytes_read = res;
  }

  return true;
}

bool dif_uart_byte_send_polled(const dif_uart_t *uart, uint8_t byte) {
  if (uart == NULL) {
    return false;
  }

  // Busy wait for the TX FIFO to free up
  while (uart_tx_full(uart)) {
  }

  (void)uart_bytes_send(uart, &byte, 1);

  // Busy wait for the TX FIFO to be drained (the byte has been processed by
  // the UART hardware).
  while (!uart_tx_empty(uart)) {
  }

  return true;
}

bool dif_uart_byte_receive_polled(const dif_uart_t *uart, uint8_t *byte) {
  if (uart == NULL || byte == NULL) {
    return false;
  }

  // Busy wait for the RX message in the FIFO
  while (uart_rx_empty(uart)) {
  }

  (void)uart_bytes_receive(uart, 1, byte);

  return true;
}

bool dif_uart_irq_state_get(const dif_uart_t *uart,
                            dif_uart_interrupt_t irq_type,
                            dif_uart_enable_t *state) {
  if (uart == NULL || state == NULL) {
    return false;
  }

  // Get the requested interrupt state (enabled/disabled)
  ptrdiff_t offset = uart_irq_offset_get(irq_type);
  bool enabled = mmio_region_get_bit32(uart->base_addr,
                                       UART_INTR_STATE_REG_OFFSET, offset);
  if (enabled) {
    *state = kDifUartEnable;
  } else {
    *state = kDifUartDisable;
  }

  return true;
}

bool dif_uart_irqs_disable(const dif_uart_t *uart, uint32_t *state) {
  if (uart == NULL) {
    return false;
  }

  // Get the current interrupts state
  uint32_t reg =
      mmio_region_read32(uart->base_addr, UART_INTR_ENABLE_REG_OFFSET);

  // Disable all UART interrupts
  mmio_region_write32(uart->base_addr, UART_INTR_ENABLE_REG_OFFSET, 0u);

  // Pass the previous interrupt state to the caller
  if (state != NULL) {
    *state = reg;
  }

  return true;
}

bool dif_uart_irqs_restore(const dif_uart_t *uart, uint32_t state) {
  if (uart == NULL) {
    return false;
  }

  // Restore the interrupt state
  mmio_region_write32(uart->base_addr, UART_INTR_ENABLE_REG_OFFSET, state);

  return true;
}

bool dif_uart_irq_enable(const dif_uart_t *uart, dif_uart_interrupt_t irq_type,
                         dif_uart_enable_t enable) {
  if (uart == NULL) {
    return false;
  }

  // Enable/disable the requested interrupt
  ptrdiff_t offset = uart_irq_offset_get(irq_type);
  if (enable == kDifUartEnable) {
    mmio_region_nonatomic_set_bit32(uart->base_addr,
                                    UART_INTR_ENABLE_REG_OFFSET, offset);
  } else {
    mmio_region_nonatomic_clear_bit32(uart->base_addr,
                                      UART_INTR_ENABLE_REG_OFFSET, offset);
  }

  return true;
}

bool dif_uart_irq_force(const dif_uart_t *uart, dif_uart_interrupt_t irq_type) {
  if (uart == NULL) {
    return false;
  }

  // Force the requested interrupt
  ptrdiff_t offset = uart_irq_offset_get(irq_type);
  mmio_region_nonatomic_set_bit32(uart->base_addr, UART_INTR_TEST_REG_OFFSET,
                                  offset);

  return true;
}

bool dif_uart_rx_bytes_available(const dif_uart_t *uart, size_t *num_bytes) {
  if (uart == NULL || num_bytes == NULL) {
    return false;
  }

  // RX FIFO fill level (in bytes)
  *num_bytes = (size_t)mmio_region_read_mask32(
      uart->base_addr, UART_FIFO_STATUS_REG_OFFSET, UART_FIFO_STATUS_RXLVL_MASK,
      UART_FIFO_STATUS_RXLVL_OFFSET);

  return true;
}

bool dif_uart_tx_bytes_available(const dif_uart_t *uart, size_t *num_bytes) {
  if (uart == NULL || num_bytes == NULL) {
    return false;
  }

  // TX FIFO fill level (in bytes)
  uint32_t fill_bytes = mmio_region_read_mask32(
      uart->base_addr, UART_FIFO_STATUS_REG_OFFSET, UART_FIFO_STATUS_TXLVL_MASK,
      UART_FIFO_STATUS_TXLVL_OFFSET);

  *num_bytes = UART_TX_FIFO_SIZE_BYTES - fill_bytes;

  return true;
}
