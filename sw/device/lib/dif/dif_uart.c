// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_uart.h"

#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"

#include "uart_regs.h"  // Generated.

#define UART_INTR_STATE_MASK 0xffffffffu

const uint32_t kDifUartFifoSizeBytes = 32u;

static bool uart_tx_full(const dif_uart_t *uart) {
  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, UART_STATUS_TXFULL_BIT);
}

static bool uart_tx_idle(const dif_uart_t *uart) {
  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, UART_STATUS_TXIDLE_BIT);
}

static bool uart_rx_empty(const dif_uart_t *uart) {
  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, UART_STATUS_RXEMPTY_BIT);
}

static uint8_t uart_rx_fifo_read(const dif_uart_t *uart) {
  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_RDATA_REG_OFFSET);

  return bitfield_field32_read(reg, UART_RDATA_RDATA_FIELD);
}

static void uart_tx_fifo_write(const dif_uart_t *uart, uint8_t byte) {
  uint32_t reg = bitfield_field32_write(0, UART_WDATA_WDATA_FIELD, byte);
  mmio_region_write32(uart->params.base_addr, UART_WDATA_REG_OFFSET, reg);
}

/**
 * Get the corresponding interrupt register bit offset. INTR_STATE, INTR_ENABLE
 * and INTR_TEST registers have the same bit offsets, so this routine can be
 * reused.
 */
static bool uart_irq_offset_get(dif_uart_irq_t irq_type,
                                ptrdiff_t *offset_out) {
  ptrdiff_t offset;
  switch (irq_type) {
    case kDifUartIrqTxWatermark:
      offset = UART_INTR_STATE_TX_WATERMARK_BIT;
      break;
    case kDifUartIrqRxWatermark:
      offset = UART_INTR_STATE_RX_WATERMARK_BIT;
      break;
    case kDifUartIrqTxEmpty:
      offset = UART_INTR_STATE_TX_EMPTY_BIT;
      break;
    case kDifUartIrqRxOverflow:
      offset = UART_INTR_STATE_RX_OVERFLOW_BIT;
      break;
    case kDifUartIrqRxFrameErr:
      offset = UART_INTR_STATE_RX_FRAME_ERR_BIT;
      break;
    case kDifUartIrqRxBreakErr:
      offset = UART_INTR_STATE_RX_BREAK_ERR_BIT;
      break;
    case kDifUartIrqRxTimeout:
      offset = UART_INTR_STATE_RX_TIMEOUT_BIT;
      break;
    case kDifUartIrqRxParityErr:
      offset = UART_INTR_STATE_RX_PARITY_ERR_BIT;
      break;
    default:
      return false;
  }

  *offset_out = offset;

  return true;
}

static void uart_reset(const dif_uart_t *uart) {
  mmio_region_write32(uart->params.base_addr, UART_CTRL_REG_OFFSET, 0u);

  // Write to the relevant bits clears the FIFOs.
  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, UART_FIFO_CTRL_RXRST_BIT, true);
  reg = bitfield_bit32_write(reg, UART_FIFO_CTRL_TXRST_BIT, true);
  mmio_region_write32(uart->params.base_addr, UART_FIFO_CTRL_REG_OFFSET, reg);

  mmio_region_write32(uart->params.base_addr, UART_OVRD_REG_OFFSET, 0u);
  mmio_region_write32(uart->params.base_addr, UART_TIMEOUT_CTRL_REG_OFFSET, 0u);
  mmio_region_write32(uart->params.base_addr, UART_INTR_ENABLE_REG_OFFSET, 0u);
  mmio_region_write32(uart->params.base_addr, UART_INTR_STATE_REG_OFFSET,
                      UART_INTR_STATE_MASK);
}

/**
 * Write up to `bytes_requested` number of bytes to the TX FIFO.
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
 * Read up to `bytes_requested` number of bytes from the RX FIFO.
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

dif_uart_result_t dif_uart_init(dif_uart_params_t params, dif_uart_t *uart) {
  if (uart == NULL) {
    return kDifUartBadArg;
  }

  uart->params = params;
  return kDifUartOk;
}

dif_uart_config_result_t dif_uart_configure(const dif_uart_t *uart,
                                            dif_uart_config_t config) {
  if (uart == NULL) {
    return kDifUartConfigBadArg;
  }

  if (config.baudrate == 0 || config.clk_freq_hz == 0) {
    return kDifUartConfigBadConfig;
  }

  // Calculation formula: NCO = 16 * 2^nco_width * baud / fclk.

  // Compute NCO register bit width
  uint32_t nco_width = 0;

  for (int i = 0; i < 32; i++) {
    nco_width += (UART_CTRL_NCO_MASK >> i) & 1;
  }

  _Static_assert((UART_CTRL_NCO_MASK >> 28) == 0,
                 "NCO bit width exceeds 28 bits.");

  // NCO creates 16x of baudrate. So, in addition to the nco_width,
  // 2^4 should be multiplied.
  uint64_t nco =
      ((uint64_t)config.baudrate << (nco_width + 4)) / config.clk_freq_hz;
  uint32_t nco_masked = nco & UART_CTRL_NCO_MASK;

  // Requested baudrate is too high for the given clock frequency.
  if (nco != nco_masked) {
    return kDifUartConfigBadNco;
  }

  // Must be called before the first write to any of the UART registers.
  uart_reset(uart);

  // Set baudrate, enable RX and TX, configure parity.
  uint32_t reg = 0;
  reg = bitfield_field32_write(reg, UART_CTRL_NCO_FIELD, nco_masked);
  reg = bitfield_bit32_write(reg, UART_CTRL_TX_BIT, true);
  reg = bitfield_bit32_write(reg, UART_CTRL_RX_BIT, true);
  if (config.parity_enable == kDifUartToggleEnabled) {
    reg = bitfield_bit32_write(reg, UART_CTRL_PARITY_EN_BIT, true);
  }
  if (config.parity == kDifUartParityOdd) {
    reg = bitfield_bit32_write(reg, UART_CTRL_PARITY_ODD_BIT, true);
  }
  mmio_region_write32(uart->params.base_addr, UART_CTRL_REG_OFFSET, reg);

  // Disable interrupts.
  mmio_region_write32(uart->params.base_addr, UART_INTR_ENABLE_REG_OFFSET, 0u);

  return kDifUartConfigOk;
}

dif_uart_result_t dif_uart_irq_is_pending(const dif_uart_t *uart,
                                          dif_uart_irq_t irq,
                                          bool *is_pending) {
  if (uart == NULL || is_pending == NULL) {
    return kDifUartBadArg;
  }

  ptrdiff_t offset;
  if (!uart_irq_offset_get(irq, &offset)) {
    return kDifUartError;
  }

  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_INTR_STATE_REG_OFFSET);
  *is_pending = bitfield_bit32_read(reg, offset);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_irq_acknowledge(const dif_uart_t *uart,
                                           dif_uart_irq_t irq) {
  if (uart == NULL) {
    return kDifUartBadArg;
  }

  ptrdiff_t offset;
  if (!uart_irq_offset_get(irq, &offset)) {
    return kDifUartError;
  }

  // Writing to the register clears the corresponding bits (Write-one clear).
  uint32_t reg = bitfield_bit32_write(0, offset, true);
  mmio_region_write32(uart->params.base_addr, UART_INTR_STATE_REG_OFFSET, reg);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_irq_disable_all(const dif_uart_t *uart,
                                           dif_uart_irq_snapshot_t *snapshot) {
  if (uart == NULL) {
    return kDifUartBadArg;
  }

  // Pass the current interrupt state to the caller.
  if (snapshot != NULL) {
    *snapshot =
        mmio_region_read32(uart->params.base_addr, UART_INTR_ENABLE_REG_OFFSET);
  }

  // Disable all UART interrupts.
  mmio_region_write32(uart->params.base_addr, UART_INTR_ENABLE_REG_OFFSET, 0u);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_irq_restore_all(
    const dif_uart_t *uart, const dif_uart_irq_snapshot_t *snapshot) {
  if (uart == NULL || snapshot == NULL) {
    return kDifUartBadArg;
  }

  mmio_region_write32(uart->params.base_addr, UART_INTR_ENABLE_REG_OFFSET,
                      *snapshot);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_irq_get_enabled(const dif_uart_t *uart,
                                           dif_uart_irq_t irq,
                                           dif_uart_toggle_t *state) {
  if (uart == NULL || state == NULL) {
    return kDifUartBadArg;
  }

  ptrdiff_t offset;
  if (!uart_irq_offset_get(irq, &offset)) {
    return kDifUartError;
  }

  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_INTR_ENABLE_REG_OFFSET);

  bool is_enabled = bitfield_bit32_read(reg, offset);
  *state = is_enabled ? kDifUartToggleEnabled : kDifUartToggleDisabled;

  return kDifUartOk;
}

dif_uart_result_t dif_uart_irq_set_enabled(const dif_uart_t *uart,
                                           dif_uart_irq_t irq,
                                           dif_uart_toggle_t state) {
  if (uart == NULL) {
    return kDifUartBadArg;
  }

  ptrdiff_t offset;
  if (!uart_irq_offset_get(irq, &offset)) {
    return kDifUartError;
  }

  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_INTR_ENABLE_REG_OFFSET);
  bool bit = (state == kDifUartToggleEnabled) ? true : false;
  reg = bitfield_bit32_write(reg, offset, bit);
  mmio_region_write32(uart->params.base_addr, UART_INTR_ENABLE_REG_OFFSET, reg);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_irq_force(const dif_uart_t *uart,
                                     dif_uart_irq_t irq) {
  if (uart == NULL) {
    return kDifUartBadArg;
  }

  ptrdiff_t offset;
  if (!uart_irq_offset_get(irq, &offset)) {
    return kDifUartError;
  }

  // Force the requested interrupt (write-only).
  uint32_t reg = bitfield_bit32_write(0, offset, true);
  mmio_region_write32(uart->params.base_addr, UART_INTR_TEST_REG_OFFSET, reg);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_watermark_rx_set(const dif_uart_t *uart,
                                            dif_uart_watermark_t watermark) {
  if (uart == NULL) {
    return kDifUartBadArg;
  }

  // Check if the requested watermark is valid, and get a corresponding
  // register definition to be written.
  uint32_t value;
  switch (watermark) {
    case kDifUartWatermarkByte1:
      value = UART_FIFO_CTRL_RXILVL_VALUE_RXLVL1;
      break;
    case kDifUartWatermarkByte4:
      value = UART_FIFO_CTRL_RXILVL_VALUE_RXLVL4;
      break;
    case kDifUartWatermarkByte8:
      value = UART_FIFO_CTRL_RXILVL_VALUE_RXLVL8;
      break;
    case kDifUartWatermarkByte16:
      value = UART_FIFO_CTRL_RXILVL_VALUE_RXLVL16;
      break;
    case kDifUartWatermarkByte30:
      value = UART_FIFO_CTRL_RXILVL_VALUE_RXLVL30;
      break;
    default:
      return kDifUartError;
  }

  // Set watermark level.
  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_FIFO_CTRL_REG_OFFSET);
  reg = bitfield_field32_write(reg, UART_FIFO_CTRL_RXILVL_FIELD, value);
  mmio_region_write32(uart->params.base_addr, UART_FIFO_CTRL_REG_OFFSET, reg);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_watermark_tx_set(const dif_uart_t *uart,
                                            dif_uart_watermark_t watermark) {
  if (uart == NULL) {
    return kDifUartBadArg;
  }

  // Check if the requested watermark is valid, and get a corresponding
  // register definition to be written.
  uint32_t value;
  switch (watermark) {
    case kDifUartWatermarkByte1:
      value = UART_FIFO_CTRL_TXILVL_VALUE_TXLVL1;
      break;
    case kDifUartWatermarkByte4:
      value = UART_FIFO_CTRL_TXILVL_VALUE_TXLVL4;
      break;
    case kDifUartWatermarkByte8:
      value = UART_FIFO_CTRL_TXILVL_VALUE_TXLVL8;
      break;
    case kDifUartWatermarkByte16:
      value = UART_FIFO_CTRL_TXILVL_VALUE_TXLVL16;
      break;
    default:
      // The minimal TX watermark is 1 byte, maximal 16 bytes.
      return kDifUartError;
  }

  // Set watermark level.
  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_FIFO_CTRL_REG_OFFSET);
  reg = bitfield_field32_write(reg, UART_FIFO_CTRL_TXILVL_FIELD, value);
  mmio_region_write32(uart->params.base_addr, UART_FIFO_CTRL_REG_OFFSET, reg);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_bytes_send(const dif_uart_t *uart,
                                      const uint8_t *data,
                                      size_t bytes_requested,
                                      size_t *bytes_written) {
  if (uart == NULL || data == NULL) {
    return kDifUartBadArg;
  }

  // `bytes_written` is an optional parameter.
  size_t res = uart_bytes_send(uart, data, bytes_requested);
  if (bytes_written != NULL) {
    *bytes_written = res;
  }

  return kDifUartOk;
}

dif_uart_result_t dif_uart_bytes_receive(const dif_uart_t *uart,
                                         size_t bytes_requested, uint8_t *data,
                                         size_t *bytes_read) {
  if (uart == NULL || data == NULL) {
    return kDifUartBadArg;
  }

  // `bytes_read` is an optional parameter.
  size_t res = uart_bytes_receive(uart, bytes_requested, data);
  if (bytes_read != NULL) {
    *bytes_read = res;
  }

  return kDifUartOk;
}

dif_uart_result_t dif_uart_byte_send_polled(const dif_uart_t *uart,
                                            uint8_t byte) {
  if (uart == NULL) {
    return kDifUartBadArg;
  }

  // Busy wait for the TX FIFO to free up.
  while (uart_tx_full(uart)) {
  }

  (void)uart_bytes_send(uart, &byte, 1);

  // Busy wait for the TX FIFO to be drained and for HW to finish processing
  // the last byte.
  while (!uart_tx_idle(uart)) {
  }

  return kDifUartOk;
}

dif_uart_result_t dif_uart_byte_receive_polled(const dif_uart_t *uart,
                                               uint8_t *byte) {
  if (uart == NULL || byte == NULL) {
    return kDifUartBadArg;
  }

  // Busy wait for the RX message in the FIFO.
  while (uart_rx_empty(uart)) {
  }

  (void)uart_bytes_receive(uart, 1, byte);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_rx_bytes_available(const dif_uart_t *uart,
                                              size_t *num_bytes) {
  if (uart == NULL || num_bytes == NULL) {
    return kDifUartBadArg;
  }

  // RX FIFO fill level (in bytes).
  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_FIFO_STATUS_REG_OFFSET);
  *num_bytes = (size_t)bitfield_field32_read(reg, UART_FIFO_STATUS_RXLVL_FIELD);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_tx_bytes_available(const dif_uart_t *uart,
                                              size_t *num_bytes) {
  if (uart == NULL || num_bytes == NULL) {
    return kDifUartBadArg;
  }

  // TX FIFO fill level (in bytes).
  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_FIFO_STATUS_REG_OFFSET);
  uint32_t fill_bytes =
      bitfield_field32_read(reg, UART_FIFO_STATUS_TXLVL_FIELD);
  *num_bytes = kDifUartFifoSizeBytes - fill_bytes;

  return kDifUartOk;
}

dif_uart_result_t dif_uart_fifo_reset(const dif_uart_t *uart,
                                      dif_uart_fifo_reset_t reset) {
  if (uart == NULL) {
    return kDifUartBadArg;
  }

  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_FIFO_CTRL_REG_OFFSET);

  if (reset == kDifUartFifoResetRx || reset == kDifUartFifoResetAll) {
    reg = bitfield_bit32_write(reg, UART_FIFO_CTRL_RXRST_BIT, true);
  }

  if (reset == kDifUartFifoResetTx || reset == kDifUartFifoResetAll) {
    reg = bitfield_bit32_write(reg, UART_FIFO_CTRL_TXRST_BIT, true);
  }

  mmio_region_write32(uart->params.base_addr, UART_FIFO_CTRL_REG_OFFSET, reg);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_loopback_set(const dif_uart_t *uart,
                                        dif_uart_loopback_t loopback,
                                        dif_uart_toggle_t enable) {
  if (uart == NULL) {
    return kDifUartBadArg;
  }

  uint32_t index = loopback ? UART_CTRL_LLPBK_BIT : UART_CTRL_SLPBK_BIT;
  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_CTRL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, index, enable == kDifUartToggleEnabled);
  mmio_region_write32(uart->params.base_addr, UART_CTRL_REG_OFFSET, reg);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_enable_rx_timeout(const dif_uart_t *uart,
                                             uint32_t duration_ticks) {
  if (uart == NULL || (duration_ticks & ~UART_TIMEOUT_CTRL_VAL_MASK) != 0) {
    return kDifUartBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, UART_TIMEOUT_CTRL_EN_BIT, true);
  reg =
      bitfield_field32_write(reg, UART_TIMEOUT_CTRL_VAL_FIELD, duration_ticks);
  mmio_region_write32(uart->params.base_addr, UART_TIMEOUT_CTRL_REG_OFFSET,
                      reg);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_disable_rx_timeout(const dif_uart_t *uart) {
  if (uart == NULL) {
    return kDifUartBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, UART_TIMEOUT_CTRL_EN_BIT, false);
  reg = bitfield_field32_write(reg, UART_TIMEOUT_CTRL_VAL_FIELD, 0);
  mmio_region_write32(uart->params.base_addr, UART_TIMEOUT_CTRL_REG_OFFSET,
                      reg);

  return kDifUartOk;
}

dif_uart_result_t dif_uart_get_rx_timeout(const dif_uart_t *uart,
                                          dif_uart_toggle_t *status,
                                          uint32_t *duration_ticks) {
  if (uart == NULL || status == NULL) {
    return kDifUartBadArg;
  }

  uint32_t reg =
      mmio_region_read32(uart->params.base_addr, UART_TIMEOUT_CTRL_REG_OFFSET);
  *status = bitfield_bit32_read(reg, UART_TIMEOUT_CTRL_EN_BIT)
                ? kDifUartToggleEnabled
                : kDifUartToggleDisabled;

  if (duration_ticks != NULL) {
    *duration_ticks = bitfield_field32_read(reg, UART_TIMEOUT_CTRL_VAL_FIELD);
  }

  return kDifUartOk;
}
