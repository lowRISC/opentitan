// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "spi_device.h"

#include "common.h"
#include "uart.h"

uint32_t calc_depth(uint32_t wptr, uint32_t rptr, uint32_t size);

/**
 * Init SPI Device
 *
 * Configure registers, RXF_ADDR, TXF_ADDR, CTRL.TIMER_V
 */
void spid_init(void) {
  /* Abort 0 */
  REG32(SPI_DEVICE_CONTROL(0)) =
      REG32(SPI_DEVICE_CONTROL(0)) & ~(1 << SPI_DEVICE_CONTROL_ABORT);

  /* CPOL(0), CPHA(0), ORDERs(00), TIMER(63) */
  REG32(SPI_DEVICE_CFG(0)) =
      ((0 << SPI_DEVICE_CFG_CPOL) | (0 << SPI_DEVICE_CFG_CPHA) |
       (0 << SPI_DEVICE_CFG_RX_ORDER) | (0 << SPI_DEVICE_CFG_TX_ORDER) |
       ((63 & SPI_DEVICE_CFG_TIMER_V_MASK) << SPI_DEVICE_CFG_TIMER_V_OFFSET));

  /* SRAM RXF/TXF ADDR. */
  REG32(SPI_DEVICE_RXF_ADDR(0)) =
      ((SPID_RXF_BASE & SPI_DEVICE_RXF_ADDR_BASE_MASK)
       << SPI_DEVICE_RXF_ADDR_BASE_OFFSET) |
      (((SPID_RXF_SIZE - 1) & SPI_DEVICE_RXF_ADDR_LIMIT_MASK)
       << SPI_DEVICE_RXF_ADDR_LIMIT_OFFSET);

  REG32(SPI_DEVICE_TXF_ADDR(0)) =
      ((SPID_TXF_BASE & SPI_DEVICE_TXF_ADDR_BASE_MASK)
       << SPI_DEVICE_TXF_ADDR_BASE_OFFSET) |
      (((SPID_TXF_SIZE - 1) & SPI_DEVICE_TXF_ADDR_LIMIT_MASK)
       << SPI_DEVICE_TXF_ADDR_LIMIT_OFFSET);
}

/**
 * Calculation FIFO depth in bytes
 *
 *  Assume SRAM size is fixed (constant) given by SPI_DEVICE_BUFFER_SIZE
 *
 * Fifo pointers are in bytes
 */
inline uint32_t calc_depth(uint32_t wptr, uint32_t rptr, uint32_t size) {
  const uint32_t sram_szw = BITLENGTH(SPI_DEVICE_BUFFER_SIZE_BYTES - 1);
  uint32_t depth;
  uint32_t wptr_phase, rptr_phase, wptr_v, rptr_v;
  wptr_phase = wptr >> sram_szw;
  rptr_phase = rptr >> sram_szw;
  wptr_v = wptr & (SPI_DEVICE_BUFFER_SIZE_BYTES - 1);
  rptr_v = rptr & (SPI_DEVICE_BUFFER_SIZE_BYTES - 1);

  if (wptr_phase == rptr_phase) {
    depth = (wptr_v - rptr_v);
  } else {
    depth = size - rptr_v + wptr_v;
  }

  return depth;
}

/*
 * Increment pointer, zero and flip phase if it gets to size
 */
uint32_t ptr_inc(uint32_t ptr, uint32_t inc, uint32_t size) {
  uint32_t phase = ptr & SPI_DEVICE_BUFFER_SIZE_BYTES;
  ptr = (ptr & (SPI_DEVICE_BUFFER_SIZE_BYTES - 1)) + inc;
  if (ptr >= size) {
    ptr -= size;
    phase ^= SPI_DEVICE_BUFFER_SIZE_BYTES;
  }
  return ptr | phase;
}

static int word_aligned(void *p) { return (((int)p & 0x3) == 0); }

/**
 * Send data over SPI
 *
 * @param data pointer to buffer of uint_8 to send
 * @param len_bytes number of bytes to send
 * @return number of bytes actually sent (<len if no space in the fifo)
 */
size_t spid_send(void *data, size_t len_bytes) {
  uint32_t txf_ptr, txf_wptr, txf_rptr;
  uint32_t fifo_inuse_bytes;
  uint32_t msg_length_bytes;

  /* Check if TXF has enough space */
  txf_ptr = REG32(SPI_DEVICE_TXF_PTR(0));
  txf_wptr = (txf_ptr >> SPI_DEVICE_TXF_PTR_WPTR_OFFSET) &
             SPI_DEVICE_TXF_PTR_WPTR_MASK;
  txf_rptr = (txf_ptr >> SPI_DEVICE_TXF_PTR_RPTR_OFFSET) &
             SPI_DEVICE_TXF_PTR_RPTR_MASK;

  fifo_inuse_bytes = calc_depth(txf_wptr, txf_rptr, SPID_TXF_SIZE);

  // Reserve the last 4 bytes in the fifo so it is always safe
  // to write 32-bit words
  if (len_bytes < SPID_TXF_SIZE - fifo_inuse_bytes - 4) {
    // Safe to send all data
    msg_length_bytes = len_bytes;
  } else {
    msg_length_bytes = SPID_TXF_SIZE - fifo_inuse_bytes - 4;
  }
  int tocopy = msg_length_bytes;

  // Aligned case can just copy words
  if (word_aligned(data) && word_aligned((void *)txf_wptr)) {
    uint32_t *data_w = (uint32_t *)data;
    while (tocopy > 0) {
      ACCESS32_TXFPTR(txf_wptr) = *data_w++;
      if (tocopy >= 4) {
        txf_wptr = ptr_inc(txf_wptr, 4, SPID_TXF_SIZE);
        tocopy -= 4;
      } else {
        txf_wptr = ptr_inc(txf_wptr, tocopy, SPID_TXF_SIZE);
        tocopy = 0;  // tocopy -= tocopy always gives zero
      }
    }
  } else {
    // preserve data if unaligned start
    uint8_t *data_b = (uint8_t *)data;
    uint32_t d = ACCESS32_TXFPTR(txf_wptr);
    while (tocopy > 0) {
      int shift = (txf_wptr & 0x3) * 8;
      uint32_t mask = 0xff << shift;
      d = (d & ~mask) | (*data_b++ << shift);
      if ((txf_wptr & 0x3) == 0x3) {
        ACCESS32_TXFPTR(txf_wptr) = d;
      }
      txf_wptr = ptr_inc(txf_wptr, 1, SPID_TXF_SIZE);
      tocopy--;
    }
  }

  // Write pointer, requires read pointer to be RO
  REG32(SPI_DEVICE_TXF_PTR(0)) = txf_wptr << SPI_DEVICE_TXF_PTR_WPTR_OFFSET;

  return msg_length_bytes;
}

/**
 * Read the amount of the data from SRAM RX FIFO
 *
 * If remained data is smaller than length, it returns only up to data
 */
size_t spid_read_nb(void *data, size_t len_bytes) {
  uint32_t rxf_ptr, rxf_wptr, rxf_rptr;
  uint32_t msg_len_bytes;

  rxf_ptr = REG32(SPI_DEVICE_RXF_PTR(0));
  rxf_wptr = (rxf_ptr >> SPI_DEVICE_RXF_PTR_WPTR_OFFSET) &
             SPI_DEVICE_RXF_PTR_WPTR_MASK;
  rxf_rptr = (rxf_ptr >> SPI_DEVICE_RXF_PTR_RPTR_OFFSET) &
             SPI_DEVICE_RXF_PTR_RPTR_MASK;

  msg_len_bytes = calc_depth(rxf_wptr, rxf_rptr, SPID_RXF_SIZE);
  if (msg_len_bytes == 0) {
    return 0;
  }
  uart_send_uint(rxf_ptr, 32);
  uart_send_char(' ');
  uart_send_uint(msg_len_bytes, 32);
  uart_send_char(' ');
  /* Check there is room for the whole buffer */
  if (msg_len_bytes > len_bytes) {
    msg_len_bytes = len_bytes;
  }

  int tocopy = msg_len_bytes;
  // Aligned case  -- which for now it always will be
  // if tocopy is not multiple of 4 then will read / write extra bytes
  // so check buffer length
  if (word_aligned(data) && ((len_bytes & 0x3) == 0) &&
      word_aligned((void *)rxf_ptr)) {
    uint32_t *data_w = (uint32_t *)data;
    while (tocopy > 0) {
      *data_w++ = READ32_RXFPTR(rxf_rptr);
      if (tocopy >= 4) {
        rxf_rptr = ptr_inc(rxf_rptr, 4, SPID_RXF_SIZE);
        tocopy -= 4;
      } else {
        rxf_rptr = ptr_inc(rxf_rptr, tocopy, SPID_RXF_SIZE);
        tocopy = 0;  // tocopy -= tocopy always gives zero
      }
    }
  } else {
    uint8_t *data_b = (uint8_t *)data;
    // Have to deal with only being able to do 32-bit accesses
    int dst = 0;
    uint32_t d = READ32_RXFPTR(rxf_rptr & ~0x3);
    while (tocopy--) {
      int boff = rxf_rptr & 0x3;
      data_b[dst++] = (d >> (boff * 8)) & 0xff;
      rxf_rptr = ptr_inc(rxf_rptr, 1, SPID_RXF_SIZE);
      if (((rxf_rptr & 0x3) == 0) && tocopy) {
        d = READ32_RXFPTR(rxf_rptr);
      }
    }
  }
  /* Update read pointer -- NB relies on write pointer being RO */
  REG32(SPI_DEVICE_RXF_PTR(0)) = rxf_rptr << SPI_DEVICE_RXF_PTR_RPTR_OFFSET;

  return msg_len_bytes;
}
