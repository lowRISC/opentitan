// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_spi_device.h"

#include "spi_device_regs.h"  // Generated.

// This is a hack to get the SPI offsets out of regs.h.
// DO NOT MERGE.
#define SPI_DEVICE0_BASE_ADDR 0x0
#define SPI_DEVICE_CONTROL_REG SPI_DEVICE_CONTROL(0)
#define SPI_DEVICE_CFG_REG SPI_DEVICE_CFG(0)
#define SPI_DEVICE_RXF_ADDR_REG SPI_DEVICE_RXF_ADDR(0)
#define SPI_DEVICE_TXF_ADDR_REG SPI_DEVICE_TXF_ADDR(0)

#define SPI_DEVICE_RXF_PTR_REG SPI_DEVICE_RXF_PTR(0)
#define SPI_DEVICE_TXF_PTR_REG SPI_DEVICE_TXF_PTR(0)

#define SPI_DEVICE_BUFFER_REG SPI_DEVICE_BUFFER(0)

// Converts a FIFO pointer into an offset from a base register address.
// To convert a FIFO pointer, one must:
// - Remove the phase bit, and the least significant two bits (so that it is
//   word-aligned).
// - Use that as an offset from the respective RXF/TXF buffer, with itself is
//   offset from the SPI device's shared buffer.
//
// The resulting formula, when used as an offset in |reg32_read()| or
// |reg32_write()|, is
//   base_addr + spi_buffer_offset +
//   (rx/tx)_buffer_offset + align(ptr_value, 4).
#define SPI_DEVICE_RXF_OFFSET(ptr) \
  (SPI_DEVICE_BUFFER_REG + SPI_DEVICE_RXF_BASE + ((ptr)&VALUE_MASK & ~0b11))
#define SPI_DEVICE_TXF_OFFSET(ptr) \
  (SPI_DEVICE_BUFFER_REG + SPI_DEVICE_TXF_BASE + ((ptr)&VALUE_MASK & ~0b11))

// RX FIFO SRAM range, given as an inclusive, word-aligned byte range.
// |SPI_DEVICE_RXF_SIZE| is the number of bytes in this range.
#define SPI_DEVICE_RXF_BASE 0x000
#define SPI_DEVICE_RXF_END 0x3ff
#define SPI_DEVICE_RXF_SIZE (SPI_DEVICE_RXF_END - SPI_DEVICE_RXF_BASE + 1)

// TX FIFO SRAM range, given as an inclusive, word-aligned byte range.
// |SPI_DEVICE_TXF_SIZE| is the number of bytes in this range.
#define SPI_DEVICE_TXF_BASE 0x600
#define SPI_DEVICE_TXF_END 0x7ff
#define SPI_DEVICE_TXF_SIZE (SPI_DEVICE_TXF_END - SPI_DEVICE_TXF_BASE + 1)

// Masks off the "phase" bit from a FIFO pointer. The phase bit is used to track
// whether a pair of pointers in a ring buffer are leading or trailing each
// other; when the phase is different, the valid area wraps around past the end
// of the buffer.
//
// See |fifo_depth()| for more information.
#define PHASE_MASK (SPI_DEVICE_BUFFER_SIZE_BYTES)

// Masks off the "value" bits from a FIFO. The value bits are actual offsets
// within the FIFO buffer.
#define VALUE_MASK (SPI_DEVICE_BUFFER_SIZE_BYTES - 1)

void dif_spi_device_init(dif_spi_device_config_t config,
                         dif_spi_device_t *spi_out) {
  // Reset the abort bit, to cause the SPI device to trash all pending
  // sends/recvs.
  reg32_clear_bit(config.base_addr, SPI_DEVICE_CONTROL_REG,
                  SPI_DEVICE_CONTROL_ABORT);

  uint32_t device_config = 0;
  // Set clock polarity to positive-edge latch.
  device_config |= 0x0 << SPI_DEVICE_CFG_CPOL;
  // Set data phase to negative-edge change.
  device_config |= 0x0 << SPI_DEVICE_CFG_CPHA;
  // Set TX order to MSB-to-LSB.
  device_config |= 0x0 << SPI_DEVICE_CFG_TX_ORDER;
  // Set RX order to MSB-to-LSB.
  device_config |= 0x0 << SPI_DEVICE_CFG_RX_ORDER;
  // Set the RXF to tick every 63 clock edges.
  device_config |=
      0x7f & SPI_DEVICE_CFG_TIMER_V_MASK << SPI_DEVICE_CFG_TIMER_V_OFFSET;
  reg32_write(config.base_addr, SPI_DEVICE_CFG_REG, device_config);

  // Set up the range of the RXF region, inclusive.
  uint32_t rxf_addr = 0;
  rxf_addr |= (SPI_DEVICE_RXF_BASE & SPI_DEVICE_RXF_ADDR_BASE_MASK)
              << SPI_DEVICE_RXF_ADDR_BASE_OFFSET;
  rxf_addr |= (SPI_DEVICE_RXF_END & SPI_DEVICE_RXF_ADDR_LIMIT_MASK)
              << SPI_DEVICE_RXF_ADDR_LIMIT_OFFSET;
  reg32_write(config.base_addr, SPI_DEVICE_RXF_ADDR_REG, rxf_addr);

  // Set up the range of the TXF region, inclusive.
  uint32_t txf_addr = 0;
  txf_addr |= (SPI_DEVICE_TXF_BASE & SPI_DEVICE_TXF_ADDR_BASE_MASK)
              << SPI_DEVICE_TXF_ADDR_BASE_OFFSET;
  txf_addr |= (SPI_DEVICE_TXF_END & SPI_DEVICE_TXF_ADDR_LIMIT_MASK)
              << SPI_DEVICE_TXF_ADDR_LIMIT_OFFSET;
  reg32_write(config.base_addr, SPI_DEVICE_TXF_ADDR_REG, txf_addr);

  spi_out->base_addr = config.base_addr;
}

/**
 * Calculates the *depth*, or bytes-in-use of a SPI FIFO (which is implemented
 * as a ring buffer).
 *
 * If the read/write pointers are in-phase, this is just their difference; if
 * they're out-of-phase, one of the pointers has "wrapped around", so there is
 * an additional FIFO's worth of data pending.
 */
static size_t fifo_depth(uint32_t write_addr, uint32_t read_addr,
                                size_t fifo_len) {
  uint32_t write_phase = write_addr & PHASE_MASK;
  uint32_t read_phase = read_addr & PHASE_MASK;
  uint32_t write_ptr_val = write_addr & VALUE_MASK;
  uint32_t read_ptr_val = read_addr & VALUE_MASK;

  // This represents the case where the valid data of the fifo is "inclusive",
  // i.e., the buffer looks like (where a / represents valid data):
  // [ /////       ]
  //   ^    ^
  //   read write
  if (write_phase == read_phase) {
    return write_ptr_val - read_ptr_val;
  }

  // This represents the case where the valid data of the fifo is "exclusive",
  // i.e., the buffer looks like (where a / represents valid data):
  // [/      //////]
  //   ^     ^
  //   write read
  return fifo_len - (read_ptr_val - write_ptr_val);
}

/**
 * Increments the FIFO address pointed to by |addr| by |increment|.
 *
 * If the pointer would wrap around the FIFO buffer, it gets wrapped and the
 * phase bit is flipped, since this causes the FIFO to switch between
 * "inclusive" and "exclusive" modes (see |fifo_depth()| above).
 *
 * A fifo pointer can be approximated by a 12-bit sign-and-magnitude integer.
 */
static void fifo_increment(uint32_t *addr, uint32_t increment,
                                  size_t fifo_len) {
  uint32_t phase_bit = *addr & PHASE_MASK;
  uint32_t inc_ptr = (*addr & VALUE_MASK) + increment;

  // If we would overflow, wrap and flip the sign bit.
  if (inc_ptr >= fifo_len) {
    inc_ptr = (inc_ptr - fifo_len) & VALUE_MASK;
    phase_bit = ~phase_bit & PHASE_MASK;
  }

  *addr = inc_ptr | phase_bit;
}

#define IS_WORD_ALIGNED(addr) (((uintptr_t)(addr)&0b11) == 0)

size_t dif_spi_device_send(const dif_spi_device_t *spi, const void *data,
                           size_t len) {
  uint32_t txf_ptr = reg32_read(spi->base_addr, SPI_DEVICE_TXF_PTR_REG);
  uint32_t txf_write_addr = (txf_ptr >> SPI_DEVICE_TXF_PTR_WPTR_OFFSET) &
                            SPI_DEVICE_TXF_PTR_WPTR_MASK;
  uint32_t txf_read_addr = (txf_ptr >> SPI_DEVICE_TXF_PTR_RPTR_OFFSET) &
                           SPI_DEVICE_TXF_PTR_RPTR_MASK;

  size_t fifo_in_use_len =
      fifo_depth(txf_write_addr, txf_read_addr, SPI_DEVICE_TXF_SIZE);
  size_t space_left = SPI_DEVICE_TXF_SIZE - fifo_in_use_len - sizeof(uint32_t);

  size_t message_len;
  if (len < space_left) {
    message_len = len;
  } else {
    message_len = space_left;
  }

  size_t bytes_left = message_len;

  // First, bring txf_write into word-alignment, so we can do full-word writes.
  if (!IS_WORD_ALIGNED(txf_write_addr)) {
    // Pull off the sub-word indexing in txf_write_addr.
    size_t misalignment = txf_write_addr & (sizeof(uint32_t) - 1);
    size_t needed_bytes = sizeof(uint32_t) - misalignment;
    if (needed_bytes > bytes_left) {
      needed_bytes = bytes_left;
    }

    uint32_t value =
        reg32_read(spi->base_addr, SPI_DEVICE_TXF_OFFSET(txf_write_addr));
    __builtin_memcpy(((uint8_t *)&value) + misalignment, data, needed_bytes);
    reg32_write(spi->base_addr, SPI_DEVICE_TXF_OFFSET(txf_write_addr), value);

    fifo_increment(&txf_write_addr, needed_bytes, SPI_DEVICE_TXF_SIZE);
    data += needed_bytes;
    bytes_left -= needed_bytes;
  }

  // Now we can treat txf_write_addr as being word-aligned, assuming we have
  // data left to write.
  while (bytes_left != 0) {
    size_t bytes_to_copy =
        bytes_left < sizeof(uint32_t) ? bytes_left : sizeof(uint32_t);

    uint32_t value = 0;
    __builtin_memcpy(&value, data, bytes_to_copy);
    reg32_write(spi->base_addr, SPI_DEVICE_TXF_OFFSET(txf_write_addr), value);

    fifo_increment(&txf_write_addr, bytes_to_copy, SPI_DEVICE_TXF_SIZE);
    data += bytes_to_copy;
    bytes_left -= bytes_to_copy;
  }

  // Write the new positions of the FIFO pointers to the pointer register.
  uint32_t new_txf_ptr = 0;
  new_txf_ptr |= txf_write_addr << SPI_DEVICE_TXF_PTR_WPTR_OFFSET;
  new_txf_ptr |= txf_read_addr << SPI_DEVICE_TXF_PTR_RPTR_OFFSET;
  reg32_write(spi->base_addr, SPI_DEVICE_TXF_PTR_REG, new_txf_ptr);

  return message_len;
}

size_t dif_spi_device_recv(const dif_spi_device_t *spi, void *buf, size_t len) {
  uint32_t rxf_ptr = reg32_read(spi->base_addr, SPI_DEVICE_RXF_PTR_REG);
  uint32_t rxf_write_addr = (rxf_ptr >> SPI_DEVICE_RXF_PTR_WPTR_OFFSET) &
                            SPI_DEVICE_RXF_PTR_WPTR_MASK;
  uint32_t rxf_read_addr = (rxf_ptr >> SPI_DEVICE_RXF_PTR_RPTR_OFFSET) &
                           SPI_DEVICE_RXF_PTR_RPTR_MASK;

  size_t fifo_in_use_len =
      fifo_depth(rxf_write_addr, rxf_read_addr, SPI_DEVICE_RXF_SIZE);

  if (fifo_in_use_len == 0) {
    return 0;
  }

  size_t message_len = fifo_in_use_len > len ? len : fifo_in_use_len;
  size_t bytes_left = message_len;

  // First, bring rxf_read into word alignment, so that we can do full-word
  // reads later.
  if (!IS_WORD_ALIGNED(rxf_read_addr)) {
    size_t misalignment = rxf_read_addr & 0b11;
    size_t needed_bytes = sizeof(uint32_t) - misalignment;
    if (needed_bytes > bytes_left) {
      needed_bytes = bytes_left;
    }

    uint32_t value =
        reg32_read(spi->base_addr, SPI_DEVICE_RXF_OFFSET(rxf_read_addr));
    __builtin_memcpy(buf, ((char *)&value) + misalignment, needed_bytes);

    fifo_increment(&rxf_write_addr, needed_bytes, SPI_DEVICE_RXF_SIZE);
    buf += needed_bytes;
    bytes_left -= needed_bytes;
  }

  // Now we can just treat rxf_read as being word-aligned, if we still have data
  // left.
  while (bytes_left != 0) {
    size_t bytes_to_copy =
        bytes_left < sizeof(uint32_t) ? bytes_left : sizeof(uint32_t);

    uint32_t value =
        reg32_read(spi->base_addr, SPI_DEVICE_RXF_OFFSET(rxf_read_addr));
    __builtin_memcpy(buf, &value, bytes_to_copy);

    fifo_increment(&rxf_write_addr, bytes_to_copy, SPI_DEVICE_TXF_SIZE);
    buf += bytes_to_copy;
    bytes_left -= bytes_to_copy;
  }

  // Set the new positions of the FIFO pointers.
  uint32_t new_rxf_ptr = 0;
  new_rxf_ptr |= rxf_write_addr << SPI_DEVICE_RXF_PTR_WPTR_OFFSET;
  new_rxf_ptr |= rxf_read_addr << SPI_DEVICE_RXF_PTR_RPTR_OFFSET;
  reg32_write(spi->base_addr, SPI_DEVICE_RXF_PTR_REG, new_rxf_ptr);

  return message_len;
}

size_t dif_spi_device_bytes_pending(const dif_spi_device_t *spi) {
  uint32_t rxf_ptr = reg32_read(spi->base_addr, SPI_DEVICE_RXF_PTR_REG);
  uint32_t rxf_write_addr = (rxf_ptr >> SPI_DEVICE_RXF_PTR_WPTR_OFFSET) &
                            SPI_DEVICE_RXF_PTR_WPTR_MASK;
  uint32_t rxf_read_addr = (rxf_ptr >> SPI_DEVICE_RXF_PTR_RPTR_OFFSET) &
                           SPI_DEVICE_RXF_PTR_RPTR_MASK;

  return fifo_depth(rxf_write_addr, rxf_read_addr, SPI_DEVICE_RXF_SIZE);
}
