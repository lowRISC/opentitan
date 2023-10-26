// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/spi_host.h"

#include "sw/lib/sw/device/base/abs_mmio.h"
#include "sw/lib/sw/device/base/bitfield.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/silicon_creator/error.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "spi_host_regs.h"

enum {
  /**
   * Base address of the spi_host registers.
   */
  kBase = TOP_DARJEELING_SPI_HOST0_BASE_ADDR,
};

static void spi_host_reset(void) {
  // Trigger software reset.
  abs_mmio_write32(kBase + SPI_HOST_CONTROL_REG_OFFSET,
                   bitfield_bit32_write(0, SPI_HOST_CONTROL_SW_RST_BIT, true));

  // Wait for the spi host to go inactive.
  bool active;
  do {
    uint32_t reg = abs_mmio_read32(kBase + SPI_HOST_STATUS_REG_OFFSET);
    active = bitfield_bit32_read(reg, SPI_HOST_STATUS_ACTIVE_BIT);
  } while (active);

  // Wait for the spi host fifos to drain.
  uint32_t txqd, rxqd;
  do {
    uint32_t reg = abs_mmio_read32(kBase + SPI_HOST_STATUS_REG_OFFSET);
    txqd = bitfield_field32_read(reg, SPI_HOST_STATUS_TXQD_FIELD);
    rxqd = bitfield_field32_read(reg, SPI_HOST_STATUS_RXQD_FIELD);
  } while (txqd != 0 || rxqd != 0);

  // Clear the software reset request bit.
  abs_mmio_write32(kBase + SPI_HOST_CONTROL_REG_OFFSET,
                   bitfield_bit32_write(0, SPI_HOST_CONTROL_SW_RST_BIT, false));
}

static void spi_host_enable(bool enable) {
  uint32_t reg = abs_mmio_read32(kBase + SPI_HOST_CONTROL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, SPI_HOST_CONTROL_SPIEN_BIT, enable);
  reg = bitfield_bit32_write(reg, SPI_HOST_CONTROL_OUTPUT_EN_BIT, enable);
  abs_mmio_write32(kBase + SPI_HOST_CONTROL_REG_OFFSET, reg);
}

void spi_host_init(uint32_t precalculated_div) {
  spi_host_reset();

  abs_mmio_write32(kBase + SPI_HOST_CONFIGOPTS_REG_OFFSET,
                   bitfield_field32_write(0, SPI_HOST_CONFIGOPTS_CLKDIV_0_FIELD,
                                          precalculated_div));

  spi_host_enable(true);
}

static void wait_ready(void) {
  bool ready;
  do {
    uint32_t reg = abs_mmio_read32(kBase + SPI_HOST_STATUS_REG_OFFSET);
    ready = bitfield_bit32_read(reg, SPI_HOST_STATUS_READY_BIT);
  } while (!ready);
}

static void wait_tx_fifo(void) {
  uint32_t txqd;
  do {
    uint32_t reg = abs_mmio_read32(kBase + SPI_HOST_STATUS_REG_OFFSET);
    txqd = bitfield_field32_read(reg, SPI_HOST_STATUS_TXQD_FIELD);
  } while (txqd == SPI_HOST_PARAM_TX_DEPTH);
}

static void wait_rx_fifo(void) {
  uint32_t rxqd;
  do {
    uint32_t reg = abs_mmio_read32(kBase + SPI_HOST_STATUS_REG_OFFSET);
    rxqd = bitfield_field32_read(reg, SPI_HOST_STATUS_RXQD_FIELD);
  } while (rxqd == 0);
}

static inline void tx_fifo_write8(uintptr_t srcaddr) {
  uint8_t *src = (uint8_t *)srcaddr;
  wait_tx_fifo();
  abs_mmio_write8(kBase + SPI_HOST_TXDATA_REG_OFFSET, *src);
}

static inline void tx_fifo_write32(uintptr_t srcaddr) {
  uint32_t val = read_32((const void *)srcaddr);
  wait_tx_fifo();
  abs_mmio_write32(kBase + SPI_HOST_TXDATA_REG_OFFSET, val);
}

static void spi_host_fifo_write(const void *src, uint16_t len) {
  uintptr_t ptr = (uintptr_t)src;

  // If the pointer starts mis-aligned, write until we are aligned.
  while (misalignment32_of(ptr) && len > 0) {
    tx_fifo_write8(ptr);
    ptr += 1;
    len -= 1;
  }

  // Write complete 32-bit words to the fifo.
  while (len > 3) {
    tx_fifo_write32(ptr);
    ptr += 4;
    len -= 4;
  }

  // Clean up any leftover bytes.
  while (len > 0) {
    tx_fifo_write8(ptr);
    ptr += 1;
    len -= 1;
  }
}
typedef struct queue {
  int32_t length;
  uint8_t alignas(uint64_t) data[8];
} queue_t;

static void enqueue_byte(queue_t *queue, uint8_t data) {
  queue->data[queue->length++] = data;
}

static void enqueue_word(queue_t *queue, uint32_t data) {
  if (queue->length % (int32_t)sizeof(uint32_t) == 0) {
    write_32(data, queue->data + queue->length);
    queue->length += 4;
  } else {
    for (size_t i = 0; i < sizeof(uint32_t); ++i) {
      enqueue_byte(queue, (uint8_t)data);
      data >>= 8;
    }
  }
}

static uint8_t dequeue_byte(queue_t *queue) {
  uint8_t val = queue->data[0];
  uint64_t qword = read_64(queue->data);
  write_64(qword >> 8, queue->data);
  queue->length -= 1;
  return val;
}

static uint32_t dequeue_word(queue_t *queue) {
  uint32_t val = read_32(queue->data);
  write_32(read_32(queue->data + sizeof(uint32_t)), queue->data);
  queue->length -= 4;
  return val;
}

void spi_host_fifo_read(void *dst, uint16_t len) {
  uintptr_t ptr = (uintptr_t)dst;
  // We always have to read from the RXFIFO as a 32-bit word.  We use a
  // two-word queue to handle destination and length mis-alignments.
  queue_t queue = {0};

  // If the buffer is misaligned, write a byte at a time until we reach
  // alignment.
  while (misalignment32_of(ptr) && len > 0) {
    if (queue.length < 1) {
      wait_rx_fifo();
      enqueue_word(&queue, abs_mmio_read32(kBase + SPI_HOST_RXDATA_REG_OFFSET));
    }
    uint8_t *p = (uint8_t *)ptr;
    *p = dequeue_byte(&queue);
    ptr += 1;
    len -= 1;
  }

  // While we can write complete words to memory, operate on 4 bytes at a time.
  while (len > 3) {
    if (queue.length < 4) {
      wait_rx_fifo();
      enqueue_word(&queue, abs_mmio_read32(kBase + SPI_HOST_RXDATA_REG_OFFSET));
    }
    write_32(dequeue_word(&queue), (void *)ptr);
    ptr += 4;
    len -= 4;
  }

  // Finish up any left over buffer a byte at a time.
  while (len > 0) {
    if (queue.length < 1) {
      wait_rx_fifo();
      enqueue_word(&queue, abs_mmio_read32(kBase + SPI_HOST_RXDATA_REG_OFFSET));
    }
    uint8_t *p = (uint8_t *)ptr;
    *p = dequeue_byte(&queue);
    ptr += 1;
    len -= 1;
  }
}

static void write_command_reg(uint16_t length, spi_host_width_t width,
                              spi_host_direction_t direction,
                              bool last_segment) {
  uint32_t reg = 0;
  reg = bitfield_field32_write(reg, SPI_HOST_COMMAND_LEN_FIELD, length - 1);
  reg = bitfield_field32_write(reg, SPI_HOST_COMMAND_SPEED_FIELD, width);
  reg =
      bitfield_field32_write(reg, SPI_HOST_COMMAND_DIRECTION_FIELD, direction);
  reg = bitfield_bit32_write(reg, SPI_HOST_COMMAND_CSAAT_BIT, !last_segment);
  abs_mmio_write32(kBase + SPI_HOST_COMMAND_REG_OFFSET, reg);
}

static void issue_opcode(const spi_host_segment_t *segment, bool last_segment) {
  wait_tx_fifo();
  abs_mmio_write8(kBase + SPI_HOST_TXDATA_REG_OFFSET, segment->opcode.opcode);
  write_command_reg(1, segment->width, kSpiHostDirectionTx, last_segment);
}

static void issue_address(const spi_host_segment_t *segment,
                          bool last_segment) {
  wait_tx_fifo();
  // The address appears on the wire in big-endian order.
  uint32_t address = bitfield_byteswap32(segment->address.address);
  uint16_t length = 4;
  if (segment->address.mode == kSpiHostAddrMode3b) {
    length = 3;
    address >>= 8;
  }
  abs_mmio_write32(kBase + SPI_HOST_TXDATA_REG_OFFSET, address);
  write_command_reg(length, segment->width, kSpiHostDirectionTx, last_segment);
}

static void issue_dummy(const spi_host_segment_t *segment, bool last_segment) {
  if (segment->dummy.length > 0) {
    // We only want to program a dummy segment if the number of cycles is
    // greater than zero.  Programming a zero to the hardware results in a
    // dummy segment of 512 bits.
    write_command_reg((uint16_t)segment->dummy.length, segment->width,
                      kSpiHostDirectionDummy, last_segment);
  }
}

static void issue_tx(const spi_host_segment_t *segment, bool last_segment) {
  uintptr_t ptr = (uintptr_t)segment->tx.buf;
  size_t remaining = segment->tx.length;
  while (remaining) {
    size_t length = remaining > 511 ? 511 : remaining;
    spi_host_fifo_write((const void *)ptr, (uint16_t)length);
    write_command_reg((uint16_t)length, segment->width, kSpiHostDirectionTx,
                      last_segment && length == remaining);
    remaining -= length;
    ptr += length;
  }
}

static void issue_rx(const spi_host_segment_t *segment, bool last_segment) {
  uintptr_t ptr = (uintptr_t)segment->rx.buf;
  size_t remaining = segment->rx.length;
  while (remaining) {
    size_t length = remaining > 511 ? 511 : remaining;
    write_command_reg((uint16_t)length, segment->width, kSpiHostDirectionRx,
                      last_segment && length == remaining);
    spi_host_fifo_read((void *)ptr, (uint16_t)length);
    remaining -= length;
    ptr += length;
  }
}

rom_error_t spi_host_transaction(uint32_t csid,
                                 const spi_host_segment_t *segments,
                                 size_t length) {
  // Write to chip select ID.
  abs_mmio_write32(kBase + SPI_HOST_CSID_REG_OFFSET, csid);

  // For each segment, write the segment information to the
  // COMMAND register and transmit FIFO.
  for (size_t i = 0; i < length; ++i) {
    bool last_segment = i == length - 1;
    wait_ready();
    const spi_host_segment_t *segment = &segments[i];
    switch (segment->type) {
      case kSpiHostSegmentTypeOpcode:
        issue_opcode(segment, last_segment);
        break;
      case kSpiHostSegmentTypeAddress:
        issue_address(segment, last_segment);
        break;
      case kSpiHostSegmentTypeDummy:
        issue_dummy(segment, last_segment);
        break;
      case kSpiHostSegmentTypeTx:
        issue_tx(segment, last_segment);
        break;
      case kSpiHostSegmentTypeRx:
        issue_rx(segment, last_segment);
        break;
      default:
        return kErrorSpiHostInvalidArgument;
    }
  }

  return kErrorOk;
}
