// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_spi_host.h"

#include <assert.h>
#include <stdalign.h>
#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"

#include "spi_host_regs.h"  // Generated.

// We create weak symbol aliases for the FIFO write and read functions so the
// unit tests can provide mocks.  The mocks provide for separate testing of
// the FIFO functions and the overall transaction management functions.
OT_WEAK
OT_ALIAS("dif_spi_host_fifo_write")
dif_result_t spi_host_fifo_write_alias(const dif_spi_host_t *spi_host,
                                       const void *src, uint16_t len);

OT_WEAK
OT_ALIAS("dif_spi_host_fifo_read")
dif_result_t spi_host_fifo_read_alias(const dif_spi_host_t *spi_host, void *dst,
                                      uint16_t len);

static void spi_host_reset(const dif_spi_host_t *spi_host) {
  // Set the software reset request bit.
  uint32_t reg =
      mmio_region_read32(spi_host->base_addr, SPI_HOST_CONTROL_REG_OFFSET);
  mmio_region_write32(
      spi_host->base_addr, SPI_HOST_CONTROL_REG_OFFSET,
      bitfield_bit32_write(reg, SPI_HOST_CONTROL_SW_RST_BIT, true));

  // Wait for the spi host to go inactive.
  bool active;
  do {
    uint32_t reg =
        mmio_region_read32(spi_host->base_addr, SPI_HOST_STATUS_REG_OFFSET);
    active = bitfield_bit32_read(reg, SPI_HOST_STATUS_ACTIVE_BIT);
  } while (active);

  // Wait for the spi host fifos to drain.
  uint32_t txqd, rxqd;
  do {
    uint32_t reg =
        mmio_region_read32(spi_host->base_addr, SPI_HOST_STATUS_REG_OFFSET);
    txqd = bitfield_field32_read(reg, SPI_HOST_STATUS_TXQD_FIELD);
    rxqd = bitfield_field32_read(reg, SPI_HOST_STATUS_RXQD_FIELD);
  } while (txqd != 0 || rxqd != 0);

  // Clear the software reset request bit.
  mmio_region_write32(
      spi_host->base_addr, SPI_HOST_CONTROL_REG_OFFSET,
      bitfield_bit32_write(0, SPI_HOST_CONTROL_SW_RST_BIT, false));
}

static void spi_host_enable(const dif_spi_host_t *spi_host, bool enable) {
  uint32_t reg =
      mmio_region_read32(spi_host->base_addr, SPI_HOST_CONTROL_REG_OFFSET);
  mmio_region_write32(
      spi_host->base_addr, SPI_HOST_CONTROL_REG_OFFSET,
      bitfield_bit32_write(reg, SPI_HOST_CONTROL_SPIEN_BIT, enable));
}

dif_result_t dif_spi_host_configure(const dif_spi_host_t *spi_host,
                                    dif_spi_host_config_t config) {
  if (spi_host == NULL) {
    return kDifBadArg;
  }
  if (config.peripheral_clock_freq_hz == 0 || config.spi_clock == 0) {
    return kDifBadArg;
  }

  uint32_t divider =
      ((config.peripheral_clock_freq_hz / config.spi_clock) / 2) - 1;
  if (divider & ~(uint32_t)SPI_HOST_CONFIGOPTS_CLKDIV_0_MASK) {
    return kDifBadArg;
  }

  spi_host_reset(spi_host);
  uint32_t reg = 0;
  reg =
      bitfield_field32_write(reg, SPI_HOST_CONFIGOPTS_CLKDIV_0_FIELD, divider);
  reg = bitfield_field32_write(reg, SPI_HOST_CONFIGOPTS_CSNIDLE_0_FIELD,
                               config.chip_select.idle);
  reg = bitfield_field32_write(reg, SPI_HOST_CONFIGOPTS_CSNTRAIL_0_FIELD,
                               config.chip_select.trail);
  reg = bitfield_field32_write(reg, SPI_HOST_CONFIGOPTS_CSNLEAD_0_FIELD,
                               config.chip_select.lead);
  reg = bitfield_bit32_write(reg, SPI_HOST_CONFIGOPTS_FULLCYC_0_BIT,
                             config.full_cycle);
  reg = bitfield_bit32_write(reg, SPI_HOST_CONFIGOPTS_CPHA_0_BIT, config.cpha);
  reg = bitfield_bit32_write(reg, SPI_HOST_CONFIGOPTS_CPOL_0_BIT, config.cpol);
  mmio_region_write32(spi_host->base_addr, SPI_HOST_CONFIGOPTS_REG_OFFSET, reg);

  reg = mmio_region_read32(spi_host->base_addr, SPI_HOST_CONTROL_REG_OFFSET);
  reg = bitfield_field32_write(reg, SPI_HOST_CONTROL_TX_WATERMARK_FIELD,
                               config.tx_watermark);
  reg = bitfield_field32_write(reg, SPI_HOST_CONTROL_RX_WATERMARK_FIELD,
                               config.rx_watermark);
  mmio_region_write32(spi_host->base_addr, SPI_HOST_CONTROL_REG_OFFSET, reg);

  spi_host_enable(spi_host, true);
  return kDifOk;
}

dif_result_t dif_spi_host_output_set_enabled(const dif_spi_host_t *spi_host,
                                             bool enabled) {
  if (spi_host == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(spi_host->base_addr, SPI_HOST_CONTROL_REG_OFFSET);
  mmio_region_write32(
      spi_host->base_addr, SPI_HOST_CONTROL_REG_OFFSET,
      bitfield_bit32_write(reg, SPI_HOST_CONTROL_OUTPUT_EN_BIT, enabled));

  return kDifOk;
}

static void wait_ready(const dif_spi_host_t *spi_host) {
  bool ready;
  do {
    uint32_t reg =
        mmio_region_read32(spi_host->base_addr, SPI_HOST_STATUS_REG_OFFSET);
    ready = bitfield_bit32_read(reg, SPI_HOST_STATUS_READY_BIT);
  } while (!ready);
}

static void wait_tx_fifo(const dif_spi_host_t *spi_host) {
  uint32_t txqd;
  do {
    uint32_t reg =
        mmio_region_read32(spi_host->base_addr, SPI_HOST_STATUS_REG_OFFSET);
    txqd = bitfield_field32_read(reg, SPI_HOST_STATUS_TXQD_FIELD);
  } while (txqd == SPI_HOST_PARAM_TX_DEPTH);
}

static void wait_rx_fifo(const dif_spi_host_t *spi_host) {
  uint32_t rxqd;
  do {
    uint32_t reg =
        mmio_region_read32(spi_host->base_addr, SPI_HOST_STATUS_REG_OFFSET);
    rxqd = bitfield_field32_read(reg, SPI_HOST_STATUS_RXQD_FIELD);
  } while (rxqd == 0);
}

static inline void tx_fifo_write8(const dif_spi_host_t *spi_host,
                                  uintptr_t srcaddr) {
  uint8_t *src = (uint8_t *)srcaddr;
  wait_tx_fifo(spi_host);
  mmio_region_write8(spi_host->base_addr, SPI_HOST_TXDATA_REG_OFFSET, *src);
}

static inline void tx_fifo_write32(const dif_spi_host_t *spi_host,
                                   uintptr_t srcaddr) {
  wait_tx_fifo(spi_host);
  uint32_t val = read_32((const void *)srcaddr);
  mmio_region_write32(spi_host->base_addr, SPI_HOST_TXDATA_REG_OFFSET, val);
}

dif_result_t dif_spi_host_fifo_write(const dif_spi_host_t *spi_host,
                                     const void *src, uint16_t len) {
  uintptr_t ptr = (uintptr_t)src;
  if (spi_host == NULL || (src == NULL && len > 0)) {
    return kDifBadArg;
  }

  // If the pointer starts mis-aligned, write until we are aligned.
  while (misalignment32_of(ptr) && len > 0) {
    tx_fifo_write8(spi_host, ptr);
    ptr += 1;
    len -= 1;
  }

  // Write complete 32-bit words to the fifo.
  while (len > 3) {
    tx_fifo_write32(spi_host, ptr);
    ptr += 4;
    len -= 4;
  }

  // Clean up any leftover bytes.
  while (len > 0) {
    tx_fifo_write8(spi_host, ptr);
    ptr += 1;
    len -= 1;
  }

  return kDifOk;
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

dif_result_t dif_spi_host_fifo_read(const dif_spi_host_t *spi_host, void *dst,
                                    uint16_t len) {
  if (spi_host == NULL || (dst == NULL && len > 0)) {
    return kDifBadArg;
  }

  uintptr_t ptr = (uintptr_t)dst;
  // We always have to read from the RXFIFO as a 32-bit word.  We use a
  // two-word queue to handle destination and length mis-alignments.
  queue_t queue = {0};

  // If the buffer is misaligned, write a byte at a time until we reach
  // alignment.
  while (misalignment32_of(ptr) && len > 0) {
    if (queue.length < 1) {
      wait_rx_fifo(spi_host);
      enqueue_word(&queue, mmio_region_read32(spi_host->base_addr,
                                              SPI_HOST_RXDATA_REG_OFFSET));
    }
    uint8_t *p = (uint8_t *)ptr;
    *p = dequeue_byte(&queue);
    ptr += 1;
    len -= 1;
  }

  // While we can write complete words to memory, operate on 4 bytes at a time.
  while (len > 3) {
    if (queue.length < 4) {
      wait_rx_fifo(spi_host);
      enqueue_word(&queue, mmio_region_read32(spi_host->base_addr,
                                              SPI_HOST_RXDATA_REG_OFFSET));
    }
    write_32(dequeue_word(&queue), (void *)ptr);
    ptr += 4;
    len -= 4;
  }

  // Finish up any left over buffer a byte at a time.
  while (len > 0) {
    if (queue.length < 1) {
      wait_rx_fifo(spi_host);
      enqueue_word(&queue, mmio_region_read32(spi_host->base_addr,
                                              SPI_HOST_RXDATA_REG_OFFSET));
    }
    uint8_t *p = (uint8_t *)ptr;
    *p = dequeue_byte(&queue);
    ptr += 1;
    len -= 1;
  }

  return kDifOk;
}

static void write_command_reg(const dif_spi_host_t *spi_host, uint16_t length,
                              dif_spi_host_width_t speed,
                              dif_spi_host_direction_t direction,
                              bool last_segment) {
  uint32_t reg = 0;
  reg = bitfield_field32_write(reg, SPI_HOST_COMMAND_LEN_FIELD, length - 1);
  reg = bitfield_field32_write(reg, SPI_HOST_COMMAND_SPEED_FIELD, speed);
  reg =
      bitfield_field32_write(reg, SPI_HOST_COMMAND_DIRECTION_FIELD, direction);
  reg = bitfield_bit32_write(reg, SPI_HOST_COMMAND_CSAAT_BIT, !last_segment);
  mmio_region_write32(spi_host->base_addr, SPI_HOST_COMMAND_REG_OFFSET, reg);
}

static void issue_opcode(const dif_spi_host_t *spi_host,
                         dif_spi_host_segment_t *segment, bool last_segment) {
  wait_tx_fifo(spi_host);
  mmio_region_write8(spi_host->base_addr, SPI_HOST_TXDATA_REG_OFFSET,
                     segment->opcode);
  write_command_reg(spi_host, 1, kDifSpiHostWidthStandard,
                    kDifSpiHostDirectionTx, last_segment);
}

static void issue_address(const dif_spi_host_t *spi_host,
                          dif_spi_host_segment_t *segment, bool last_segment) {
  wait_tx_fifo(spi_host);
  // The address appears on the wire in big-endian order.
  uint32_t address = bitfield_byteswap32(segment->address.address);
  uint16_t length;
  if (segment->address.mode == kDifSpiHostAddrMode4b) {
    length = 4;
    mmio_region_write32(spi_host->base_addr, SPI_HOST_TXDATA_REG_OFFSET,
                        address);
  } else {
    length = 3;
    address >>= 8;
    mmio_region_write32(spi_host->base_addr, SPI_HOST_TXDATA_REG_OFFSET,
                        address);
  }
  write_command_reg(spi_host, length, segment->address.width,
                    kDifSpiHostDirectionTx, last_segment);
}

static void issue_dummy(const dif_spi_host_t *spi_host,
                        dif_spi_host_segment_t *segment, bool last_segment) {
  if (segment->dummy.length > 0) {
    // We only want to program a dummy segment if the number of cycles is
    // greater than zero.  Programming a zero to the hardware results in a
    // dummy segment of 512 bits.
    write_command_reg(spi_host, (uint16_t)segment->dummy.length,
                      segment->dummy.width, kDifSpiHostDirectionDummy,
                      last_segment);
  }
}

static dif_result_t issue_data_phase(const dif_spi_host_t *spi_host,
                                     dif_spi_host_segment_t *segment,
                                     bool last_segment) {
  size_t length;
  dif_spi_host_width_t width;
  dif_spi_host_direction_t direction;

  switch (segment->type) {
    case kDifSpiHostSegmentTypeTx:
      width = segment->tx.width;
      length = segment->tx.length;
      direction = kDifSpiHostDirectionTx;
      spi_host_fifo_write_alias(spi_host, segment->tx.buf,
                                (uint16_t)segment->tx.length);
      break;
    case kDifSpiHostSegmentTypeBidirectional:
      width = segment->bidir.width;
      length = segment->bidir.length;
      direction = kDifSpiHostDirectionBidirectional;
      spi_host_fifo_write_alias(spi_host, segment->bidir.txbuf,
                                (uint16_t)segment->bidir.length);
      break;
    case kDifSpiHostSegmentTypeRx:
      width = segment->rx.width;
      length = segment->rx.length;
      direction = kDifSpiHostDirectionRx;
      break;
    default:
      // Programming error (within this file).  We should never get here.
      // `issue_data_phase` should only get called for segment types which
      // represent a data transfer.
      return kDifBadArg;
  }
  write_command_reg(spi_host, (uint16_t)length, width, direction, last_segment);
  return kDifOk;
}

dif_result_t dif_spi_host_transaction(const dif_spi_host_t *spi_host,
                                      uint32_t csid,
                                      dif_spi_host_segment_t *segments,
                                      size_t length) {
  // Write to chip select ID.
  mmio_region_write32(spi_host->base_addr, SPI_HOST_CSID_REG_OFFSET, csid);

  // For each segment, write the segment information to the
  // COMMAND register and transmit FIFO.
  for (size_t i = 0; i < length; ++i) {
    bool last_segment = i == length - 1;
    wait_ready(spi_host);
    dif_spi_host_segment_t *segment = &segments[i];
    switch (segment->type) {
      case kDifSpiHostSegmentTypeOpcode:
        issue_opcode(spi_host, segment, last_segment);
        break;
      case kDifSpiHostSegmentTypeAddress:
        issue_address(spi_host, segment, last_segment);
        break;
      case kDifSpiHostSegmentTypeDummy:
        issue_dummy(spi_host, segment, last_segment);
        break;
      case kDifSpiHostSegmentTypeTx:
      case kDifSpiHostSegmentTypeRx:
      case kDifSpiHostSegmentTypeBidirectional: {
        dif_result_t error = issue_data_phase(spi_host, segment, last_segment);
        if (error != kDifOk) {
          return error;
        }
        break;
      }
      default:
        return kDifBadArg;
    }
  }

  // For each segment which receives data, read from the receive FIFO.
  for (size_t i = 0; i < length; ++i) {
    dif_spi_host_segment_t *segment = &segments[i];
    switch (segment->type) {
      case kDifSpiHostSegmentTypeRx:
        spi_host_fifo_read_alias(spi_host, segment->rx.buf,
                                 (uint16_t)segment->rx.length);
        break;
      case kDifSpiHostSegmentTypeBidirectional:
        spi_host_fifo_read_alias(spi_host, segment->bidir.rxbuf,
                                 (uint16_t)segment->bidir.length);
        break;
      default:
          /* do nothing */;
    }
  }
  return kDifOk;
}

dif_result_t dif_spi_host_event_set_enabled(const dif_spi_host_t *spi_host,
                                            dif_spi_host_events_t event,
                                            bool enable) {
  if (spi_host == NULL || (event & ~(uint32_t)kDifSpiHostEvtAll) != 0) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(spi_host->base_addr, SPI_HOST_EVENT_ENABLE_REG_OFFSET);
  if (enable) {
    reg |= event;
  } else {
    reg &= ~event;
  }
  mmio_region_write32(spi_host->base_addr, SPI_HOST_EVENT_ENABLE_REG_OFFSET,
                      reg);
  return kDifOk;
}

dif_result_t dif_spi_host_event_get_enabled(const dif_spi_host_t *spi_host,
                                            dif_spi_host_events_t *events) {
  if (spi_host == NULL || events == NULL) {
    return kDifBadArg;
  }

  *events =
      mmio_region_read32(spi_host->base_addr, SPI_HOST_EVENT_ENABLE_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_spi_host_get_status(const dif_spi_host_t *spi_host,
                                     dif_spi_host_status_t *status) {
  if (spi_host == NULL || status == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(spi_host->base_addr, SPI_HOST_STATUS_REG_OFFSET);

  status->ready = bitfield_bit32_read(reg, SPI_HOST_STATUS_READY_BIT);
  status->active = bitfield_bit32_read(reg, SPI_HOST_STATUS_ACTIVE_BIT);
  status->tx_empty = bitfield_bit32_read(reg, SPI_HOST_STATUS_TXEMPTY_BIT);
  status->rx_empty = bitfield_bit32_read(reg, SPI_HOST_STATUS_RXEMPTY_BIT);
  status->tx_full = bitfield_bit32_read(reg, SPI_HOST_STATUS_TXFULL_BIT);
  status->rx_full = bitfield_bit32_read(reg, SPI_HOST_STATUS_RXFULL_BIT);
  status->tx_water_mark = bitfield_bit32_read(reg, SPI_HOST_STATUS_TXWM_BIT);
  status->rx_water_mark = bitfield_bit32_read(reg, SPI_HOST_STATUS_RXWM_BIT);
  status->tx_stall = bitfield_bit32_read(reg, SPI_HOST_STATUS_TXSTALL_BIT);
  status->rx_stall = bitfield_bit32_read(reg, SPI_HOST_STATUS_RXSTALL_BIT);
  status->least_significant_first =
      bitfield_bit32_read(reg, SPI_HOST_STATUS_BYTEORDER_BIT);
  status->tx_queue_depth =
      bitfield_field32_read(reg, SPI_HOST_STATUS_TXQD_FIELD);
  status->rx_queue_depth =
      bitfield_field32_read(reg, SPI_HOST_STATUS_RXQD_FIELD);
  status->cmd_queue_depth =
      bitfield_field32_read(reg, SPI_HOST_STATUS_CMDQD_FIELD);

  return kDifOk;
}

dif_result_t dif_spi_host_write_command(const dif_spi_host_t *spi_host,
                                        uint16_t length,
                                        dif_spi_host_width_t speed,
                                        dif_spi_host_direction_t direction,
                                        bool last_segment) {
  if (spi_host == NULL) {
    return kDifBadArg;
  }
  write_command_reg(spi_host, length, speed, direction, last_segment);
  return kDifOk;
}

dif_result_t dif_spi_host_error_set_enabled(const dif_spi_host_t *spi_host,
                                            dif_spi_host_errors_t error,
                                            bool enable) {
  if (spi_host == NULL || (error & ~(uint32_t)kDifSpiHostIrqErrorAll) != 0) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(spi_host->base_addr, SPI_HOST_ERROR_ENABLE_REG_OFFSET);
  if (enable) {
    reg |= error;
  } else {
    reg &= ~error;
  }
  mmio_region_write32(spi_host->base_addr, SPI_HOST_ERROR_ENABLE_REG_OFFSET,
                      reg);
  return kDifOk;
}

dif_result_t dif_spi_host_error_get_enabled(const dif_spi_host_t *spi_host,
                                            dif_spi_host_errors_t *errors) {
  if (spi_host == NULL || errors == NULL) {
    return kDifBadArg;
  }

  *errors =
      mmio_region_read32(spi_host->base_addr, SPI_HOST_ERROR_ENABLE_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_spi_host_get_error(const dif_spi_host_t *spi_host,
                                    dif_spi_host_errors_t *error) {
  if (spi_host == NULL || error == NULL) {
    return kDifBadArg;
  }

  *error =
      mmio_region_read32(spi_host->base_addr, SPI_HOST_ERROR_STATUS_REG_OFFSET);

  return kDifOk;
}
