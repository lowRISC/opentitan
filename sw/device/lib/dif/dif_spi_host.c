// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_spi_host.h"

#include <assert.h>
#include <stddef.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"

#include "spi_host_regs.h"  // Generated.

dif_result_t dif_spi_host_init(mmio_region_t base_addr,
                               dif_spi_host_t *spi_host) {
  spi_host->base_addr = base_addr;
  LOG_INFO("spi_host base_addr = %p", spi_host->base_addr.base);
  return kDifOk;
}

static void spi_host_reset(const dif_spi_host_t *spi_host) {
  // Set the software reset request bit.
  mmio_region_write32(
      spi_host->base_addr, SPI_HOST_CONTROL_REG_OFFSET,
      bitfield_bit32_write(0, SPI_HOST_CONTROL_SW_RST_BIT, true));

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
  mmio_region_write32(
      spi_host->base_addr, SPI_HOST_CONTROL_REG_OFFSET,
      bitfield_bit32_write(0, SPI_HOST_CONTROL_SPIEN_BIT, enable));
}

static void spi_status(const dif_spi_host_t *spi_host) {
  uint32_t ctl =
      mmio_region_read32(spi_host->base_addr, SPI_HOST_CONTROL_REG_OFFSET);
  uint32_t sts =
      mmio_region_read32(spi_host->base_addr, SPI_HOST_STATUS_REG_OFFSET);
  uint32_t err =
      mmio_region_read32(spi_host->base_addr, SPI_HOST_ERROR_STATUS_REG_OFFSET);
  LOG_INFO("control=%08x status=%08x errsts=%02x", ctl, sts, err);
}

dif_result_t dif_spi_host_configure(const dif_spi_host_t *spi_host,
                                    dif_spi_host_config_t config) {
  uint32_t divider = (kClockFreqPeripheralHz / config.spi_clock) + 1;
  LOG_INFO("divider=%d", divider);
  if (divider & ~SPI_HOST_CONFIGOPTS_CLKDIV_0_MASK) {
    return kDifBadArg;
  }
  divider = 0;

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
  spi_host_enable(spi_host, true);
  LOG_INFO("configopts=%08x", reg);
  spi_status(spi_host);
  return kDifOk;
}

static void wait_ready(const dif_spi_host_t *spi_host) {
  bool ready;
  do {
    uint32_t reg =
        mmio_region_read32(spi_host->base_addr, SPI_HOST_STATUS_REG_OFFSET);
    ready = bitfield_bit32_read(reg, SPI_HOST_STATUS_READY_BIT);
    LOG_INFO("ready=%d", ready);
  } while (!ready);
}

static void wait_tx_fifo(const dif_spi_host_t *spi_host) {
  uint32_t txqd;
  do {
    uint32_t reg =
        mmio_region_read32(spi_host->base_addr, SPI_HOST_STATUS_REG_OFFSET);
    txqd = bitfield_field32_read(reg, SPI_HOST_STATUS_TXQD_FIELD);
    LOG_INFO("txqd=%d", txqd);
  } while (txqd == 0xFF);
}

static void wait_rx_fifo(const dif_spi_host_t *spi_host) {
  uint32_t rxqd;
  do {
    uint32_t reg =
        mmio_region_read32(spi_host->base_addr, SPI_HOST_STATUS_REG_OFFSET);
    rxqd = bitfield_field32_read(reg, SPI_HOST_STATUS_RXQD_FIELD);
    // LOG_INFO("rxqd=%d", rxqd);
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
  uint32_t *src = (uint32_t *)srcaddr;
  wait_tx_fifo(spi_host);
  mmio_region_write32(spi_host->base_addr, SPI_HOST_TXDATA_REG_OFFSET, *src);
}

static void tx_fifo_write(const dif_spi_host_t *spi_host, const void *src,
                          uint16_t len) {
  uintptr_t ptr = (uintptr_t)src;

  // If the pointer starts mis-aligned, write until we are aligned.
  while (ptr & 3 && len > 0) {
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
}

typedef struct queue {
  int32_t length;
  union {
    uint64_t qword;
    uint32_t word[2];
    uint8_t byte[8];
  };
} queue_t;

#if 0
static void tx_fifo_write2(const dif_spi_host_t *spi_host, const void *src,
                           uint16_t len) {
  uintptr_t ptr = (uintptr_t)src;
  queue_t queue = {
      0,
  };

  while (ptr & 3 && len > 0) {
    queue.byte[queue.length++] = *(uint8_t *)ptr;
    ptr += 1;
    len -= 1;
  }

  while (len > 3) {
    uint32_t next = *(uint32_t *)ptr;
    if (queue.length % sizeof(uint32_t)) {
      queue.word[queue.length / sizeof(uint32_t)] = next;
      queue.length += 4;
    } else {
      queue.byte[queue.length++] = (uint8_t)next;
      next >>= 8;
      queue.byte[queue.length++] = (uint8_t)next;
      next >>= 8;
      queue.byte[queue.length++] = (uint8_t)next;
      next >>= 8;
      queue.byte[queue.length++] = (uint8_t)next;
      next >>= 8;
    }
    ptr += 4;
    len -= 4;
    if (queue.length >= 4) {
      wait_tx_fifo(spi_host);
      mmio_region_write32(spi_host->base_addr, SPI_HOST_TXDATA_REG_OFFSET,
                          queue.word[0]);
      queue.qword >>= 32;
      queue.length -= 4;
    }
  }

  while (len > 0) {
    queue.byte[queue.length++] = *(uint8_t *)ptr;
    ptr += 1;
    len -= 1;
  }
  while (queue.length > 0) {
    wait_tx_fifo(spi_host);
    mmio_region_write32(spi_host->base_addr, SPI_HOST_TXDATA_REG_OFFSET,
                        queue.word[0]);
    queue.qword >>= 32;
    queue.length -= 4;
  }
}
#endif

static void rx_fifo_read(const dif_spi_host_t *spi_host, void *dst,
                         uint16_t len) {
  uint32_t *ptr = (uint32_t *)dst;

  LOG_INFO("rx_fifo_read(%p, %d)", ptr, len);
  spi_status(spi_host);

  // FIXME: do something more clever to deal with a possibly misaligned starting
  // address;
  while (len > 3) {
    wait_rx_fifo(spi_host);
    uint32_t data =
        mmio_region_read32(spi_host->base_addr, SPI_HOST_RXDATA_REG_OFFSET);
    *ptr = data;
    ptr += 1;
    len -= 4;
    LOG_INFO("rx=%08x len=%d", data, len);
  }
  if (len > 0) {
    wait_rx_fifo(spi_host);
    uint32_t data =
        mmio_region_read32(spi_host->base_addr, SPI_HOST_RXDATA_REG_OFFSET);
    uint8_t *byte = (uint8_t *)ptr;
    while (len > 0) {
      *byte = (uint8_t)data;
      byte += 1;
      len -= 1;
      data >>= 8;
    }
  }
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
  LOG_INFO("command_reg=%08x", reg);
  mmio_region_write32(spi_host->base_addr, SPI_HOST_COMMAND_REG_OFFSET, reg);
}

static void issue_opcode(const dif_spi_host_t *spi_host,
                         dif_spi_host_segment_t *segment, bool last_segment) {
  LOG_INFO("issue_opcode=%02x", segment->opcode);
  wait_tx_fifo(spi_host);
  mmio_region_write8(spi_host->base_addr, SPI_HOST_TXDATA_REG_OFFSET,
                     segment->opcode);
  write_command_reg(spi_host, 1, kDifSpiHostWidthStandard,
                    kDifSpiHostDirectionTx, last_segment);
}

static void issue_address(const dif_spi_host_t *spi_host,
                          dif_spi_host_segment_t *segment, bool last_segment) {
  LOG_INFO("issue_address=%08x", segment->address.address);
  wait_tx_fifo(spi_host);
  uint32_t address = bitfield_byteswap32(segment->address.address);
  uint32_t length;
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
  LOG_INFO("issue_address length=%d", length);
  write_command_reg(spi_host, length, segment->address.width,
                    kDifSpiHostDirectionTx, last_segment);
}

static void issue_dummy(const dif_spi_host_t *spi_host,
                        dif_spi_host_segment_t *segment, bool last_segment) {
  LOG_INFO("issue_dummy=%d", segment->dummy.length);
  write_command_reg(spi_host, segment->dummy.length, segment->dummy.width,
                    kDifSpiHostDirectionDummy, last_segment);
}

static void issue_data_phase(const dif_spi_host_t *spi_host,
                             dif_spi_host_segment_t *segment,
                             bool last_segment) {
  size_t length;
  dif_spi_host_width_t width;
  dif_spi_host_direction_t direction;

  switch (segment->type) {
    case kDifSpiHostSegmentTypeTx:
      LOG_INFO("issue_data_phase txlen=%d", segment->tx.length);
      width = segment->tx.width;
      length = segment->tx.length;
      direction = kDifSpiHostDirectionTx;
      tx_fifo_write(spi_host, segment->tx.buf, segment->tx.length);
      break;
    case kDifSpiHostSegmentTypeBidirectional:
      LOG_INFO("issue_data_phase bidirlen=%d", segment->bidir.length);
      width = segment->bidir.width;
      length = segment->bidir.length;
      direction = kDifSpiHostDirectionBidirectional;
      tx_fifo_write(spi_host, segment->bidir.txbuf, segment->bidir.length);
      break;
    case kDifSpiHostSegmentTypeRx:
      LOG_INFO("issue_data_phase rxlen=%d", segment->rx.length);
      width = segment->rx.width;
      length = segment->rx.length;
      direction = kDifSpiHostDirectionRx;
      break;
    default:
      // Error
      return;
  }
  write_command_reg(spi_host, length, width, direction, last_segment);
}

dif_result_t dif_spi_host_start(const dif_spi_host_t *spi_host,
                                dif_spi_host_transaction_t *transaction) {
  // Write to chip select ID.
  mmio_region_write32(spi_host->base_addr, SPI_HOST_CSID_REG_OFFSET,
                      transaction->csid);

  // For each segment, write the segment information to the
  // COMMAND register and transmit FIFO.
  for (size_t i = 0; i < transaction->length; ++i) {
    bool last_segment = i == transaction->length - 1;
    wait_ready(spi_host);
    dif_spi_host_segment_t *segment = &transaction->segments[i];
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
        FALLTHROUGH_INTENDED;
      case kDifSpiHostSegmentTypeRx:
        FALLTHROUGH_INTENDED;
      case kDifSpiHostSegmentTypeBidirectional:
        issue_data_phase(spi_host, segment, last_segment);
        break;
    }
    spi_status(spi_host);
  }

  LOG_INFO("rx phase");
  // For each segment which receives data, read from the receive FIFO.
  for (size_t i = 0; i < transaction->length; ++i) {
    dif_spi_host_segment_t *segment = &transaction->segments[i];
    switch (segment->type) {
      case kDifSpiHostSegmentTypeRx:
        rx_fifo_read(spi_host, segment->rx.buf, segment->rx.length);
        break;
      case kDifSpiHostSegmentTypeBidirectional:
        rx_fifo_read(spi_host, segment->bidir.rxbuf, segment->bidir.length);
        break;
      default:
          /* do nothing */;
    }
  }
  return kDifOk;
}
