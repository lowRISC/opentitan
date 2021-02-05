// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_spi_device.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "spi_device_regs.h"  // Generated.

const uint16_t kDifSpiDeviceBufferLen = SPI_DEVICE_BUFFER_SIZE_BYTES;

dif_spi_device_result_t dif_spi_device_init(dif_spi_device_params_t params,
                                            dif_spi_device_t *spi) {
  if (spi == NULL) {
    return kDifSpiDeviceBadArg;
  }

  // This ensures all other fields are zeroed.
  *spi = (dif_spi_device_t){.params = params};

  return kDifSpiDeviceOk;
}

/**
 * Computes the required value of the control register from a given
 * configuration.
 */
static uint32_t build_control_word(dif_spi_device_config_t config) {
  uint32_t val = 0;

  val =
      bitfield_bit32_write(val, SPI_DEVICE_CFG_CPOL_BIT,
                           config.clock_polarity == kDifSpiDeviceEdgeNegative);
  val = bitfield_bit32_write(val, SPI_DEVICE_CFG_CPHA_BIT,
                             config.data_phase == kDifSpiDeviceEdgePositive);
  val = bitfield_bit32_write(val, SPI_DEVICE_CFG_TX_ORDER_BIT,
                             config.tx_order == kDifSpiDeviceBitOrderLsbToMsb);
  val = bitfield_bit32_write(val, SPI_DEVICE_CFG_RX_ORDER_BIT,
                             config.rx_order == kDifSpiDeviceBitOrderLsbToMsb);
  val = bitfield_field32_write(val, SPI_DEVICE_CFG_TIMER_V_FIELD,
                               config.rx_fifo_timeout);

  return val;
}

dif_spi_device_result_t dif_spi_device_configure(
    dif_spi_device_t *spi, dif_spi_device_config_t config) {
  if (spi == NULL) {
    return kDifSpiDeviceBadArg;
  }

  // NOTE: we do not write to any registers until performing all
  // function argument checks, to avoid a halfway-configured SPI.

  uint32_t device_config = build_control_word(config);

  uint16_t rx_fifo_start = 0x0;
  uint16_t rx_fifo_end = config.rx_fifo_len - 1;
  uint16_t tx_fifo_start = rx_fifo_end + 1;
  uint16_t tx_fifo_end = tx_fifo_start + config.tx_fifo_len - 1;
  if (tx_fifo_end >= kDifSpiDeviceBufferLen) {
    // We've overflown the SRAM region...
    return kDifSpiDeviceBadArg;
  }

  uint32_t rx_fifo_bounds = 0;
  rx_fifo_bounds = bitfield_field32_write(
      rx_fifo_bounds, SPI_DEVICE_RXF_ADDR_BASE_FIELD, rx_fifo_start);
  rx_fifo_bounds = bitfield_field32_write(
      rx_fifo_bounds, SPI_DEVICE_RXF_ADDR_LIMIT_FIELD, rx_fifo_end);

  uint32_t tx_fifo_bounds = 0;
  tx_fifo_bounds = bitfield_field32_write(
      tx_fifo_bounds, SPI_DEVICE_TXF_ADDR_BASE_FIELD, tx_fifo_start);
  tx_fifo_bounds = bitfield_field32_write(
      tx_fifo_bounds, SPI_DEVICE_TXF_ADDR_LIMIT_FIELD, tx_fifo_end);

  spi->rx_fifo_len = config.rx_fifo_len;
  spi->tx_fifo_len = config.tx_fifo_len;

  mmio_region_write32(spi->params.base_addr, SPI_DEVICE_CFG_REG_OFFSET,
                      device_config);
  mmio_region_write32(spi->params.base_addr, SPI_DEVICE_RXF_ADDR_REG_OFFSET,
                      rx_fifo_bounds);
  mmio_region_write32(spi->params.base_addr, SPI_DEVICE_TXF_ADDR_REG_OFFSET,
                      tx_fifo_bounds);

  return kDifSpiDeviceOk;
}

dif_spi_device_result_t dif_spi_device_abort(const dif_spi_device_t *spi) {
  if (spi == NULL) {
    return kDifSpiDeviceBadArg;
  }

  // Set the `abort` bit, and then spin until `abort_done` is asserted.
  uint32_t reg =
      mmio_region_read32(spi->params.base_addr, SPI_DEVICE_CONTROL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CONTROL_ABORT_BIT, true);
  mmio_region_write32(spi->params.base_addr, SPI_DEVICE_CONTROL_REG_OFFSET,
                      reg);

  while (true) {
    uint32_t reg =
        mmio_region_read32(spi->params.base_addr, SPI_DEVICE_STATUS_REG_OFFSET);
    if (bitfield_bit32_read(reg, SPI_DEVICE_STATUS_ABORT_DONE_BIT)) {
      return kDifSpiDeviceOk;
    }
  }
}

DIF_WARN_UNUSED_RESULT
static bool irq_index(dif_spi_device_irq_t irq, bitfield_bit32_index_t *index) {
  switch (irq) {
    case kDifSpiDeviceIrqRxFull:
      *index = SPI_DEVICE_INTR_COMMON_RXF_BIT;
      break;
    case kDifSpiDeviceIrqRxAboveLevel:
      *index = SPI_DEVICE_INTR_COMMON_RXLVL_BIT;
      break;
    case kDifSpiDeviceIrqTxBelowLevel:
      *index = SPI_DEVICE_INTR_COMMON_TXLVL_BIT;
      break;
    case kDifSpiDeviceIrqRxError:
      *index = SPI_DEVICE_INTR_COMMON_RXERR_BIT;
      break;
    case kDifSpiDeviceIrqRxOverflow:
      *index = SPI_DEVICE_INTR_COMMON_RXOVERFLOW_BIT;
      break;
    case kDifSpiDeviceIrqTxUnderflow:
      *index = SPI_DEVICE_INTR_COMMON_TXUNDERFLOW_BIT;
      break;
    default:
      return false;
  }
  return true;
}

dif_spi_device_result_t dif_spi_device_irq_is_pending(
    const dif_spi_device_t *spi, dif_spi_device_irq_t irq, bool *is_pending) {
  if (spi == NULL || is_pending == NULL) {
    return kDifSpiDeviceBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifSpiDeviceBadArg;
  }

  uint32_t reg = mmio_region_read32(spi->params.base_addr,
                                    SPI_DEVICE_INTR_STATE_REG_OFFSET);
  *is_pending = bitfield_bit32_read(reg, index);

  return kDifSpiDeviceOk;
}

dif_spi_device_result_t dif_spi_device_irq_acknowledge(
    const dif_spi_device_t *spi, dif_spi_device_irq_t irq) {
  if (spi == NULL) {
    return kDifSpiDeviceBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifSpiDeviceBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(spi->params.base_addr, SPI_DEVICE_INTR_STATE_REG_OFFSET,
                      reg);

  return kDifSpiDeviceOk;
}

dif_spi_device_result_t dif_spi_device_irq_get_enabled(
    const dif_spi_device_t *spi, dif_spi_device_irq_t irq,
    dif_spi_device_toggle_t *state) {
  if (spi == NULL || state == NULL) {
    return kDifSpiDeviceBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifSpiDeviceBadArg;
  }

  uint32_t reg = mmio_region_read32(spi->params.base_addr,
                                    SPI_DEVICE_INTR_ENABLE_REG_OFFSET);
  *state = bitfield_bit32_read(reg, index) ? kDifSpiDeviceToggleEnabled
                                           : kDifSpiDeviceToggleDisabled;

  return kDifSpiDeviceOk;
}

dif_spi_device_result_t dif_spi_device_irq_set_enabled(
    const dif_spi_device_t *spi, dif_spi_device_irq_t irq,
    dif_spi_device_toggle_t state) {
  if (spi == NULL) {
    return kDifSpiDeviceBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifSpiDeviceBadArg;
  }

  bool flag;
  switch (state) {
    case kDifSpiDeviceToggleEnabled:
      flag = true;
      break;
    case kDifSpiDeviceToggleDisabled:
      flag = false;
      break;
    default:
      return kDifSpiDeviceBadArg;
  }

  uint32_t reg = mmio_region_read32(spi->params.base_addr,
                                    SPI_DEVICE_INTR_ENABLE_REG_OFFSET);
  reg = bitfield_bit32_write(reg, index, flag);
  mmio_region_write32(spi->params.base_addr, SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
                      reg);

  return kDifSpiDeviceOk;
}

dif_spi_device_result_t dif_spi_device_irq_force(const dif_spi_device_t *spi,
                                                 dif_spi_device_irq_t irq) {
  if (spi == NULL) {
    return kDifSpiDeviceBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifSpiDeviceBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(spi->params.base_addr, SPI_DEVICE_INTR_TEST_REG_OFFSET,
                      reg);

  return kDifSpiDeviceOk;
}

dif_spi_device_result_t dif_spi_device_irq_disable_all(
    const dif_spi_device_t *spi, dif_spi_device_irq_snapshot_t *snapshot) {
  if (spi == NULL) {
    return kDifSpiDeviceBadArg;
  }

  if (snapshot != NULL) {
    *snapshot = mmio_region_read32(spi->params.base_addr,
                                   SPI_DEVICE_INTR_ENABLE_REG_OFFSET);
  }

  mmio_region_write32(spi->params.base_addr, SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
                      0);

  return kDifSpiDeviceOk;
}

dif_spi_device_result_t dif_spi_device_irq_restore_all(
    const dif_spi_device_t *spi,
    const dif_spi_device_irq_snapshot_t *snapshot) {
  if (spi == NULL || snapshot == NULL) {
    return kDifSpiDeviceBadArg;
  }

  mmio_region_write32(spi->params.base_addr, SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
                      *snapshot);

  return kDifSpiDeviceOk;
}

dif_spi_device_result_t dif_spi_device_set_irq_levels(
    const dif_spi_device_t *spi, uint16_t rx_level, uint16_t tx_level) {
  if (spi == NULL) {
    return kDifSpiDeviceBadArg;
  }

  uint32_t compressed_limit = 0;
  compressed_limit = bitfield_field32_write(
      compressed_limit, SPI_DEVICE_FIFO_LEVEL_RXLVL_FIELD, rx_level);
  compressed_limit = bitfield_field32_write(
      compressed_limit, SPI_DEVICE_FIFO_LEVEL_TXLVL_FIELD, tx_level);
  mmio_region_write32(spi->params.base_addr, SPI_DEVICE_FIFO_LEVEL_REG_OFFSET,
                      compressed_limit);

  return kDifSpiDeviceOk;
}

/**
 * Parameters for compressing and decompressing a FIFO pointer register.
 */
typedef struct fifo_ptr_params {
  ptrdiff_t reg_offset;
  ptrdiff_t write_offset;
  ptrdiff_t read_offset;
  uint32_t write_mask;
  uint32_t read_mask;
} fifo_ptr_params_t;

/**
 * Parameters for the transmission FIFO.
 */
static const fifo_ptr_params_t kTxFifoParams = {
    .reg_offset = SPI_DEVICE_TXF_PTR_REG_OFFSET,
    .write_offset = SPI_DEVICE_TXF_PTR_WPTR_OFFSET,
    .write_mask = SPI_DEVICE_TXF_PTR_WPTR_MASK,
    .read_offset = SPI_DEVICE_TXF_PTR_RPTR_OFFSET,
    .read_mask = SPI_DEVICE_TXF_PTR_RPTR_MASK,
};

/**
 * Parameters for the receipt FIFO.
 */
static const fifo_ptr_params_t kRxFifoParams = {
    .reg_offset = SPI_DEVICE_RXF_PTR_REG_OFFSET,
    .write_offset = SPI_DEVICE_RXF_PTR_WPTR_OFFSET,
    .write_mask = SPI_DEVICE_RXF_PTR_WPTR_MASK,
    .read_offset = SPI_DEVICE_RXF_PTR_RPTR_OFFSET,
    .read_mask = SPI_DEVICE_RXF_PTR_RPTR_MASK,
};

/**
 * An exploded FIFO pointer value, consisting of a `uint11_t`
 * offset part (an offset into a FIFO), and a `uint1_t` phase
 * (which indicates whether this pointer has wrapped around or not).
 *
 * See also `fifo_ptrs_t`.
 */
typedef struct fifo_ptr {
  uint16_t offset;
  bool phase;
} fifo_ptr_t;

// Masks for extracting the phase and offset parts from a
// compressed FIFO pointer.
static const uint16_t kFifoPhaseMask = (1 << 12);
static const uint16_t kFifoOffsetMask = (1 << 12) - 1;

/**
 * Modifies a `fifo_ptr_t` into a FIFO of length `fifo_len` by
 * incrementing it by `increment`, making sure to correctly flip the
 * phase bit on overflow.
 *
 * @param ptr the poitner to increment.
 * @param increment the amount to increment by.
 * @param fifo_len the length of the FIFO the pointer points into.
 */
static void fifo_ptr_increment(fifo_ptr_t *ptr, uint16_t increment,
                               uint16_t fifo_len) {
  uint32_t inc_with_overflow = ptr->offset + increment;
  // If we would overflow, wrap and flip the overflow bit.
  if (inc_with_overflow >= fifo_len) {
    inc_with_overflow -= fifo_len;
    ptr->phase = !ptr->phase;
  }

  ptr->offset = inc_with_overflow & kFifoOffsetMask;
}

/**
 * A decompressed FIFO pointer register, consisting of a read offset
 * and a write offset within the FIFO region.
 *
 * The offsets themselves are only `uint11_t`, with an additional
 * 12th "phase" bit used for detecting the wrap around behavior of
 * the ring buffer FIFOs.
 */
typedef struct fifo_ptrs {
  fifo_ptr_t write_ptr;
  fifo_ptr_t read_ptr;
} fifo_ptrs_t;

/**
 * Expands read and write FIFO pointers out of `spi`, using the given FIFO
 * parameters.
 *
 * @param spi the SPI device.
 * @param params bitfield parameters for the FIFO.
 * @return expanded pointers read out of `spi`.
 */
static fifo_ptrs_t decompress_ptrs(const dif_spi_device_t *spi,
                                   fifo_ptr_params_t params) {
  uint32_t ptr = mmio_region_read32(spi->params.base_addr, params.reg_offset);
  uint16_t write_val =
      (uint16_t)((ptr >> params.write_offset) & params.write_mask);
  uint16_t read_val =
      (uint16_t)((ptr >> params.read_offset) & params.read_mask);
  return (fifo_ptrs_t){
      .write_ptr =
          {
              .offset = write_val & kFifoOffsetMask,
              .phase = (write_val & kFifoPhaseMask) != 0,
          },
      .read_ptr =
          {
              .offset = read_val & kFifoOffsetMask,
              .phase = (read_val & kFifoPhaseMask) != 0,
          },
  };
}

/**
 * Writes back read and write FIFO pointers into `spi`, using the given FIFO
 * parameters.
 *
 * @param spi the SPI device.
 * @param params bitfield parameters for the FIFO.
 * @param ptrs the new pointer values.
 */
static void compress_ptrs(const dif_spi_device_t *spi, fifo_ptr_params_t params,
                          fifo_ptrs_t ptrs) {
  uint16_t write_val = ptrs.write_ptr.offset;
  if (ptrs.write_ptr.phase) {
    write_val |= kFifoPhaseMask;
  }
  uint16_t read_val = ptrs.read_ptr.offset;
  if (ptrs.read_ptr.phase) {
    read_val |= kFifoPhaseMask;
  }

  uint32_t ptr = 0;
  ptr = bitfield_field32_write(
      ptr,
      (bitfield_field32_t){
          .mask = params.write_mask, .index = params.write_offset,
      },
      write_val);
  ptr = bitfield_field32_write(
      ptr,
      (bitfield_field32_t){
          .mask = params.read_mask, .index = params.read_offset,
      },
      read_val);
  mmio_region_write32(spi->params.base_addr, params.reg_offset, ptr);
}

/**
 * Counts the number of bytes from the read pointer to the write pointer in
 * `ptrs`, in a FIFO of length `fifo_len`.
 *
 * @param ptrs a set of FIFO pointers.
 * @param fifo_len the length of the fifo, in bytes.
 * @return the number of bytes "in use".
 */
static uint16_t fifo_bytes_in_use(fifo_ptrs_t ptrs, uint16_t fifo_len) {
  // This represents the case where the valid data of the fifo is "inclusive",
  // i.e., the buffer looks like (where a / represents valid data):
  // [ /////       ]
  //   ^    ^
  //   r    w
  //
  // In particular, when r == w, the fifo is empty.
  if (ptrs.write_ptr.phase == ptrs.read_ptr.phase) {
    return ptrs.write_ptr.offset - ptrs.read_ptr.offset;
  }

  // This represents the case where the valid data of the fifo is "exclusive",
  // i.e., the buffer looks like (where a / represents valid data):
  // [/      //////]
  //   ^     ^
  //   w     r
  //
  // In particular, when r == w, the fifo is full.
  return fifo_len - (ptrs.read_ptr.offset - ptrs.write_ptr.offset);
}

dif_spi_device_result_t dif_spi_device_rx_pending(const dif_spi_device_t *spi,
                                                  size_t *bytes_pending) {
  if (spi == NULL || bytes_pending == NULL) {
    return kDifSpiDeviceBadArg;
  }

  fifo_ptrs_t ptrs = decompress_ptrs(spi, kRxFifoParams);
  *bytes_pending = fifo_bytes_in_use(ptrs, spi->rx_fifo_len);

  return kDifSpiDeviceOk;
}

dif_spi_device_result_t dif_spi_device_tx_pending(const dif_spi_device_t *spi,
                                                  size_t *bytes_pending) {
  if (spi == NULL || bytes_pending == NULL) {
    return kDifSpiDeviceBadArg;
  }

  fifo_ptrs_t ptrs = decompress_ptrs(spi, kTxFifoParams);
  *bytes_pending = fifo_bytes_in_use(ptrs, spi->tx_fifo_len);

  return kDifSpiDeviceOk;
}

/**
 * Performs a "memcpy" of sorts between a main memory buffer and SPI SRAM,
 * which does not support non-word I/O.
 *
 * If `is_recv` is set, then the copy direction is `spi -> buf`. If it is
 * unset, the copy direction is `buf -> spi`.
 *
 * @param spi a SPI device.
 * @param fifo a decompressed FIFO pointer pair.
 * @param fifo_base the offset from start of SRAM for the FIFO to copy to/from.
 * @param fifo_len the length of the FIFO, in bytes.
 * @param byte_buf a main memory buffer for copying from/to.
 * @param buf_len the length of the main memory buffer.
 * @param is_recv whether this is a SPI reciept or SPI transmit transaction.
 * @return the number of bytes copied.
 */
static size_t spi_memcpy(const dif_spi_device_t *spi, fifo_ptrs_t *fifo,
                         uint16_t fifo_base, uint16_t fifo_len,
                         uint8_t *byte_buf, size_t buf_len, bool is_recv) {
  uint16_t bytes_left = fifo_bytes_in_use(*fifo, fifo_len);
  // When sending, the bytes left are the empty space still available.
  if (!is_recv) {
    bytes_left = fifo_len - bytes_left;
  }

  if (bytes_left > buf_len) {
    bytes_left = buf_len;
  }
  if (bytes_left == 0) {
    return 0;
  }
  const uint16_t total_bytes = bytes_left;

  // For receipt, we advance the read pointer, which indicates how far ahead
  // we've read so far. For sending, we advance the write pointer, which
  // indicates how far ahead we've written.
  fifo_ptr_t *ptr;
  if (is_recv) {
    ptr = &fifo->read_ptr;
  } else {
    ptr = &fifo->write_ptr;
  }

  // `mmio_region_memcpy_*_mmio32` functions assume sequential memory access
  // while the SPI device uses a circular buffer. Therefore, we split the copy
  // operation into chunks that access the device buffer sequentially.
  while (bytes_left > 0) {
    const uint32_t mmio_offset =
        SPI_DEVICE_BUFFER_REG_OFFSET + fifo_base + ptr->offset;
    const uint32_t bytes_until_wrap = fifo_len - ptr->offset;
    uint16_t bytes_to_copy = bytes_left;
    if (bytes_to_copy > bytes_until_wrap) {
      bytes_to_copy = bytes_until_wrap;
    }
    if (is_recv) {
      // SPI device buffer -> `byte_buf`
      mmio_region_memcpy_from_mmio32(spi->params.base_addr, mmio_offset,
                                     byte_buf, bytes_to_copy);
    } else {
      // `byte_buf` -> SPI device buffer
      mmio_region_memcpy_to_mmio32(spi->params.base_addr, mmio_offset, byte_buf,
                                   bytes_to_copy);
    }
    fifo_ptr_increment(ptr, bytes_to_copy, fifo_len);
    byte_buf += bytes_to_copy;
    bytes_left -= bytes_to_copy;
  }

  return total_bytes;
}

dif_spi_device_result_t dif_spi_device_recv(const dif_spi_device_t *spi,
                                            void *buf, size_t buf_len,
                                            size_t *bytes_received) {
  if (spi == NULL || buf == NULL) {
    return kDifSpiDeviceBadArg;
  }

  uint16_t fifo_base = 0;
  uint16_t fifo_len = spi->rx_fifo_len;
  fifo_ptrs_t fifo = decompress_ptrs(spi, kRxFifoParams);

  size_t bytes = spi_memcpy(spi, &fifo, fifo_base, fifo_len, (uint8_t *)buf,
                            buf_len, /*is_recv=*/true);
  if (bytes_received != NULL) {
    *bytes_received = bytes;
  }
  if (bytes > 0) {
    // Commit the new RX FIFO pointers.
    compress_ptrs(spi, kRxFifoParams, fifo);
  }
  return kDifSpiDeviceOk;
}

dif_spi_device_result_t dif_spi_device_send(const dif_spi_device_t *spi,
                                            const void *buf, size_t buf_len,
                                            size_t *bytes_sent) {
  if (spi == NULL || buf == NULL) {
    return kDifSpiDeviceBadArg;
  }

  // Start of the TX FIFO is the end of the RX FIFO.
  uint16_t fifo_base = spi->rx_fifo_len;
  uint16_t fifo_len = spi->tx_fifo_len;
  fifo_ptrs_t fifo = decompress_ptrs(spi, kTxFifoParams);

  size_t bytes = spi_memcpy(spi, &fifo, fifo_base, fifo_len, (uint8_t *)buf,
                            buf_len, /*is_recv=*/false);
  if (bytes_sent != NULL) {
    *bytes_sent = bytes;
  }
  if (bytes > 0) {
    // Commit the new TX FIFO pointers.
    compress_ptrs(spi, kTxFifoParams, fifo);
  }
  return kDifSpiDeviceOk;
}
