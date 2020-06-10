// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_spi_device.h"

#include "spi_device_regs.h"  // Generated.
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"

const uint16_t kDifSpiDeviceBufferLen = SPI_DEVICE_BUFFER_SIZE_BYTES;

/**
 * Computes the required value of the control register from a given
 * configuration.
 */
static dif_spi_device_result_t build_control_word(
    const dif_spi_device_config_t *config, uint32_t *control_word) {
  *control_word = 0;

  // Default polarity is positive.
  if (config->clock_polarity == kDifSpiDeviceEdgeNegative) {
    *control_word |= 0x1 << SPI_DEVICE_CFG_CPOL;
  }

  // Default phase is negative.
  if (config->data_phase == kDifSpiDeviceEdgePositive) {
    *control_word |= 0x1 << SPI_DEVICE_CFG_CPHA;
  }

  // Default order is msb to lsb.
  if (config->tx_order == kDifSpiDeviceBitOrderLsbToMsb) {
    *control_word |= 0x1 << SPI_DEVICE_CFG_TX_ORDER;
  }

  // Default order is msb to lsb.
  if (config->rx_order == kDifSpiDeviceBitOrderLsbToMsb) {
    *control_word |= 0x1 << SPI_DEVICE_CFG_RX_ORDER;
  }

  *control_word = bitfield_set_field32(
      *control_word, (bitfield_field32_t){
                         .mask = SPI_DEVICE_CFG_TIMER_V_MASK,
                         .index = SPI_DEVICE_CFG_TIMER_V_OFFSET,
                         .value = config->rx_fifo_timeout,
                     });

  return kDifSpiDeviceResultOk;
}

dif_spi_device_result_t dif_spi_device_init(
    mmio_region_t base_addr, const dif_spi_device_config_t *config,
    dif_spi_device_t *spi) {
  if (config == NULL || spi == NULL) {
    return kDifSpiDeviceResultBadArg;
  }
  spi->base_addr = base_addr;

  // NOTE: we do not write to any registers until performing all
  // function argument checks, to avoid a halfway-configured SPI.

  uint32_t device_config;
  dif_spi_device_result_t control_error =
      build_control_word(config, &device_config);
  if (control_error != kDifSpiDeviceResultOk) {
    return control_error;
  }

  uint16_t rx_fifo_start = 0x0;
  uint16_t rx_fifo_end = config->rx_fifo_len - 1;
  uint16_t tx_fifo_start = rx_fifo_end + 1;
  uint16_t tx_fifo_end = tx_fifo_start + config->tx_fifo_len - 1;
  if (tx_fifo_end >= kDifSpiDeviceBufferLen) {
    // We've overflown the SRAM region...
    return kDifSpiDeviceResultBadArg;
  }

  uint32_t rx_fifo_bounds = 0;
  rx_fifo_bounds = bitfield_set_field32(
      rx_fifo_bounds, (bitfield_field32_t){
                          .mask = SPI_DEVICE_RXF_ADDR_BASE_MASK,
                          .index = SPI_DEVICE_RXF_ADDR_BASE_OFFSET,
                          .value = rx_fifo_start,
                      });
  rx_fifo_bounds = bitfield_set_field32(
      rx_fifo_bounds, (bitfield_field32_t){
                          .mask = SPI_DEVICE_RXF_ADDR_LIMIT_MASK,
                          .index = SPI_DEVICE_RXF_ADDR_LIMIT_OFFSET,
                          .value = rx_fifo_end,
                      });

  uint32_t tx_fifo_bounds = 0;
  tx_fifo_bounds = bitfield_set_field32(
      tx_fifo_bounds, (bitfield_field32_t){
                          .mask = SPI_DEVICE_TXF_ADDR_BASE_MASK,
                          .index = SPI_DEVICE_TXF_ADDR_BASE_OFFSET,
                          .value = tx_fifo_start,
                      });
  tx_fifo_bounds = bitfield_set_field32(
      tx_fifo_bounds, (bitfield_field32_t){
                          .mask = SPI_DEVICE_TXF_ADDR_LIMIT_MASK,
                          .index = SPI_DEVICE_TXF_ADDR_LIMIT_OFFSET,
                          .value = tx_fifo_end,
                      });

  spi->rx_fifo_base = rx_fifo_start;
  spi->rx_fifo_len = config->rx_fifo_len;
  spi->tx_fifo_base = tx_fifo_start;
  spi->tx_fifo_len = config->tx_fifo_len;

  // Now that we know that all function arguments are valid, we can abort
  // all current transactions and begin reconfiguring the device.
  dif_spi_device_result_t err;
  err = dif_spi_device_abort(spi);
  if (err != kDifSpiDeviceResultOk) {
    return err;
  }
  err = dif_spi_device_irq_reset(spi);
  if (err != kDifSpiDeviceResultOk) {
    return err;
  }

  mmio_region_write32(spi->base_addr, SPI_DEVICE_CFG_REG_OFFSET, device_config);
  mmio_region_write32(spi->base_addr, SPI_DEVICE_RXF_ADDR_REG_OFFSET,
                      rx_fifo_bounds);
  mmio_region_write32(spi->base_addr, SPI_DEVICE_TXF_ADDR_REG_OFFSET,
                      tx_fifo_bounds);

  return kDifSpiDeviceResultOk;
}

dif_spi_device_result_t dif_spi_device_abort(const dif_spi_device_t *spi) {
  if (spi == NULL) {
    return kDifSpiDeviceResultBadArg;
  }

  // Set the `abort` bit, and then spin until `abort_done` is asserted.
  mmio_region_nonatomic_set_bit32(spi->base_addr, SPI_DEVICE_CONTROL_REG_OFFSET,
                                  SPI_DEVICE_CONTROL_ABORT);
  while (!mmio_region_get_bit32(spi->base_addr, SPI_DEVICE_STATUS_REG_OFFSET,
                                SPI_DEVICE_STATUS_ABORT_DONE)) {
  }

  return kDifSpiDeviceResultOk;
}

dif_spi_device_result_t dif_spi_device_irq_reset(const dif_spi_device_t *spi) {
  if (spi == NULL) {
    return kDifSpiDeviceResultBadArg;
  }

  dif_spi_device_result_t err;

  err = dif_spi_device_irq_clear_all(spi);
  if (err != kDifSpiDeviceResultOk) {
    return err;
  }
  err = dif_spi_device_set_irq_levels(spi, 0x80, 0x00);
  if (err != kDifSpiDeviceResultOk) {
    return err;
  }

  // Disable interrupts manually, since the relevant DIF only allows for single
  // bit flips.
  mmio_region_write32(spi->base_addr, SPI_DEVICE_INTR_ENABLE_REG_OFFSET, 0);

  return kDifSpiDeviceResultOk;
}

dif_spi_device_result_t dif_spi_device_irq_get(const dif_spi_device_t *spi,
                                               dif_spi_device_irq_type_t type,
                                               bool *flag_out) {
  if (spi == NULL || flag_out == NULL) {
    return kDifSpiDeviceResultBadArg;
  }

  uint32_t bit_index = 0;
  switch (type) {
    case kDifSpiDeviceIrqTypeRxFull:
      bit_index = SPI_DEVICE_INTR_STATE_RXF;
      break;
    case kDifSpiDeviceIrqTypeRxAboveLevel:
      bit_index = SPI_DEVICE_INTR_STATE_RXLVL;
      break;
    case kDifSpiDeviceIrqTypeTxBelowLevel:
      bit_index = SPI_DEVICE_INTR_STATE_TXLVL;
      break;
    case kDifSpiDeviceIrqTypeRxError:
      bit_index = SPI_DEVICE_INTR_STATE_RXERR;
      break;
    case kDifSpiDeviceIrqTypeRxOverflow:
      bit_index = SPI_DEVICE_INTR_STATE_RXOVERFLOW;
      break;
    case kDifSpiDeviceIrqTypeTxUnderflow:
      bit_index = SPI_DEVICE_INTR_STATE_TXUNDERFLOW;
      break;
  }

  *flag_out = mmio_region_get_bit32(
      spi->base_addr, SPI_DEVICE_INTR_STATE_REG_OFFSET, bit_index);
  return kDifSpiDeviceResultOk;
}

dif_spi_device_result_t dif_spi_device_irq_clear_all(
    const dif_spi_device_t *spi) {
  if (spi == NULL) {
    return kDifSpiDeviceResultBadArg;
  }

  // The state register is a write-one-clear register.
  mmio_region_write32(spi->base_addr, SPI_DEVICE_INTR_STATE_REG_OFFSET,
                      UINT32_MAX);

  return kDifSpiDeviceResultOk;
}

dif_spi_device_result_t dif_spi_device_irq_enable(
    const dif_spi_device_t *spi, dif_spi_device_irq_type_t type,
    dif_spi_device_irq_state_t state) {
  if (spi == NULL) {
    return kDifSpiDeviceResultBadArg;
  }

  uint32_t bit_index = 0;
  switch (type) {
    case kDifSpiDeviceIrqTypeRxFull:
      bit_index = SPI_DEVICE_INTR_ENABLE_RXF;
      break;
    case kDifSpiDeviceIrqTypeRxAboveLevel:
      bit_index = SPI_DEVICE_INTR_ENABLE_RXLVL;
      break;
    case kDifSpiDeviceIrqTypeTxBelowLevel:
      bit_index = SPI_DEVICE_INTR_ENABLE_TXLVL;
      break;
    case kDifSpiDeviceIrqTypeRxError:
      bit_index = SPI_DEVICE_INTR_ENABLE_RXERR;
      break;
    case kDifSpiDeviceIrqTypeRxOverflow:
      bit_index = SPI_DEVICE_INTR_ENABLE_RXOVERFLOW;
      break;
    case kDifSpiDeviceIrqTypeTxUnderflow:
      bit_index = SPI_DEVICE_INTR_ENABLE_TXUNDERFLOW;
      break;
  }

  switch (state) {
    case kDifSpiDeviceIrqStateEnabled:
      mmio_region_nonatomic_set_bit32(
          spi->base_addr, SPI_DEVICE_INTR_ENABLE_REG_OFFSET, bit_index);
      break;
    case kDifSpiDeviceIrqStateDisabled:
      mmio_region_nonatomic_clear_bit32(
          spi->base_addr, SPI_DEVICE_INTR_ENABLE_REG_OFFSET, bit_index);
      break;
  }

  return kDifSpiDeviceResultOk;
}

dif_spi_device_result_t dif_spi_device_irq_force(
    const dif_spi_device_t *spi, dif_spi_device_irq_type_t type) {
  if (spi == NULL) {
    return kDifSpiDeviceResultBadArg;
  }

  uint32_t bit_index = 0;
  switch (type) {
    case kDifSpiDeviceIrqTypeRxFull:
      bit_index = SPI_DEVICE_INTR_TEST_RXF;
      break;
    case kDifSpiDeviceIrqTypeRxAboveLevel:
      bit_index = SPI_DEVICE_INTR_TEST_RXLVL;
      break;
    case kDifSpiDeviceIrqTypeTxBelowLevel:
      bit_index = SPI_DEVICE_INTR_TEST_TXLVL;
      break;
    case kDifSpiDeviceIrqTypeRxError:
      bit_index = SPI_DEVICE_INTR_TEST_RXERR;
      break;
    case kDifSpiDeviceIrqTypeRxOverflow:
      bit_index = SPI_DEVICE_INTR_TEST_RXOVERFLOW;
      break;
    case kDifSpiDeviceIrqTypeTxUnderflow:
      bit_index = SPI_DEVICE_INTR_TEST_TXUNDERFLOW;
      break;
  }

  uint32_t mask = 1 << bit_index;
  mmio_region_write32(spi->base_addr, SPI_DEVICE_INTR_TEST_REG_OFFSET, mask);

  return kDifSpiDeviceResultOk;
}

dif_spi_device_result_t dif_spi_device_set_irq_levels(
    const dif_spi_device_t *spi, uint16_t rx_level, uint16_t tx_level) {
  if (spi == NULL) {
    return kDifSpiDeviceResultBadArg;
  }

  uint32_t compressed_limit = 0;
  compressed_limit = bitfield_set_field32(
      compressed_limit, (bitfield_field32_t){
                            .mask = SPI_DEVICE_FIFO_LEVEL_RXLVL_MASK,
                            .index = SPI_DEVICE_FIFO_LEVEL_RXLVL_OFFSET,
                            .value = rx_level,
                        });
  compressed_limit = bitfield_set_field32(
      compressed_limit, (bitfield_field32_t){
                            .mask = SPI_DEVICE_FIFO_LEVEL_TXLVL_MASK,
                            .index = SPI_DEVICE_FIFO_LEVEL_TXLVL_OFFSET,
                            .value = tx_level,
                        });
  mmio_region_write32(spi->base_addr, SPI_DEVICE_FIFO_LEVEL_REG_OFFSET,
                      compressed_limit);

  return kDifSpiDeviceResultOk;
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
static const uint16_t kFifoPhaseMask = (1 << 11);
static const uint16_t kFifoOffsetMask = (1 << 11) - 1;

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
  uint32_t ptr = mmio_region_read32(spi->base_addr, params.reg_offset);
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
  ptr = bitfield_set_field32(ptr, (bitfield_field32_t){
                                      .mask = params.write_mask,
                                      .index = params.write_offset,
                                      .value = write_val,
                                  });
  ptr = bitfield_set_field32(ptr, (bitfield_field32_t){
                                      .mask = params.read_mask,
                                      .index = params.read_offset,
                                      .value = read_val,
                                  });
  mmio_region_write32(spi->base_addr, params.reg_offset, ptr);
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
    return kDifSpiDeviceResultBadArg;
  }

  fifo_ptrs_t ptrs = decompress_ptrs(spi, kRxFifoParams);
  *bytes_pending = fifo_bytes_in_use(ptrs, spi->rx_fifo_len);

  return kDifSpiDeviceResultOk;
}

dif_spi_device_result_t dif_spi_device_tx_pending(const dif_spi_device_t *spi,
                                                  size_t *bytes_pending) {
  if (spi == NULL || bytes_pending == NULL) {
    return kDifSpiDeviceResultBadArg;
  }

  fifo_ptrs_t ptrs = decompress_ptrs(spi, kTxFifoParams);
  *bytes_pending = fifo_bytes_in_use(ptrs, spi->tx_fifo_len);

  return kDifSpiDeviceResultOk;
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
      mmio_region_memcpy_from_mmio32(spi->base_addr, mmio_offset, byte_buf,
                                     bytes_to_copy);
    } else {
      // `byte_buf` -> SPI device buffer
      mmio_region_memcpy_to_mmio32(spi->base_addr, mmio_offset, byte_buf,
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
    return kDifSpiDeviceResultBadArg;
  }

  uint16_t fifo_base = spi->rx_fifo_base;
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
  return kDifSpiDeviceResultOk;
}

dif_spi_device_result_t dif_spi_device_send(const dif_spi_device_t *spi,
                                            const void *buf, size_t buf_len,
                                            size_t *bytes_sent) {
  if (spi == NULL || buf == NULL) {
    return kDifSpiDeviceResultBadArg;
  }

  uint16_t fifo_base = spi->tx_fifo_base;
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
  return kDifSpiDeviceResultOk;
}
