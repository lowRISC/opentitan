// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_

/**
 * @file
 * @brief <a href="/hw/ip/spi_device/doc/">SPI Device</a> Device Interface
 * Functions
 */

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_spi_device_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A signal edge type: positive or negative.
 */
typedef enum dif_spi_device_edge {
  /**
   * Represents a positive edge (i.e., from low to high).
   */
  kDifSpiDeviceEdgePositive,
  /**
   * Represents a negative edge (i.e., from high to low).
   */
  kDifSpiDeviceEdgeNegative,
} dif_spi_device_edge_t;

/**
 * A bit ordering within a byte.
 */
typedef enum dif_spi_device_bit_order {
  /**
   * Represents the most-significant-bit to least-significant-bit order.
   */
  kDifSpiDeviceBitOrderMsbToLsb,
  /**
   * Represents the least-significant-bit to most-significant-bit order.
   */
  kDifSpiDeviceBitOrderLsbToMsb,
} dif_spi_device_bit_order_t;

/**
 * Runtime configuration for SPI.
 *
 * This struct describes runtime information for one-time configuration of the
 * hardware.
 */
typedef struct dif_spi_device_config {
  dif_spi_device_edge_t clock_polarity;
  dif_spi_device_edge_t data_phase;
  dif_spi_device_bit_order_t tx_order;
  dif_spi_device_bit_order_t rx_order;
  uint8_t rx_fifo_timeout;
  /**
   * The length, in bytes, that should be reserved for the RX FIFO.
   *
   * `kDifSpiDeviceBufferLen / 2` is a good default for this value.
   */
  uint16_t rx_fifo_len;
  /**
   * The length, in bytes, that should be reserved for the TX FIFO.
   *
   * `kDifSpiDeviceBufferLen / 2` is a good default for this value.
   */
  uint16_t tx_fifo_len;
} dif_spi_device_config_t;

/**
 * The length of the SPI device FIFO buffer, in bytes.
 *
 * Useful for initializing FIFO lengths: for example, for equally-sized FIFOs,
 * `rx_fifo_len` and `tx_fifo_len` would be set to `kDifSpiDeviceBufferLen / 2`.
 */
extern const uint16_t kDifSpiDeviceBufferLen;

/**
 * Creates a new handle for SPI.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr Hardware instantiation base address.
 * @param[out] spi Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_init(mmio_region_t base_addr,
                                 dif_spi_device_t *spi);

/**
 * Configures SPI with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * @param spi A SPI handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_configure(const dif_spi_device_t *spi,
                                      const dif_spi_device_config_t *config);

/**
 * Issues an "abort" to the given SPI device, causing all in-progress IO to
 * halt.
 *
 * @param spi A SPI handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_abort(const dif_spi_device_t *spi);

/**
 * Sets up the "FIFO level" (that is, number of bytes present in a particular
 * FIFO) at which the TxLevel and RxLevel IRQs will fire.
 *
 * For the reciept side, when the FIFO overflows `rx_level` (i.e., goes over
 * the set level), an interrupt is fired. This can be used to detect that more
 * data should be read from the RX FIFO. This is the
 * `Spi Buffer -> Main Memory` case.
 *
 * Conversely, for the transmission side, when the FIFO underflows `tx_level`
 * (i.e., goes below the set level), an interrupt is fired. This can be used
 * to detect that there is free space to write more data to the TX FIFO.
 * This is the `Main Memory -> Spi Buffer` case.
 *
 * @param spi A SPI handle.
 * @param rx_level The new RX level, as described above.
 * @param tx_level The new TX level, as described above.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_set_irq_levels(const dif_spi_device_t *spi,
                                           uint16_t rx_level,
                                           uint16_t tx_level);

/**
 * Returns the number of bytes still pending receipt by software in the RX FIFO.
 *
 * @param spi A SPI handle.
 * @param[out] bytes_pending The number of bytes pending
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_rx_pending(const dif_spi_device_t *spi,
                                       const dif_spi_device_config_t *config,
                                       size_t *bytes_pending);

/**
 * Returns the number of bytes still pending transmission by hardware in the TX
 * FIFO.
 *
 * @param spi A SPI handle.
 * @param[out] bytes_pending The number of bytes pending
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_tx_pending(const dif_spi_device_t *spi,
                                       const dif_spi_device_config_t *config,
                                       size_t *bytes_pending);

/**
 * Reads at most `buf_len` bytes from the RX FIFO; the number of bytes read
 * will be written to `bytes_received`.
 *
 * @param spi A SPI device.
 * @param[out] buf A pointer to valid memory.
 * @param buf_len The length of the buffer `buf` points to.
 * @param[out] bytes_received The number of bytes successfully read; may be
 * null.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_recv(const dif_spi_device_t *spi,
                                 const dif_spi_device_config_t *config,
                                 void *buf, size_t buf_len,
                                 size_t *bytes_received);

/**
 * Writes at most `buf_len` bytes to the TX FIFO; the number of bytes actually
 * written will be written to `bytes_sent`.
 *
 * @param spi A SPI device.
 * @param buf A pointer to bytes to be written.
 * @param buf_len The length of the buffer `buf` points to.
 * @param[out] bytes_sent The number of bytes successfully written; may be null.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_send(const dif_spi_device_t *spi,
                                 const dif_spi_device_config_t *config,
                                 const void *buf, size_t buf_len,
                                 size_t *bytes_sent);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_
