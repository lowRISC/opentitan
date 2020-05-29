// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"

// Header Extern Guard (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Represents a signal edge type.
 */
typedef enum dif_spi_device_edge {
  kDifSpiDeviceEdgePositive,
  kDifSpiDeviceEdgeNegative,
} dif_spi_device_edge_t;

/**
 * Represents a bit ordering.
 */
typedef enum dif_spi_device_bit_order {
  kDifSpiDeviceBitOrderMsbToLsb,
  kDifSpiDeviceBitOrderLsbToMsb,
} dif_spi_device_bit_order_t;

/**
 * Represents the enablement state of a particular SPI IRQ.
 */
typedef enum dif_spi_device_irq_state {
  kDifSpiDeviceIrqStateEnabled = true,
  kDifSpiDeviceIrqStateDisabled = false,
} dif_spi_device_irq_state_t;

/**
 * Represents the types of interrupts that the SPI device will
 * fire to signal state.
 */
typedef enum dif_spi_device_irq_type {
  kDifSpiDeviceIrqTypeRxFull,
  kDifSpiDeviceIrqTypeRxAboveLevel,
  kDifSpiDeviceIrqTypeTxBelowLevel,
  kDifSpiDeviceIrqTypeRxError,
  kDifSpiDeviceIrqTypeRxOverflow,
  kDifSpiDeviceIrqTypeTxUnderflow,
} dif_spi_device_irq_type_t;

/**
 * Errors returned by SPI DIF functions.
 */
typedef enum dif_spi_device_result {
  /**
   * Indicates a successful operation.
   */
  kDifSpiDeviceResultOk = 0,
  /**
   * Indicates a failed precondition on the function arguments.
   */
  kDifSpiDeviceResultBadArg,
} dif_spi_device_result_t;

/**
 * The length of the SPI device FIFO buffer, in bytes.
 *
 * Useful for initializing FIFO lengths: for example, for equally-sized FIFOs,
 * `rx_fifo_len` and `tx_fifo_len` would be set to `kDifSpiDeviceBufferLen / 2`.
 */
extern const uint16_t kDifSpiDeviceBufferLen;

/**
 * Configuration for initializing a SPI device.
 */
typedef struct dif_spi_device_config {
  dif_spi_device_edge_t clock_polarity;
  dif_spi_device_edge_t data_phase;
  dif_spi_device_bit_order_t tx_order;
  dif_spi_device_bit_order_t rx_order;
  uint8_t rx_fifo_timeout;
  uint16_t rx_fifo_len;
  uint16_t tx_fifo_len;
} dif_spi_device_config_t;

/**
 * State for a particular SPI device.
 *
 * Its member variables should be considered private, and are only provided so
 * that callers can allocate it.
 */
typedef struct dif_spi_device {
  mmio_region_t base_addr;
  uint16_t rx_fifo_base;
  uint16_t rx_fifo_len;
  uint16_t tx_fifo_base;
  uint16_t tx_fifo_len;
} dif_spi_device_t;

/**
 * Initializes a SPI device with the given configuration.
 *
 * @param base_addr The start of the SPI device register.
 * @param config The configuration to initialize with.
 * @param spi Out param for the initialized device.
 * @return The result of the operation.
 */
dif_spi_device_result_t dif_spi_device_init(
    mmio_region_t base_addr, const dif_spi_device_config_t *config,
    dif_spi_device_t *spi);

/**
 * Issues an "abort" to the given SPI device, causing all in-progress IO to
 * halt.
 *
 * @param spi A SPI device.
 * @return The result of the operation.
 */
dif_spi_device_result_t dif_spi_device_abort(const dif_spi_device_t *spi);

/**
 * Resets all interrupt-related state on the given SPI device, such as enabled
 * interrupts and set RX/TX levels.
 *
 * @param spi A SPI device.
 * @return The result of the operation.
 */
dif_spi_device_result_t dif_spi_device_irq_reset(const dif_spi_device_t *spi);

/**
 * Returns whether the given IRQ is currently being serviced.
 *
 * @param spi A SPI device.
 * @param type Which IRQ type to check.
 * @param flag Out param for whether the IRQ is active..
 * @return The result of the operation.
 */
dif_spi_device_result_t dif_spi_device_irq_get(const dif_spi_device_t *spi,
                                               dif_spi_device_irq_type_t type,
                                               bool *flag_out);

/**
 * Clears all active interrupt bits.
 *
 * @param spi A SPI device.
 * @return The result of the operation.
 */
dif_spi_device_result_t dif_spi_device_irq_clear_all(
    const dif_spi_device_t *spi);

/**
 * Enable or disable a particular interrupt.
 *
 * @param spi A SPI device.
 * @param type Which IRQ type to toggle.
 * @param state The state to update the bit to.
 * @return The result of the operation.
 */
dif_spi_device_result_t dif_spi_device_irq_enable(
    const dif_spi_device_t *spi, dif_spi_device_irq_type_t type,
    dif_spi_device_irq_state_t state);

/**
 * Forces a particular IRQ type to fire.
 *
 * @param spi A SPI device.
 * @param type Which IRQ type to fire.
 * @return The result of the operation.
 */
dif_spi_device_result_t dif_spi_device_irq_force(
    const dif_spi_device_t *spi, dif_spi_device_irq_type_t type);

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
 * @param spi A SPI device.
 * @param rx_level The new RX level, as described above.
 * @param tx_level The new TX level, as described above.
 * @return The result of the operation.
 */
dif_spi_device_result_t dif_spi_device_set_irq_levels(
    const dif_spi_device_t *spi, uint16_t rx_level, uint16_t tx_level);

/**
 * Returns the number of bytes still pending receipt by software in the RX FIFO.
 *
 * @param spi A SPI device.
 * @param bytes_pending Out param for the number of bytes pending
 * @return The result of the operation.
 */
dif_spi_device_result_t dif_spi_device_rx_pending(const dif_spi_device_t *spi,
                                                  size_t *bytes_pending);

/**
 * Returns the number of bytes still pending transmission by hardware in the TX
 * FIFO.
 *
 * @param spi A SPI device.
 * @param bytes_pending Out param for the number of bytes pending
 * @return The result of the operation.
 */
dif_spi_device_result_t dif_spi_device_tx_pending(const dif_spi_device_t *spi,
                                                  size_t *bytes_pending);

/**
 * Reads at most `buf_len` bytes from the RX FIFO; the number of bytes read
 * will be written to `bytes_received`.
 *
 * @param spi A SPI device.
 * @param buf A pointer to valid memory.
 * @param buf_len The length of the buffer `buf` points to.
 * @param bytes_received Out param for the number of bytes successfully read;
 * may be null.
 * @return The result of the operation.
 */
dif_spi_device_result_t dif_spi_device_recv(const dif_spi_device_t *spi,
                                            void *buf, size_t buf_len,
                                            size_t *bytes_received);

/**
 * Writes at most `buf_len` bytes to the TX FIFO; the number of bytes actually
 * written will be written to `bytes_sent`.
 *
 * @param spi A SPI device.
 * @param buf A pointer to bytes to be written.
 * @param buf_len The length of the buffer `buf` points to.
 * @param bytes_recved Out param for the number of bytes successfully written;
 * may be null.
 * @return The result of the operation.
 */
dif_spi_device_result_t dif_spi_device_send(const dif_spi_device_t *spi,
                                            const void *buf, size_t buf_len,
                                            size_t *bytes_sent);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_
