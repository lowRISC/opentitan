// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"

/**
 * Configuration for initializing a SPI device.
 */
typedef struct dif_spi_device_config {
  mmio_region_t base_addr;
} dif_spi_device_config_t;

/**
 * State for a particular SPI device.
 *
 * Its member variables should be considered private, and are only provided so
 * that callers can allocate it.
 */
typedef struct dif_spi_device {
  mmio_region_t base_addr;
} dif_spi_device_t;

/**
 * Errors returned by |dif_spi_device_init()|.
 */
typedef enum dif_spi_device_init_result {
  /**
   * Indicates a successful operation.
   */
  kDifSpiDeviceInitOk = 0,
  /**
   * Indicates a failed precondition on the function arguments.
   */
  kDifSpiDeviceInitPreconditionFailed,
} dif_spi_device_init_result_t;

/**
 * Initializes the SPI device described by |config|, writing internal state to
 * |spi_out|.
 *
 * This function *must* be called on a particular |mmio_region_t| before calling
 * any other functions in this header with that |mmio_region_t|; moreover, it
 * *may not* be called more than once with any |mmio_region_t|. All deviations
 * are Undefined Behavior.
 *
 * @param config configuration supplied for initializing a particular device.
 * @param spi_out out param for the SPI device; this location must
 *                be valid to write to.
 * @return the result of the operation.
 */
dif_spi_device_init_result_t dif_spi_device_init(dif_spi_device_config_t config,
                                                 dif_spi_device_t *spi_out);

/**
 * Errors returned by |dif_spi_device_send()|.
 */
typedef enum dif_spi_device_send_result {
  /**
   * Indicates a successful operation.
   */
  kDifSpiDeviceSendOk = 0,
  /**
   * Indicates a failed precondition on the function arguments.
   */
  kDifSpiDeviceSendPreconditionFailed,
} dif_spi_device_send_result_t;

/**
 * Attempts to send |len| bytes from the buffer pointed to by |data| over the
 * initialized SPI device at |spi|.
 *
 * |data| *must* point to a buffer of at least |len| bytes of initialized data;
 * not doing so is Undefined Behavior.
 *
 * @param spi the SPI device to send to.
 * @param data a contiguous buffer to copy from.
 * @param len the length of the buffer |data| points to.
 * @param bytes_sent out param for the number of bytes sent.
 * @return the result of the operation.
 */
dif_spi_device_send_result_t dif_spi_device_send(const dif_spi_device_t *spi,
                                                 const void *data, size_t len,
                                                 size_t *bytes_sent);

/**
 * Errors returned by |dif_spi_device_send()|.
 */
typedef enum dif_spi_device_recv_result {
  /**
   * Indicates a successful operation.
   */
  kDifSpiDeviceRecvOk = 0,
  /**
   * Indicates a failed precondition on the function arguments.
   */
  kDifSpiDeviceRecvPreconditionFailed,
} dif_spi_device_recv_result_t;

/**
 * Attempts to recieve |len| bytes over the SPI device at |spi|, which
 * will be written to the buffer pointed to by |data|.
 *
 * |data| *must* point to a buffer of at least |len| bytes of allocated data,
 * which may be uninitialized; not doing so is Undefined Behavior.
 *
 * After this function returns, the first |len| bytes pointed to by |buf| will
 * be in an initialized state. This function will never read from |buf|.
 *
 * @param spi the SPI device to send to.
 * @param buf a contiguous, possibly uninitialized buffer to write to.
 * @param len the length of the buffer |data| points to.
 * @param bytes_recved out param for the number of bytes recieved.
 * @return the result of the operation.
 */
dif_spi_device_recv_result_t dif_spi_device_recv(const dif_spi_device_t *spi,
                                                 void *buf, size_t len,
                                                 size_t *bytes_recved);

/**
 * Errors returned by |dif_spi_device_send()|.
 */
typedef enum dif_spi_device_bytes_pending_result {
  /**
   * Indicates a successful operation.
   */
  kDifSpiDeviceBytesPendingOk = 0,
  /**
   * Indicates a failed precondition on the function arguments.
   */
  kDifSpiDeviceBytesPendingPreconditionFailed,
} dif_spi_device_bytes_pending_result_t;

/**
 * Retrieves the number of bytes that would be returned if |spi_device_recv| was
 * called with a buffer of infinite length on the SPI device at |spi|.
 *
 * @param spi the SPI device to send to.
 * @param bytes_pending out param for the number of bytes pending.
 * @return the result of the operation.
 */
dif_spi_device_bytes_pending_result_t dif_spi_device_bytes_pending(
    const dif_spi_device_t *spi, size_t *bytes_pending);

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_
