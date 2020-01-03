// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_

#include <stddef.h>
#include <stdint.h>

#ifdef MOCK_MMIO
#include "sw/device/lib/dif/testing/mock_mmio.h"
#endif  // MOCK_MMIO

#include "sw/device/lib/base/mmio.h"

/**
 * Configuration for initializing a SPI device.
 */
typedef struct dif_spi_device_config {
  reg32_t base_addr;
} dif_spi_device_config_t;

/**
 * State for a particular SPI device.
 *
 * Its member variables should be considered private, and are only provided so
 * that callers can allocate it.
 */
typedef struct dif_spi_device { reg32_t base_addr; } dif_spi_device_t;

/**
 * Initializes the SPI device described by |config|, writing internal state to
 * |spi_out|.
 *
 * This function *must* be called on a particular |reg32_t| before calling any
 * other functions in this header with that |reg32_t|; moreover, it *may not*
 * be called more than once with any |reg32_t|. All deviations are Undefined
 * Behavior.
 *
 * @param config configuration supplied for initializing a particular device.
 * @param spi_out the location at which to write SPI state; this location must
 *                be valid to write to.
 */
void dif_spi_device_init(dif_spi_device_config_t config,
                         dif_spi_device_t *spi_out);

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
 * @return the number of bytes actually sent.
 */
size_t dif_spi_device_send(const dif_spi_device_t *spi, const void *data,
                           size_t len);

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
 * @return the number of bytes actually recieved.
 */
size_t dif_spi_device_recv(const dif_spi_device_t *spi, void *buf, size_t len);

/**
 * Retrieves the number of bytes that would be returned if |spi_device_recv| was
 * called with a buffer of infinite length on the SPI device at |spi|.
 *
 * @param spi the SPI device to send to.
 * @return the number of bytes that could potentially be read.
 */
size_t dif_spi_device_bytes_pending(const dif_spi_device_t *spi);

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_
