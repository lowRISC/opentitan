// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_DMA_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_DMA_TESTUTILS_H_

#include "sw/device/lib/dif/dif_dma.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/testing/test_framework/check.h"

/**
 * Initialize the provided SPI host for being used in the DMA hardware handshake
 * mode.
 *
 * @param spi_host An spi_host DIF handle.
 * @param peripheral_clock_freq_hz The peripheral clock frequency in hertz.
 * @param rx_watermark The watermark level of the FIFO to raise the status IRQ
 * for the DMA.
 */
void init_spi_host(dif_spi_host_t *spi_host, uint32_t peripheral_clock_freq_hz,
                   uint32_t rx_watermark);

/**
 * Setup pads for spi_host0
 *
 * This peripheral is 'direct' connected to the pads.
 *
 * @param pinmux An pinmux DIF handle.
 */
void setup_pads_spi_host0(dif_pinmux_t *pinmux);

/**
 * Configure the SPI for a receiving transaction and configure the DMA for the
 * hardware handshake mode to read the SPI host.
 *
 *  @param spi_host An spi_host DIF handle.
 *  @param dma An DMA DIF handle.
 *  @param rx_buffer Pointer to the receiving buffer, where the DMA writes the
 * received data.
 *  @param chunk_size The size of one chunk read from the LSIO peripheral.
 *  @param total_size The total size of data to be read from the LSIO
 * peripheral.
 */
void setup_spi_dma_transaction(dif_spi_host_t *spi_host, dif_dma_t *dma,
                               uint8_t *rx_buffer, uint32_t chunk_size,
                               uint32_t total_size);

/**
 * Return the digest length given a DMA opcode.
 *
 * @param opcode A DMA opcode.
 * @return The digest length.
 */
uint32_t get_digest_length(dif_dma_transaction_opcode_t opcode);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_DMA_TESTUTILS_H_
