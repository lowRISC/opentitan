// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/dma_testutils.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "spi_host_regs.h"  // Generated.

static const top_darjeeling_direct_pads_t spi_host0_direct_pads[6] = {
    kTopDarjeelingDirectPadsSpiHost0Sck,   // sck
    kTopDarjeelingDirectPadsSpiHost0Csb,   // csb
    kTopDarjeelingDirectPadsSpiHost0Sd3,   // sio[3]
    kTopDarjeelingDirectPadsSpiHost0Sd2,   // sio[2]
    kTopDarjeelingDirectPadsSpiHost0Sd1,   // sio[1]
    kTopDarjeelingDirectPadsSpiHost0Sd0};  // sio[0]

/**
 * Initialize the provided SPI host for being used in the DMA hardware handshake
 * mode.
 */
void init_spi_host(dif_spi_host_t *spi_host, uint32_t peripheral_clock_freq_hz,
                   uint32_t rx_watermark) {
  dif_spi_host_config_t config = {
      .spi_clock = peripheral_clock_freq_hz / 2,
      .peripheral_clock_freq_hz = peripheral_clock_freq_hz,
      .chip_select = {.idle = 2, .trail = 2, .lead = 2},
      .full_cycle = true,
      .cpha = true,
      .cpol = true,
      .rx_watermark = rx_watermark};
  CHECK_DIF_OK(dif_spi_host_configure(spi_host, config));
  CHECK_DIF_OK(dif_spi_host_output_set_enabled(spi_host, /*enabled=*/true));
}

/**
 * Setup pads for spi_host0
 *
 * This peripheral is 'direct' connected to the pads.
 */
void setup_pads_spi_host0(dif_pinmux_t *pinmux) {
  // set weak pull-ups for all the pads
  dif_pinmux_pad_attr_t out_attr;
  dif_pinmux_pad_attr_t in_attr = {
      .slew_rate = 0,
      .drive_strength = 0,
      .flags = kDifPinmuxPadAttrPullResistorEnable |
               kDifPinmuxPadAttrPullResistorUp};
  for (uint32_t i = 0; i < ARRAYSIZE(spi_host0_direct_pads); ++i) {
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(pinmux, spi_host0_direct_pads[i],
                                            kDifPinmuxPadKindDio, in_attr,
                                            &out_attr));
  }
}

void setup_spi_dma_transaction(dif_spi_host_t *spi_host, dif_dma_t *dma,
                               uint8_t *rx_buffer, uint32_t chunk_size,
                               uint32_t total_size) {
  dif_spi_host_segment_t host_operations[1] = {
      {.type = kDifSpiHostSegmentTypeRx,
       .tx = {.width = kDifSpiHostWidthStandard,
              .buf = NULL,
              .length = total_size}},
  };

  // Issue the SPI transaction
  CHECK_DIF_OK(dif_spi_host_start_transaction(
      spi_host, /*csid=*/0, host_operations, ARRAYSIZE(host_operations)));

  // Configure the DMA to read from SPI in hardware-handshake mode
  dif_dma_transaction_t transaction = {
      .source = {.address = TOP_DARJEELING_SPI_HOST0_BASE_ADDR +
                            SPI_HOST_RXDATA_REG_OFFSET,
                 .asid = kDifDmaOpentitanInternalBus},
      .destination = {.address = (uint32_t)&rx_buffer[0],
                      .asid = kDifDmaOpentitanInternalBus},
      .src_config = {.wrap = true, .increment = false},
      .dst_config = {.wrap = false, .increment = true},
      .total_size = total_size,
      .chunk_size = chunk_size,
      .width = kDifDmaTransWidth4Bytes};

  CHECK_DIF_OK(dif_dma_memory_range_set(dma, TOP_DARJEELING_RAM_MAIN_BASE_ADDR,
                                        TOP_DARJEELING_RAM_MAIN_SIZE_BYTES));
  // Enable LSIO trigger for SPI host at bit 1
  CHECK_DIF_OK(dif_dma_handshake_irq_enable(dma, 0x2));
  CHECK_DIF_OK(dif_dma_configure(dma, transaction));
  CHECK_DIF_OK(dif_dma_handshake_enable(dma));
}
