// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define DATA_SET_SIZE 16

static dif_spi_host_t spi_host;
static dif_pinmux_t pinmux;

OTTF_DEFINE_TEST_CONFIG();

void enable_pull_up(void) {
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  dif_pinmux_pad_attr_t out_attr;
  dif_pinmux_pad_attr_t in_attr = {
      .slew_rate = 0,
      .drive_strength = 0,
      .flags = kDifPinmuxPadAttrPullResistorEnable |
               kDifPinmuxPadAttrPullResistorUp};

  // set weak pull-ups for all the pins
  top_earlgrey_direct_pads_t spi_direct_pads[6] = {
      kTopEarlgreyDirectPadsSpiHost0Sd0, kTopEarlgreyDirectPadsSpiHost0Sd1,
      kTopEarlgreyDirectPadsSpiHost0Sd2, kTopEarlgreyDirectPadsSpiHost0Sd3,
      kTopEarlgreyDirectPadsSpiHost0Sck, kTopEarlgreyDirectPadsSpiHost0Csb};

  for (uint32_t i = 0; i <= ARRAYSIZE(spi_direct_pads); ++i) {
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(
        &pinmux, spi_direct_pads[i], kDifPinmuxPadKindDio, in_attr, &out_attr));
  }
}

bool test_main(void) {
  // enable pull-up on relevant pads
  enable_pull_up();

  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR), &spi_host));

  dif_spi_host_config_t config = {
      .spi_clock = (uint32_t)(kClockFreqHiSpeedPeripheralHz / 2),
      .peripheral_clock_freq_hz = (uint32_t)(kClockFreqHiSpeedPeripheralHz),
      .chip_select = {.idle = 2, .trail = 2, .lead = 2},
      .full_cycle = true,
      .cpha = true,
      .cpol = true};

  // Setup spi host configuration
  CHECK_DIF_OK(dif_spi_host_configure(&spi_host, config));

  uint32_t expected_data[DATA_SET_SIZE];
  uint32_t received_data[DATA_SET_SIZE];
  for (uint32_t i = 0; i < ARRAYSIZE(expected_data); ++i) {
    expected_data[i] = rand_testutils_gen32();
  }

  // Define the segments:
  // 1st segment, TX only, host sends out the first word.
  // 2nd segment, Bidirectional.  The external device begins sending back data
  // that it received. So it always lags the TX by 1 word.
  // 3rd segment, RX only, final word readback.
  dif_spi_host_segment_t host_operations[3] = {
      {.type = kDifSpiHostSegmentTypeTx,
       .tx = {.width = kDifSpiHostWidthStandard,
              .buf = &expected_data[0],
              .length = 4}},

      {.type = kDifSpiHostSegmentTypeBidirectional,
       .bidir = {.width = kDifSpiHostWidthStandard,
                 .txbuf = &expected_data[1],
                 .rxbuf = received_data,
                 .length = (DATA_SET_SIZE - 1) * sizeof(uint32_t)}},

      {.type = kDifSpiHostSegmentTypeRx,
       .tx = {.width = kDifSpiHostWidthStandard,
              .buf = &received_data[DATA_SET_SIZE - 1],
              .length = 4}},
  };

  // Enable spi host to actually talk to the outside world
  CHECK_DIF_OK(dif_spi_host_output_set_enabled(&spi_host, true));

  // Issue host transactions
  CHECK_DIF_OK(dif_spi_host_transaction(&spi_host, /*csid=*/0, host_operations,
                                        ARRAYSIZE(host_operations)));

  uint32_t err = 0;
  for (int32_t i = 0; i < ARRAYSIZE(expected_data); ++i) {
    if (received_data[i] != expected_data[i]) {
      err++;
      LOG_INFO("Received 0x%x, Expected 0x%x", received_data[i],
               expected_data[i]);
    }
  }

  return (err == 0);
}
