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
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Indicates the spi_host instance under test.
 *
 * This constant is backdoor_overwritten by the vseq.
 * (See comment in uart_tx_rx_test.c for details on 'static volatile const'
 * qualifiers)
 */
static volatile const uint8_t kSPIHostIdx = 0x0;

#define DATA_SET_SIZE 16

static dif_spi_host_t spi_host;
static dif_pinmux_t pinmux;

static const top_earlgrey_direct_pads_t spi_host0_direct_pads[6] = {
    kTopEarlgreyDirectPadsSpiHost0Sck,   // sck
    kTopEarlgreyDirectPadsSpiHost0Csb,   // csb
    kTopEarlgreyDirectPadsSpiHost0Sd3,   // sio[3]
    kTopEarlgreyDirectPadsSpiHost0Sd2,   // sio[2]
    kTopEarlgreyDirectPadsSpiHost0Sd1,   // sio[1]
    kTopEarlgreyDirectPadsSpiHost0Sd0};  // sio[0]

// pinmap defined in chip_if.sv (spi_device1_if)
static const top_earlgrey_muxed_pads_t spi_host1_muxed_pads[6] = {
    kTopEarlgreyMuxedPadsIob0,  // sck
    kTopEarlgreyMuxedPadsIob1,  // csb
    kTopEarlgreyMuxedPadsIob6,  // sio[3]
    kTopEarlgreyMuxedPadsIob5,  // sio[2]
    kTopEarlgreyMuxedPadsIob4,  // sio[1]
    kTopEarlgreyMuxedPadsIob3,  // sio[0]
};

// For spi_host1
// sck       output
// csb       output
// sio[0:3]  bidir (input+output)

/** To setup the pinmux using the enum's in top_earlgrey.h ...
 *
 *                                             - Choose corresponding pad/periph
 * from...
 *
 * dif_result_t dif_pinmux_output_select(...,
 *   dif_pinmux_index_t mio_pad_output,        | top_earlgrey_pinmux_mio_out_t
 *   dif_pinmux_index_t outsel)                | top_earlgrey_pinmux_outsel_t
 * dif_result_t dif_pinmux_input_select(...,
 *   dif_pinmux_index_t peripheral_input,      |
 * top_earlgrey_pinmux_peripheral_in_t dif_pinmux_index_t insel) |
 * top_earlgrey_pinmux_insel_t
 *
 */

typedef struct pinmux_select {
  dif_pinmux_index_t pad;
  dif_pinmux_index_t peripheral;
} pinmux_select_t;

static const pinmux_select_t pinmux_out_config[] = {
    // spi_host1
    {
        .pad = kTopEarlgreyPinmuxMioOutIob0,
        .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sck,  // SCK
    },
    {
        .pad = kTopEarlgreyPinmuxMioOutIob1,
        .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Csb,  // CSB
    },
    {
        .pad = kTopEarlgreyPinmuxMioOutIob3,
        .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sd0,  // sio[0]
    },
    {
        .pad = kTopEarlgreyPinmuxMioOutIob4,
        .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sd1,  // sio[1]
    },
    {
        .pad = kTopEarlgreyPinmuxMioOutIob5,
        .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sd2,  // sio[2]
    },
    {
        .pad = kTopEarlgreyPinmuxMioOutIob6,
        .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sd3,  // sio[3]
    },
};

static const pinmux_select_t pinmux_in_config[] = {
    // spi_host1
    {
        .pad = kTopEarlgreyPinmuxInselIob3,
        .peripheral = kTopEarlgreyPinmuxPeripheralInSpiHost1Sd0,  // sio[0]
    },
    {
        .pad = kTopEarlgreyPinmuxInselIob4,
        .peripheral = kTopEarlgreyPinmuxPeripheralInSpiHost1Sd1,  // sio[1]
    },
    {
        .pad = kTopEarlgreyPinmuxInselIob5,
        .peripheral = kTopEarlgreyPinmuxPeripheralInSpiHost1Sd2,  // sio[2]
    },
    {
        .pad = kTopEarlgreyPinmuxInselIob6,
        .peripheral = kTopEarlgreyPinmuxPeripheralInSpiHost1Sd3,  // sio[3]
    },
};

/**
 * Initialize the provided SPI host.
 */
void init_spi_host(dif_spi_host_t *spi_host,
                   uint32_t peripheral_clock_freq_hz) {
  dif_spi_host_config_t config = {
      .spi_clock = peripheral_clock_freq_hz / 2,
      .peripheral_clock_freq_hz = peripheral_clock_freq_hz,
      .chip_select = {.idle = 2, .trail = 2, .lead = 2},
      .full_cycle = true,
      .cpha = true,
      .cpol = true,
  };
  CHECK_DIF_OK(dif_spi_host_configure(spi_host, config));
  CHECK_DIF_OK(dif_spi_host_output_set_enabled(spi_host, /*enabled=*/true));
}

/**
 * Setup pads for spi_host0
 *
 * This peripheral is 'direct' connected to the pads.
 */
void setup_pads_spi_host0(void) {
  // set weak pull-ups for all the pads
  dif_pinmux_pad_attr_t out_attr;
  dif_pinmux_pad_attr_t in_attr = {
      .slew_rate = 0,
      .drive_strength = 0,
      .flags = kDifPinmuxPadAttrPullResistorEnable |
               kDifPinmuxPadAttrPullResistorUp};
  for (uint32_t i = 0; i <= ARRAYSIZE(spi_host0_direct_pads); ++i) {
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(&pinmux, spi_host0_direct_pads[i],
                                            kDifPinmuxPadKindDio, in_attr,
                                            &out_attr));
  }
}

/**
 * Setup pads and pinmux for spi_host0
 *
 * This peripheral is 'muxed', so configure the pinmux as well as pads.
 */
void setup_pinmux_pads_spi_host1(void) {
  // Set weak pull-ups for the pads
  dif_pinmux_pad_attr_t out_attr;
  dif_pinmux_pad_attr_t in_attr = {
      .slew_rate = 0,
      .drive_strength = 0,
      // set weak pull-ups for all the pads
      .flags = kDifPinmuxPadAttrPullResistorEnable |
               kDifPinmuxPadAttrPullResistorUp};
  for (uint32_t i = 0; i <= ARRAYSIZE(spi_host1_muxed_pads); ++i) {
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(&pinmux, spi_host1_muxed_pads[i],
                                            kDifPinmuxPadKindMio, in_attr,
                                            &out_attr));
  }

  // Setup Inputs
  for (int i = 0; i < ARRAYSIZE(pinmux_in_config); ++i) {
    pinmux_select_t setting = pinmux_in_config[i];
    CHECK_DIF_OK(
        dif_pinmux_input_select(&pinmux, setting.peripheral, setting.pad));
  }
  // Setup Outputs
  for (int i = 0; i < ARRAYSIZE(pinmux_out_config); ++i) {
    pinmux_select_t setting = pinmux_out_config[i];
    CHECK_DIF_OK(
        dif_pinmux_output_select(&pinmux, setting.pad, setting.peripheral));
  }
}

bool test_main(void) {
  // Initialize the pinmux.
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);

  // Setup pinmux if required, enable weak pull-up on relevant pads
  setup_pads_spi_host0();         // direct
  setup_pinmux_pads_spi_host1();  // muxed

  // Setup spi host configuration
  LOG_INFO("Testing spi_host%0d", kSPIHostIdx);
  uintptr_t base_addr;
  uint64_t clkHz;
  switch (kSPIHostIdx) {
    case 0: {
      base_addr = TOP_EARLGREY_SPI_HOST0_BASE_ADDR;
      clkHz = kClockFreqHiSpeedPeripheralHz;
      break;
    }
    case 1: {
      base_addr = TOP_EARLGREY_SPI_HOST1_BASE_ADDR;
      clkHz = kClockFreqPeripheralHz;
      break;
    }
    default:
      LOG_FATAL("Invalid kSPIHostIdx: %d", kSPIHostIdx);
      return false;
  }
  CHECK_DIF_OK(dif_spi_host_init(mmio_region_from_addr(base_addr), &spi_host));
  init_spi_host(&spi_host, (uint32_t)clkHz);

  // DV sync message
  LOG_INFO("spi host configuration complete");

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

  // Issue the transaction
  CHECK_DIF_OK(dif_spi_host_transaction(&spi_host, /*csid=*/0, host_operations,
                                        ARRAYSIZE(host_operations)));

  CHECK_ARRAYS_EQ(received_data, expected_data, ARRAYSIZE(expected_data));

  return true;
}
