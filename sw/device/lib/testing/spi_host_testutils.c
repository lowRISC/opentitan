// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/spi_host_testutils.h"

#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// `extern` declarations to give the inline functions in the
// corresponding header a link location.
extern status_t spi_host_testutils_is_active(dif_spi_host_t *spi_host);

status_t spi_host_testutils_flush(dif_spi_host_t *spi_host) {
  dif_spi_host_status_t status;
  uint8_t dummy[sizeof(uint32_t)];
  TRY(dif_spi_host_get_status(spi_host, &status));
  while (!status.rx_empty) {
    TRY(dif_spi_host_fifo_read(spi_host, &dummy, sizeof(dummy)));
    TRY(dif_spi_host_get_status(spi_host, &status));
  }
  return OK_STATUS();
}

status_t spi_host1_pinmux_connect_to_bob(const dif_pinmux_t *pinmux,
                                         dif_pinmux_index_t csb_outsel) {
  // CSB.
  TRY(dif_pinmux_output_select(pinmux, csb_outsel,
                               kTopEarlgreyPinmuxOutselSpiHost1Csb));
  // SCLK.
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoa3,
                               kTopEarlgreyPinmuxOutselSpiHost1Sck));
  // SD0.
  TRY(dif_pinmux_input_select(pinmux, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd0,
                              kTopEarlgreyPinmuxInselIoa5));
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoa5,
                               kTopEarlgreyPinmuxOutselSpiHost1Sd0));

  // SD1.
  TRY(dif_pinmux_input_select(pinmux, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd1,
                              kTopEarlgreyPinmuxInselIoa4));
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoa4,
                               kTopEarlgreyPinmuxOutselSpiHost1Sd1));
  // SD2.
  TRY(dif_pinmux_input_select(pinmux, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd2,
                              kTopEarlgreyPinmuxInselIoa8));
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoa8,
                               kTopEarlgreyPinmuxOutselSpiHost1Sd2));
  // SD3.
  TRY(dif_pinmux_input_select(pinmux, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd3,
                              kTopEarlgreyPinmuxInselIoa7));
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIoa7,
                               kTopEarlgreyPinmuxOutselSpiHost1Sd3));
  return OK_STATUS();
}
