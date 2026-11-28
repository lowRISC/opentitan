// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/spi_host_testutils.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

// Writes the pad attributes. If the platform does not support the slew rate or
// drive strength, falls back to the supported values and keeps them in `attr`
// so that the same attributes are used for all pads.
static void write_pad_attrs(dif_pinmux_t *pinmux, dt_pad_t pad,
                            dif_pinmux_pad_attr_t *attr) {
  dif_pinmux_pad_attr_t out_attr;
  if (dif_pinmux_pad_write_attrs_dt(pinmux, pad, *attr, &out_attr) ==
      kDifError) {
    if (out_attr.slew_rate != attr->slew_rate) {
      LOG_INFO("Specified slew rate not supported, trying supported slew rate");
      attr->slew_rate = out_attr.slew_rate;
    }
    if (out_attr.drive_strength != attr->drive_strength) {
      LOG_INFO(
          "Specified drive strength not supported, trying supported drive "
          "strength");
      attr->drive_strength = out_attr.drive_strength;
    }
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs_dt(pinmux, pad, *attr, &out_attr));
    // Here attr is not reset to implement the fallthrough.
  }
}

status_t spi_host_testutils_configure_host0_pad_attrs(dif_pinmux_t *pinmux) {
  // Set fast slew rate and strong drive strength for the SPI host0 pads.
  dif_pinmux_pad_attr_t attr = {
      .slew_rate = 1,
      .drive_strength = 3,
      // Set weak pull-ups for all the pads.
      .flags =
          kDifPinmuxPadAttrPullResistorEnable | kDifPinmuxPadAttrPullResistorUp,
  };
#if defined(OPENTITAN_IS_EARLGREY)
  // Earlgrey has muxed SPI host0 pads, each signal can only reach its own pad.
  static const dt_pad_t kSpiHost0Pads[] = {
      kDtPadSpiHostD0, kDtPadSpiHostD1,  kDtPadSpiHostD2,
      kDtPadSpiHostD3, kDtPadSpiHostClk, kDtPadSpiHostCsL,
  };
  for (size_t i = 0; i < ARRAYSIZE(kSpiHost0Pads); ++i) {
    write_pad_attrs(pinmux, kSpiHost0Pads[i], &attr);
  }
#else
  for (uint32_t i = 0; i < kDtSpiHostPeriphIoCount; ++i) {
    dt_periph_io_t periph_io =
        dt_spi_host_periph_io(kDtSpiHost0, (dt_spi_host_periph_io_t)i);
    // Some chip select lines of SPI host0 may be muxed instead of dedicated.
    if (dt_periph_io_type(periph_io) != kDtPeriphIoTypeDio) {
      continue;
    }
    write_pad_attrs(pinmux, dt_periph_io_dio_pad(periph_io), &attr);
  }
#endif
  return OK_STATUS();
}

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

#if defined(OPENTITAN_IS_EARLGREY)
/**
 * Define a spi pinmux configuration.
 */
typedef struct spi_host1_pinmux_pads {
  dt_pad_t csb;
  dt_pad_t clk;
  dt_pad_t sd0;
  dt_pad_t sd1;
  dt_pad_t sd2;
  dt_pad_t sd3;
} spi_host1_pinmux_pads_t;

/**
 * spi host 1 reaches each signal on a single pad, the same on every platform.
 */
static const spi_host1_pinmux_pads_t kSpiHost1Pads = {
    .csb = kDtPadIob0,
    .clk = kDtPadIob3,
    .sd0 = kDtPadIob1,
    .sd1 = kDtPadIob2,
    .sd2 = kDtPadIob4,
    .sd3 = kDtPadIob6,
};

status_t spi_host1_pinmux_connect_to_bob(const dif_pinmux_t *pinmux) {
  const spi_host1_pinmux_pads_t *pads = &kSpiHost1Pads;

  // CSB.
  dt_periph_io_t csb =
      dt_spi_host_periph_io(kDtSpiHost1, kDtSpiHostPeriphIoCsb0);
  TRY(dif_pinmux_mio_select_output(pinmux, pads->csb, csb));
  // SCK.
  dt_periph_io_t sck =
      dt_spi_host_periph_io(kDtSpiHost1, kDtSpiHostPeriphIoSck);
  TRY(dif_pinmux_mio_select_output(pinmux, pads->clk, sck));
  // SD0.
  dt_periph_io_t sd0 =
      dt_spi_host_periph_io(kDtSpiHost1, kDtSpiHostPeriphIoSd0);
  TRY(dif_pinmux_mio_select_input(pinmux, sd0, pads->sd0));
  TRY(dif_pinmux_mio_select_output(pinmux, pads->sd0, sd0));
  // SD1.
  dt_periph_io_t sd1 =
      dt_spi_host_periph_io(kDtSpiHost1, kDtSpiHostPeriphIoSd1);
  TRY(dif_pinmux_mio_select_input(pinmux, sd1, pads->sd1));
  TRY(dif_pinmux_mio_select_output(pinmux, pads->sd1, sd1));
  // SD2.
  dt_periph_io_t sd2 =
      dt_spi_host_periph_io(kDtSpiHost1, kDtSpiHostPeriphIoSd2);
  TRY(dif_pinmux_mio_select_input(pinmux, sd2, pads->sd2));
  TRY(dif_pinmux_mio_select_output(pinmux, pads->sd2, sd2));
  // SD3.
  dt_periph_io_t sd3 =
      dt_spi_host_periph_io(kDtSpiHost1, kDtSpiHostPeriphIoSd3);
  TRY(dif_pinmux_mio_select_input(pinmux, sd3, pads->sd3));
  TRY(dif_pinmux_mio_select_output(pinmux, pads->sd3, sd3));
  return OK_STATUS();
}
#elif defined(OPENTITAN_IS_DARJEELING)
// Darjeeling only has a single SPI host
#else
#error "spi_host_testutils does not support this top"
#endif
