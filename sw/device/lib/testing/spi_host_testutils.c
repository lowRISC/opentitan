// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/spi_host_testutils.h"

#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

status_t spi_host_testutils_configure_host0_pad_attrs(dif_pinmux_t *pinmux) {
  // Set fast slew rate and strong drive strengh for SPI host0 pads.
  dif_pinmux_pad_attr_t out_attr;
  dif_pinmux_pad_attr_t in_attr = {
      .slew_rate = 1,
      .drive_strength = 3,
      // Set weak pull-ups for all the pads.
      .flags = kDifPinmuxPadAttrPullResistorEnable |
               kDifPinmuxPadAttrPullResistorUp};
  dif_result_t res;
  for (uint32_t i = 0; i < kDtSpiHostPeriphIoCount; ++i) {
    dt_periph_io_t periph_io =
        dt_spi_host_periph_io(kDtSpiHost0, (dt_spi_host_periph_io_t)i);
    dt_pad_t pad = dt_periph_io_dio_pad(periph_io);
    res = dif_pinmux_pad_write_attrs_dt(pinmux, pad, in_attr, &out_attr);
    if (res == kDifError) {
      // Some target platforms may not support the specified value for slew rate
      // and drive strength. If that's the case, use the values actually
      // supported.
      if (out_attr.slew_rate != in_attr.slew_rate) {
        LOG_INFO(
            "Specified slew rate not supported, trying supported slew rate");
        in_attr.slew_rate = out_attr.slew_rate;
      }
      if (out_attr.drive_strength != in_attr.drive_strength) {
        LOG_INFO(
            "Specified drive strength not supported, trying supported drive "
            "strength");
        in_attr.drive_strength = out_attr.drive_strength;
      }
      CHECK_DIF_OK(
          dif_pinmux_pad_write_attrs_dt(pinmux, pad, in_attr, &out_attr));
      // Note: fallthrough with the modified `in_attr` so that the same
      // attributes are used for all pads.
    }
  }
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
  dt_pad_t clk;
  dt_pad_t sd0;
  dt_pad_t sd1;
  dt_pad_t sd2;
  dt_pad_t sd3;
} spi_host1_pinmux_pads_t;

/**
 * This table stores spi host 1 pin mappings of different platforms.
 * This is used to connect spi host 1 to mio pins based on the platform.
 */
static const spi_host1_pinmux_pads_t kSpiHost1PinmuxMap[] = {
    [kSpiPinmuxPlatformIdCw310] =
        {
            .clk = kDtPadIoa3,
            .sd0 = kDtPadIoa5,
            .sd1 = kDtPadIoa4,
            .sd2 = kDtPadIoa8,
            .sd3 = kDtPadIoa7,
        },
    [kSpiPinmuxPlatformIdCw340] =
        {
            .clk = kDtPadIoa3,
            .sd0 = kDtPadIoa5,
            .sd1 = kDtPadIoa4,
            .sd2 = kDtPadIoa8,
            .sd3 = kDtPadIoa7,
        },
    [kSpiPinmuxPlatformIdTeacup] =
        {
            .clk = kDtPadIoa3,
            .sd0 = kDtPadIoa4,
            .sd1 = kDtPadIoa5,
            .sd2 = kDtPadIoa8,
            .sd3 = kDtPadIoa7,
        },
};

status_t spi_host1_pinmux_connect_to_bob(const dif_pinmux_t *pinmux,
                                         dt_pad_t csb_outsel,
                                         spi_pinmux_platform_id_t platform_id) {
  TRY_CHECK(platform_id < kSpiPinmuxPlatformIdCount);
  const spi_host1_pinmux_pads_t *platform = &kSpiHost1PinmuxMap[platform_id];

  // CSB.
  dt_periph_io_t csb =
      dt_spi_host_periph_io(kDtSpiHost1, kDtSpiHostPeriphIoCsb);
  TRY(dif_pinmux_mio_select_output(pinmux, csb_outsel, csb));
  // SCK.
  dt_periph_io_t sck =
      dt_spi_host_periph_io(kDtSpiHost1, kDtSpiHostPeriphIoSck);
  TRY(dif_pinmux_mio_select_output(pinmux, platform->clk, sck));
  // SD0.
  dt_periph_io_t sd0 =
      dt_spi_host_periph_io(kDtSpiHost1, kDtSpiHostPeriphIoSd0);
  TRY(dif_pinmux_mio_select_input(pinmux, sd0, platform->sd0));
  TRY(dif_pinmux_mio_select_output(pinmux, platform->sd0, sd0));
  // SD1.
  dt_periph_io_t sd1 =
      dt_spi_host_periph_io(kDtSpiHost1, kDtSpiHostPeriphIoSd1);
  TRY(dif_pinmux_mio_select_input(pinmux, sd1, platform->sd1));
  TRY(dif_pinmux_mio_select_output(pinmux, platform->sd1, sd1));
  // SD2.
  dt_periph_io_t sd2 =
      dt_spi_host_periph_io(kDtSpiHost1, kDtSpiHostPeriphIoSd2);
  TRY(dif_pinmux_mio_select_input(pinmux, sd2, platform->sd2));
  TRY(dif_pinmux_mio_select_output(pinmux, platform->sd2, sd2));
  // SD3.
  dt_periph_io_t sd3 =
      dt_spi_host_periph_io(kDtSpiHost1, kDtSpiHostPeriphIoSd3);
  TRY(dif_pinmux_mio_select_input(pinmux, sd3, platform->sd3));
  TRY(dif_pinmux_mio_select_output(pinmux, platform->sd3, sd3));
  return OK_STATUS();
}
#elif defined(OPENTITAN_IS_DARJEELING)
// Darjeeling only has a single SPI host
#else
#error "spi_host_testutils does not support this top"
#endif
