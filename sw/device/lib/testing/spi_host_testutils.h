// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_HOST_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_HOST_TESTUTILS_H_

#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_spi_host.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

typedef enum spi_pinmux_platform_id {
  kSpiPinmuxPlatformIdCw310 = 0,
  kSpiPinmuxPlatformIdCw340,
  kSpiPinmuxPlatformIdTeacup,
  kSpiPinmuxPlatformIdCount,
} spi_pinmux_platform_id_t;

/*
 * The SPI host pads for which `spi_host_testutils_configure_host0_pad_attrs()`
 * configures the pad attributes.
 */
static const top_earlgrey_direct_pads_t spi_host0_direct_pads[6] = {
    kTopEarlgreyDirectPadsSpiHost0Sck,  // sck
    kTopEarlgreyDirectPadsSpiHost0Csb,  // csb
    kTopEarlgreyDirectPadsSpiHost0Sd3,  // sio[3]
    kTopEarlgreyDirectPadsSpiHost0Sd2,  // sio[2]
    kTopEarlgreyDirectPadsSpiHost0Sd1,  // sio[1]
    kTopEarlgreyDirectPadsSpiHost0Sd0   // sio[0]
};

/**
 * Configure the pad attributes of SPI Host 0.
 *
 * @return A status_t indicating success or failure configuring the pad
 * attributes.
 */
OT_WARN_UNUSED_RESULT
status_t spi_host_testutils_configure_host0_pad_attrs(dif_pinmux_t *pinmux);

/**
 * Return True if spi host is active.
 *
 * @param spi_host A spi host handle.
 * @return `Ok(res)` Where `res` is true if spi host is active, or `kInternal`
 * in case of an error.
 */
OT_WARN_UNUSED_RESULT
static inline status_t spi_host_testutils_is_active(dif_spi_host_t *spi_host) {
  dif_spi_host_status_t status;
  TRY(dif_spi_host_get_status(spi_host, &status));
  return OK_STATUS(status.active);
}

/**
 * Flush the rx fifo.
 *
 * @param spi_host A spi host handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t spi_host_testutils_flush(dif_spi_host_t *spi_host);

/**
 * Connect the spi host 1 to the BoB.
 *
 * @param pinmux A pinmux handle.
 * @param csb_outsel The chip select pin, this should be one of the eight
 * devices in the BoB connected to the bus. See ::top_earlgrey_pinmux_mio_out_t.
 * @param platform_id The ID of the platform where the test in running.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t spi_host1_pinmux_connect_to_bob(const dif_pinmux_t *pinmux,
                                         dif_pinmux_index_t csb_outsel,
                                         spi_pinmux_platform_id_t platform_id);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_HOST_TESTUTILS_H_
