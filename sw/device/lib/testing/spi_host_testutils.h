// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_HOST_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_HOST_TESTUTILS_H_

#include <assert.h>
#include <stdint.h>

#include "hw/top/dt/api.h"  // Generated
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_spi_host.h"

/**
 * Configure the pad attributes of the dedicated pads of SPI Host 0.
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

#if defined(OPENTITAN_IS_EARLGREY)
/**
 * Connect the spi host 1 to the BoB.
 *
 * spi_host1 reaches each signal on a single pad, csb[0] is on IOB0. The BoB
 * selects the flash device itself.
 *
 * @param pinmux A pinmux handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t spi_host1_pinmux_connect_to_bob(const dif_pinmux_t *pinmux);
#elif defined(OPENTITAN_IS_DARJEELING)
// Darjeeling only has a single SPI host
#else
#error "spi_host_testutils does not support this top"
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_HOST_TESTUTILS_H_
