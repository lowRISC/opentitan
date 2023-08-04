// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/spi_host_testutils.h"

#include "sw/device/lib/testing/test_framework/check.h"

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
