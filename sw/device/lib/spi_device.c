// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/spi_device.h"

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_spi_device.h"

#define SPI_DEVICE0_BASE_ADDR 0x40020000

dif_spi_device_t spi;

void spid_init(void) {
  dif_spi_device_init((dif_spi_device_config_t) {
    .base_addr = reg32_from_addr(SPI_DEVICE0_BASE_ADDR),
  }, &spi);
}

uint32_t spid_send(void *data, uint32_t len_bytes) {
  return dif_spi_device_send(&spi, data, len_bytes);
}

uint32_t spid_read_nb(void *data, uint32_t len_bytes) {
  return dif_spi_device_recv(&spi, data, len_bytes);
}

uint32_t spid_bytes_available(void) {
  return dif_spi_device_bytes_pending(&spi);
}
