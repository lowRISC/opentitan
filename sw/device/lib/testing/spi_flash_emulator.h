// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_FLASH_EMULATOR_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_FLASH_EMULATOR_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/ip/spi_device/dif/dif_spi_device.h"
#include "sw/ip/spi_host/dif/dif_spi_host.h"
#include "sw/lib/sw/device/base/status.h"

/**
 * Emulate a SPI eeprom.
 *
 * @param spih A SPI host handle.
 * @param spid A SPI device handle.
 * @return A status.
 */
status_t spi_flash_emulator(dif_spi_host_t *spih,
                            dif_spi_device_handle_t *spid);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_FLASH_EMULATOR_H_
