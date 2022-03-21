// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_DEVICE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_DEVICE_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Bit field definitions for JEDEC device ID.
 *
 * Note: spi_device sends bits 7:0 of the device ID first.
 */
#define SPI_DEVICE_DEV_ID_CHIP_REV_FIELD \
  ((bitfield_field32_t){.mask = 0x7, .index = 0})
#define SPI_DEVICE_DEV_ID_ROM_BOOTSTRAP_BIT 3
#define SPI_DEVICE_DEV_ID_CHIP_GEN_FIELD \
  ((bitfield_field32_t){.mask = 0xf, .index = 4})
#define SPI_DEVICE_DEV_ID_DENSITY_FIELD \
  ((bitfield_field32_t){.mask = 0xff, .index = 8})

enum {
  /**
   * lowRISC's manufacturer ID from the JEDEC JEP106BE standard.
   */
  kSpiDeviceJedecContCode = 0x7f,
  kSpiDeviceJedecContCodeCount = 12,
  kSpiDeviceJedecManufId = 0xef,
  /**
   * LSB of the 2-byte device ID.
   */
  kSpiDeviceJedecDensity = 0x0a,
  /**
   * READ_JECEC_ID command.
   *
   * This command is handled by the spi_device. Upon receiving this instruction,
   * spi_device sends `kSpiDeviceJedecContCodeCount` repetitions of
   * `kSpiDeviceJedecContCode`, followed by `kSpiDeviceJedecManufId` and 2 bytes
   * of device id.
   */
  kSpiDeviceCmdReadJedecId = 0x9f,
};

/**
 * Initializes the spi_device in flash mode for bootstrap in mask ROM.
 *
 * This function initializes the spi_device in the following configuration:
 * - CPOL = 0, CPHA = 0 (clock low in idle, data sampled on rising clock edge).
 * - MSb-first bit order for RX and TX.
 * - Flash mode with 3-byte addressing.
 * - Commands:
 *   - READ_JEDEC_ID
 */
void spi_device_init(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_DEVICE_H_
