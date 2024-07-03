// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_LIB_SW_DEVICE_SILICON_CREATOR_SPI_NOR_FLASH_H_
#define OPENTITAN_SW_LIB_SW_DEVICE_SILICON_CREATOR_SPI_NOR_FLASH_H_

#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/silicon_creator/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initialize the SPI NOR Flash memory.
 *
 * Assumes that the SPI_HOST controller is already initialized.
 * This function will detect if a flash memory is present and reset it.
 *
 * @param csid The chip-select ID of the flash memory.
 * @param jedec_id[out] JEDEC ID for the detected flash on success
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t spi_nor_flash_init(uint32_t csid, uint32_t *jedec_id);

/**
 * Reads data from the flash memory.
 *
 * @param csid The chip-select ID of the flash memory.
 * @param addr Address to read from.
 * @param byte_count Number of bytes to read.
 * @param[out] data Buffer to store the read data.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t spi_nor_flash_read(uint32_t csid, uint32_t addr,
                               uint32_t byte_count, void *data);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_LIB_SW_DEVICE_SILICON_CREATOR_SPI_NOR_FLASH_H_
