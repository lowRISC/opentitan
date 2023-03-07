// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_FLASH_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_FLASH_TESTUTILS_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_spi_host.h"

typedef struct spi_flash_testutils_jedec_id {
  uint16_t device_id;
  uint8_t manufacturer_id;
  uint8_t continuation_len;
} spi_flash_testutils_jedec_id_t;

/**
 * Read out the JEDEC ID from the SPI flash.
 *
 * @param spih A SPI host handle.
 * @param[out] id A pointer to where to store the ID.
 */
void spi_flash_testutils_read_id(dif_spi_host_t *spih,
                                 spi_flash_testutils_jedec_id_t *id);

/**
 * Read out the SFDP from the indicated address and place the table contents
 * into the buffer.
 *
 * @param spih A SPI host handle.
 * @param buffer A pointer to a buffer that will hold the SFDP contents.
 * @param length The number of bytes to write into `buffer`.
 */
void spi_flash_testutils_read_sfdp(dif_spi_host_t *spih, uint32_t address,
                                   uint8_t *buffer, size_t length);

typedef enum spi_flash_status_bit {
  kSpiFlashStatusBitWip = 0x1,
  kSpiFlashStatusBitWel = 0x2,
} spi_flash_status_bit_t;

/**
 * Spin wait until a Read Status command shows the downstream SPI flash is no
 * longer busy.
 */
void spi_flash_testutils_wait_until_not_busy(dif_spi_host_t *spih);

/**
 * Issue the Write Enable command to the downstream SPI flash.
 */
void spi_flash_testutils_issue_write_enable(dif_spi_host_t *spih);

/**
 * Perform full Chip Erase sequence, including the Write Enable and Chip Erase
 * commands, and poll the status registers in a loop until the WIP bit clears.
 *
 * Does not return until the erase completes.
 *
 * @param spih A SPI host handle.
 */
void spi_flash_testutils_erase_chip(dif_spi_host_t *spih);

/**
 * Perform full Sector Erase sequence, including the Write Enable and Sector
 * Erase commands, and poll the status registers in a loop until the WIP bit
 * clears.
 *
 * Does not return until the erase completes.
 *
 * @param spih A SPI host handle.
 * @param address An address contained within the desired sector.
 * @param addr_is_4b True if `address` is 4 bytes long, else 3 bytes.
 */
void spi_flash_testutils_erase_sector(dif_spi_host_t *spih, uint32_t address,
                                      bool addr_is_4b);

/**
 * Perform full Page Program sequence, including the Write Enable and Page
 * Program commands, and poll the status registers in a loop until the WIP bit
 * clears.
 *
 * Does not return until the programming operation completes.
 *
 * @param spih A SPI host handle.
 * @param payload A pointer to the payload to be written to the page.
 * @param length Number of bytes in the payload. Must be less than or equal to
 *               256 bytes.
 * @param address The start address where the payload programming should begin.
 *                Note that an address + length that crosses a page boundary may
 *                wrap around to the start of the page.
 * @param addr_is_4b True if `address` is 4 bytes long, else 3 bytes.
 */
void spi_flash_testutils_program_page(dif_spi_host_t *spih, uint8_t *payload,
                                      size_t length, uint32_t address,
                                      bool addr_is_4b);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_FLASH_TESTUTILS_H_
