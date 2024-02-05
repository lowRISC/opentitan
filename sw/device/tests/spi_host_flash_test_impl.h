// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_SPI_HOST_FLASH_TEST_IMPL_H_
#define OPENTITAN_SW_DEVICE_TESTS_SPI_HOST_FLASH_TEST_IMPL_H_

#include "sw/ip/spi_host/dif/dif_spi_host.h"
#include "sw/lib/sw/device/base/status.h"

/**
 * Send the sw_reset command.
 *
 * @param spi A spi host handler.
 * @return status_t containing either OK or an error.
 */
status_t test_software_reset(dif_spi_host_t *spi);

/**
 * Read the sfdp header and check the signature.
 *
 * @param spi A spi host handler.
 * @return status_t containing either OK or an error.
 */
status_t test_read_sfdp(dif_spi_host_t *spi);

/**
 * Send the sector erase command, read a page that it was erased.
 *
 * @param spi A spi host handler.
 * @return status_t containing either OK or an error.
 */
status_t test_sector_erase(dif_spi_host_t *spi);

/**
 * Read jedec and check the device_id and manufacturer_id.
 *
 * @param spi A spi host handler.
 * @param device_id The expected device_id.
 * @param manufacture_id The expected manufacture_id.
 * @return status_t containing either OK or an error.
 */
status_t test_read_jedec(dif_spi_host_t *spi, uint16_t device_id,
                         uint16_t manufacture_id);

/**
 * Send the enable quad mode command.
 *
 * @param spi A spi host handler.
 * @return status_t containing either OK or an error.
 */
status_t test_enable_quad_mode(dif_spi_host_t *spi);

/**
 * Program a complete page and read it back to verify.
 *
 * @param spi A spi host handler.
 * @return status_t containing either OK or an error.
 */
status_t test_page_program(dif_spi_host_t *spi);

/**
 * Perform a fast read operation.
 *
 * @param spi A spi host handler.
 * @return status_t containing either OK or an error.
 */
status_t test_fast_read(dif_spi_host_t *spi);

/**
 * Perform a dual read operation.
 *
 * @param spi A spi host handler.
 * @return status_t containing either OK or an error.
 */
status_t test_dual_read(dif_spi_host_t *spi);

/**
 * Perform a quad read operation.
 *
 * @param spi A spi host handler.
 * @return status_t containing either OK or an error.
 */
status_t test_quad_read(dif_spi_host_t *spi);

/**
 * Check if the flash supports 4-byte addressing.
 *
 * @param spi A spi host handler.
 * @return True if 4-byte addressing mode is supported.
 */
bool is_4_bytes_address_mode_supported(void);

/**
 * Enable 4-byte addressing mode, write and read to a page that needs 4 bytes to
 * be addressed and disables the 4-bytes addressing mode.
 *
 * @param spi A spi host handler.
 * @return status_t containing either OK or an error.
 */
status_t test_4bytes_address(dif_spi_host_t *spi);

/**
 * Write and read in order to compare a page using quad mode.
 *
 * @param spi A spi host handler.
 * @param opcode The opcode used by the part-number for quad page program.
 * @return status_t containing either OK or an error.
 */
status_t test_page_program_quad(dif_spi_host_t *spi, uint8_t opcode);

/**
 * Erase a 32kB block and read it back to check if was erased.
 *
 * @param spi A spi host handler.
 * @return status_t containing either OK or an error.
 */
status_t test_erase_32k_block(dif_spi_host_t *spi);

/**
 * Erase a 64kB block and read it back to check if was erased.
 *
 * @param spi A spi host handler.
 * @return status_t containing either OK or an error.
 */
status_t test_erase_64k_block(dif_spi_host_t *spi);

#endif  // OPENTITAN_SW_DEVICE_TESTS_SPI_HOST_FLASH_TEST_IMPL_H_
