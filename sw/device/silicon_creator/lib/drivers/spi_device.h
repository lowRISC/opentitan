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
  // TODO(#11740): Auto-generated macros for SFDP offset and size.
  /**
   * Size of the SFDP area in spi_device buffer in bytes.
   *
   * spi_device provides 256 bytes for the SFDP table.
   */
  kSpiDeviceSfdpAreaNumBytes = 256,
  /**
   * Offset of the SFDP area in spi_device buffer.
   */
  kSpiDeviceSfdpAreaOffset = 0xc00,
  /**
   * Size of the JEDEC Basic Flash Parameter Table (BFPT) in words.
   *
   * Note: JESD261F 6.4.1 states that this
   */
  kSpiDeviceBfptNumWords = 23,
  /**
   * Size of the SFDP table in words.
   */
  kSpiDeviceSfdpTableNumWords = 27,
  /**
   * READ_JEDEC_ID command.
   *
   * This command is handled by the spi_device. Upon receiving this instruction,
   * spi_device sends `kSpiDeviceJedecContCodeCount` repetitions of
   * `kSpiDeviceJedecContCode`, followed by `kSpiDeviceJedecManufId` and 2 bytes
   * of device id.
   */
  kSpiDeviceCmdReadJedecId = 0x9f,
  /**
   * READ_SFDP command.
   *
   * This commond is handled by the spi_device. Upon receiving this instruction,
   * 3 bytes of address (all zeroes), and 8 dummy cycles; spi_device sends
   * `kSpiDeviceSfdpTable` from its buffer.
   */
  kSpiDeviceCmdReadSfdp = 0x5a,
  /**
   * SECTOR_ERASE command.
   */
  kSpiDeviceCmdSectorErase = 0x20,
};

/**
 * SFDP header (JESD216F 6.2).
 */
typedef struct spi_device_sfdp_header {
  /**
   * 32-bit SFDP signature that indicates the presence of a SFDP table
   * (JESD216F 6.2.1).
   */
  uint32_t signature;
  /**
   * SFDP major revision number (JESD216F 6.2.2).
   */
  uint8_t minor_revision;
  /**
   * SFDP minor revision number (JESD216F 6.2.2).
   */
  uint8_t major_revision;
  /**
   * Number of parameter headers, zero-based (JESD216F 6.2.2).
   */
  uint8_t param_count;
  /**
   * SFDP access protocol (JESD216F 6.2.3).
   */
  uint8_t access_protocol;
} spi_device_sfdp_header_t;
OT_ASSERT_MEMBER_OFFSET(spi_device_sfdp_header_t, signature, 0);
OT_ASSERT_MEMBER_OFFSET(spi_device_sfdp_header_t, minor_revision, 4);
OT_ASSERT_MEMBER_OFFSET(spi_device_sfdp_header_t, major_revision, 5);
OT_ASSERT_MEMBER_OFFSET(spi_device_sfdp_header_t, param_count, 6);
OT_ASSERT_MEMBER_OFFSET(spi_device_sfdp_header_t, access_protocol, 7);
OT_ASSERT_SIZE(spi_device_sfdp_header_t, 8);

/**
 * SFDP parameter header (JESD216F 6.3).
 */
typedef struct spi_device_param_header {
  /**
   * LSB of the parameter ID that indicates parameter table ownership and type
   * (JESD216F 6.3.1, 6.3.3).
   */
  uint8_t param_id_lsb;
  /**
   * Parameter table minor revision number (JESD216F 6.3.1).
   */
  uint8_t minor_revision;
  /**
   * Parameter table major revision number (JESD216F 6.3.1).
   */
  uint8_t major_revision;
  /**
   * Length of the parameter table in words, one-based (JESD216F 6.3.1).
   */
  uint8_t table_word_count;
  /**
   * Word-aligned byte offset of the corresponding parameter table from the
   * start of the SFDP table (JESD216F 6.3.2).
   */
  uint8_t table_pointer[3];
  /**
   * MSB of the parameter ID that indicates parameter table ownership and type
   * (JESD216F 6.3.2, 6.3.3).
   */
  uint8_t param_id_msb;
} spi_device_param_header_t;
OT_ASSERT_MEMBER_OFFSET(spi_device_param_header_t, param_id_lsb, 0);
OT_ASSERT_MEMBER_OFFSET(spi_device_param_header_t, minor_revision, 1);
OT_ASSERT_MEMBER_OFFSET(spi_device_param_header_t, major_revision, 2);
OT_ASSERT_MEMBER_OFFSET(spi_device_param_header_t, table_word_count, 3);
OT_ASSERT_MEMBER_OFFSET(spi_device_param_header_t, table_pointer, 4);
OT_ASSERT_MEMBER_OFFSET(spi_device_param_header_t, param_id_msb, 7);
OT_ASSERT_SIZE(spi_device_param_header_t, 8);

/**
 * Basic Flash Parameter Table (BFPT) (JESD216F 6.4).
 *
 * This is a mandatory table defined by JEDEC that identifies some of the basic
 * features of a SPI protocol flash memory device.
 */
typedef struct spi_device_bfpt {
  uint32_t data[kSpiDeviceBfptNumWords];
} spi_device_bfpt_t;
OT_ASSERT_SIZE(spi_device_bfpt_t, 92);
static_assert(sizeof(spi_device_bfpt_t) ==
                  kSpiDeviceBfptNumWords * sizeof(uint32_t),
              "`kSpiDeviceBfptNumWords` is incorrect");

/**
 * SFDP table.
 */
typedef struct spi_device_sfdp_table {
  /**
   * SFDP header.
   */
  spi_device_sfdp_header_t sfdp_header;
  /**
   * Parameter header for the Basic Flash Parameters Table (BFPT).
   */
  spi_device_param_header_t bfpt_header;
  /**
   * Basic Flash Parameters Table (BFPT).
   */
  spi_device_bfpt_t bfpt;
} spi_device_sfdp_table_t;
OT_ASSERT_MEMBER_OFFSET(spi_device_sfdp_table_t, sfdp_header, 0);
OT_ASSERT_MEMBER_OFFSET(spi_device_sfdp_table_t, bfpt_header, 8);
OT_ASSERT_MEMBER_OFFSET(spi_device_sfdp_table_t, bfpt, 16);
OT_ASSERT_SIZE(spi_device_sfdp_table_t, 108);
static_assert(sizeof(spi_device_sfdp_table_t) <= kSpiDeviceSfdpAreaNumBytes,
              "SFDP table must fit in the space provided by spi_device");
static_assert(sizeof(spi_device_sfdp_table_t) ==
                  kSpiDeviceSfdpTableNumWords * sizeof(uint32_t),
              "`kSpiDeviceSfdpTableNumWords` is incorrect");

// Note: Declared here to be able to use in tests.
extern const spi_device_sfdp_table_t kSpiDeviceSfdpTable;

/**
 * Initializes the spi_device in flash mode for bootstrap in mask ROM.
 *
 * This function initializes the spi_device in the following configuration:
 * - CPOL = 0, CPHA = 0 (clock low in idle, data sampled on rising clock edge).
 * - MSb-first bit order for RX and TX.
 * - Flash mode with 3-byte addressing.
 * - `kSpiDeviceSfdpTable` written to the SFDP area in the buffer.
 * - Commands:
 *   - READ_JEDEC_ID
 *   - READ_SFDP
 */
void spi_device_init(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_DEVICE_H_
