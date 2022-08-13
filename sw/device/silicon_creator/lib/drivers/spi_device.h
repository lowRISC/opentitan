// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_DEVICE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_DEVICE_H_

#include <stdalign.h>
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
   *
   * Density is expressed as log2(flash size in bytes).
   */
  kSpiDeviceJedecDensity = 20,
  /**
   * Size of the JEDEC Basic Flash Parameter Table (BFPT) in words.
   */
  kSpiDeviceBfptNumWords = 23,
  /**
   * Size of the SFDP table in words.
   */
  kSpiDeviceSfdpTableNumWords = 27,
  /**
   * Address value used when a command does not have an address.
   *
   * Since the spi_device is configured to support only the 3-byte addressing
   * mode this value is not a valid address.
   */
  kSpiDeviceNoAddress = UINT32_MAX,
};

// TODO(#11740): Auto-generated macros for HW constants.
enum {
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
   * Offset of the payload area in spi_device buffer.
   */
  kSpiDevicePayloadAreaOffset = 0xd00,
  /**
   * Size of the payload area in spi_device buffer in bytes.
   */
  kSpiDevicePayloadAreaNumBytes = 256,
  /**
   * Size of the payload area in spi_device buffer in words.
   */
  kSpiDevicePayloadAreaNumWords =
      kSpiDevicePayloadAreaNumBytes / sizeof(uint32_t),
  /**
   * Index of the WEL bit in flash status register.
   */
  kSpiDeviceWelBit = 1,
};

/**
 * Supported SPI flash command opcodes.
 *
 * SPI flash commands consist of a single byte of opcode followed by optional
 * address (transmitted MSB-first by the host) and payload fields (transmitted
 * LSB-first by the host).
 *
 * spi_device is configured to support only the 3-byte addressing mode and the
 * maximum payload size is 256 bytes. If a command with a larger payload is
 * received, spi_device overwrites the contents of the payload buffer.
 */
typedef enum spi_device_opcode {
  /**
   * READ_STATUS command.
   *
   * This command is handled by the spi_device. Upon receiving this command,
   * spi_device sends the bits of the status register.
   */
  kSpiDeviceOpcodeReadStatus = 0x05,
  /**
   * READ_JEDEC_ID command.
   *
   * This command is handled by the spi_device. Upon receiving this command,
   * spi_device sends `kSpiDeviceJedecContCodeCount` repetitions of
   * `kSpiDeviceJedecContCode`, followed by `kSpiDeviceJedecManufId` and 2 bytes
   * of device id.
   */
  kSpiDeviceOpcodeReadJedecId = 0x9f,
  /**
   * READ_SFDP command.
   *
   * This commond is handled by the spi_device. Upon receiving this
   * opcode, 3 bytes of address (all zeroes), and 8 dummy cycles;
   * spi_device sends `kSpiDeviceSfdpTable` from its buffer.
   */
  kSpiDeviceOpcodeReadSfdp = 0x5a,
  /**
   * CHIP_ERASE command.
   *
   * This command should be handled in software. Upon receiving this command,
   * all data partitions of the embedded flash should be erased.
   */
  kSpiDeviceOpcodeChipErase = 0xc7,
  /**
   * SECTOR_ERASE command.
   *
   * This command has a 3 byte address field and should be handled in software.
   * Upon receiving this command, the corresponding 4 KiB in the embedded flash
   * should be erased.
   */
  kSpiDeviceOpcodeSectorErase = 0x20,
  /**
   * PAGE_PROGRAM command.
   *
   * This command has a 3 byte address field followed by a variable length
   * payload (max 256 bytes) and should be handled in software. Upon receiving
   * this command, the corresponding area in the embedded flash should be
   * programmed with the payload.
   */
  kSpiDeviceOpcodePageProgram = 0x02,
  /**
   * RESET command.
   *
   * This command should be handled in software. Upon receiving this command,
   * the chip should be reset. Note that OpenTitan does not enforce the
   * RESET_ENABLE (0x66) and RESET (0x99) sequence.
   */
  kSpiDeviceOpcodeReset = 0x99,
  /**
   * WRITE_ENABLE command.
   *
   * This command is handled by the spi_device. Upon receiving this command,
   * spi_device sets the WEL (write enable latch) bit of the status register.
   */
  kSpiDeviceOpcodeWriteEnable = 0x06,
  /**
   * WRITE_DISABLE command.
   *
   * This command is handled by the spi_device. Upon receiving this command,
   * spi_device clears the WEL (write enable latch) bit of the status register.
   */
  kSpiDeviceOpcodeWriteDisable = 0x04,

} spi_device_opcode_t;

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
 * Initializes the spi_device in flash mode for bootstrap in ROM.
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

/**
 * A SPI flash command.
 */
typedef struct spi_device_cmd {
  /**
   * Command opcode.
   *
   * See `spi_device_opcode_t` for a list of command opcodes.
   */
  spi_device_opcode_t opcode;
  /**
   * Address.
   *
   * This field is set to `kSpiDeviceNoAddress` if the command does not have an
   * address field.
   */
  uint32_t address;
  /**
   * Payload size in bytes.
   */
  size_t payload_byte_count;
  /**
   * Payload.
   */
  alignas(uint32_t) uint8_t payload[kSpiDevicePayloadAreaNumBytes];
} spi_device_cmd_t;

/**
 * Gets the SPI flash command received from the host.
 *
 * This function returns only the commands that are handled by software and
 * blocks until the next command. The size of the payload is rounded up to the
 * next word boundary.
 *
 * @param[out] cmd SPI flash command.
 */
rom_error_t spi_device_cmd_get(spi_device_cmd_t *cmd);

/**
 * Clears the SPI flash status register.
 *
 * This function should be called after handling a SPI flash command in software
 * to clear the WIP (busy) and WEL (write enable latch) bits.
 */
void spi_device_flash_status_clear(void);

/**
 * Gets the SPI flash status register.
 */
uint32_t spi_device_flash_status_get(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_SPI_DEVICE_H_
