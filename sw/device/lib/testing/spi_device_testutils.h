// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_DEVICE_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_DEVICE_TESTUTILS_H_

#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_spi_device.h"

/**
 * A set of typical opcodes for named flash commands.
 */
typedef enum spi_device_flash_opcode {
  kSpiDeviceFlashOpReadJedec = 0x9f,
  kSpiDeviceFlashOpReadSfdp = 0x5a,
  kSpiDeviceFlashOpReadNormal = 0x03,
  kSpiDeviceFlashOpReadFast = 0x0b,
  kSpiDeviceFlashOpReadDual = 0x3b,
  kSpiDeviceFlashOpReadQuad = 0x6b,
  kSpiDeviceFlashOpWriteEnable = 0x06,
  kSpiDeviceFlashOpWriteDisable = 0x04,
  kSpiDeviceFlashOpReadStatus1 = 0x05,
  kSpiDeviceFlashOpReadStatus2 = 0x35,
  kSpiDeviceFlashOpReadStatus3 = 0x15,
  kSpiDeviceFlashOpWriteStatus1 = 0x01,
  kSpiDeviceFlashOpWriteStatus2 = 0x31,
  kSpiDeviceFlashOpWriteStatus3 = 0x11,
  kSpiDeviceFlashOpChipErase = 0xc7,
  kSpiDeviceFlashOpSectorErase = 0x20,
  kSpiDeviceFlashOpPageProgram = 0x02,
  kSpiDeviceFlashOpEnter4bAddr = 0xb7,
  kSpiDeviceFlashOpExit4bAddr = 0xe9,
} spi_device_flash_opcode_t;

/**
 * The index where read and write commands begin in the command slots.
 */
enum spi_device_command_slot {
  kSpiDeviceReadCommandSlotBase = 0,
  kSpiDeviceWriteCommandSlotBase = 11,
};

/**
 * Configure the SPI device in passthrough mode, allowing the following
 * commands to pass through:
 *  - ReadJedec
 *  - ReadSfdp
 *  - ReadNormal
 *  - ReadFast
 *  - ReadDual
 *  - ReadQuad
 *  - WriteEnable
 *  - WriteDisable
 *  - ReadStatus1
 *  - ReadStatus2
 *  - ReadStatus3
 *  - WriteStatus1
 *  - WriteStatus2
 *  - WriteStatus3
 *  - ChipErase
 *  - SectorErase
 *  - PageProgram
 *  - Enter4bAddr
 *  - Exit4bAddr
 *
 * @param spi_device A spi_device DIF handle.
 * @param filters A bitmap of command slots to enable passthrough filters for.
 * @param upload_write_commands Whether to upload write commands.
 */
void spi_device_testutils_configure_passthrough(
    dif_spi_device_handle_t *spi_device, uint32_t filters,
    bool upload_write_commands);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_SPI_DEVICE_TESTUTILS_H_
