// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOTSTRAP_UNITTEST_UTIL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOTSTRAP_UNITTEST_UTIL_H_

#include <stdint.h>

#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/mock_spi_device.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace bootstrap_unittest_util {

class BootstrapTest : public rom_test::RomTest {
 protected:
  /**
   * Sets an expectation for a bootstrap request check.
   *
   * @param requested Whether bootstrap is requested.
   */
  void ExpectBootstrapRequestCheck(bool requested);

  /**
   * Sets an expectation for a spi flash command.
   *
   * @param cmd Command struct to output.
   */
  void ExpectSpiCmd(spi_device_cmd_t cmd);

  /**
   * Sets an expectation for getting the SPI flash status register.
   *
   * @param wel Value of the WEL bit.
   */
  void ExpectSpiFlashStatusGet(bool wel);

  /**
   * Sets an expectation for enabling write for the data partition.
   */
  void ExpectFlashCtrlWriteEnable();

  /**
   * Sets an expectation for enabling erase for the data partition.
   */
  void ExpectFlashCtrlEraseEnable();

  /**
   * Sets an expectation for disabling all permissions for the data partition.
   */
  void ExpectFlashCtrlAllDisable();

  /**
   * Sets expectations for a chip erase.
   *
   * @param err0 Result of erase for the first bank.
   * @param err1 Result of erase for the second bank.
   */
  void ExpectFlashCtrlChipErase(rom_error_t err0, rom_error_t err1);

  /**
   * Sets expectations for a sector erase.
   *
   * @param err0 Result of erase for the first page.
   * @param err1 Result of erase for the second page.
   * @param addr Erase start address.
   */
  void ExpectFlashCtrlSectorErase(rom_error_t err0, rom_error_t err1,
                                  uint32_t addr);

  /**
   * Sets expectations for a chip erase verification.
   *
   * @param err0 Result of erase verification for the first bank.
   * @param err1 Result of erase verification for the second bank.
   */
  void ExpectFlashCtrlEraseVerify(rom_error_t err0, rom_error_t err1);

  ::rom_test::MockAbsMmio mmio_;
  ::rom_test::MockFlashCtrl flash_ctrl_;
  ::rom_test::MockOtp otp_;
  ::rom_test::MockRstmgr rstmgr_;
  ::rom_test::MockSpiDevice spi_device_;
};

/**
 * Returns a struct that represents a CHIP_ERASE command.
 *
 * @return A `spi_device_cmd_t` that represents a CHIP_ERASE command.
 */
spi_device_cmd_t ChipEraseCmd();

/**
 * Returns a struct that represents a SECTOR_ERASE command.
 *
 * @param address Address field of the command.
 * @return A `spi_device_cmd_t` that represents a SECTOR_ERASE command.
 */
spi_device_cmd_t SectorEraseCmd(uint32_t address);

/**
 * Returns a struct that represents a PAGE_PROGRAM command.
 *
 * @param address Address field of the command.
 * @param payload_byte_count Payload size in bytes.
 * @return A `spi_device_cmd_t` that represents a PAGE_PROGRAM command.
 */
spi_device_cmd_t PageProgramCmd(uint32_t address, size_t payload_byte_count);

spi_device_cmd_t ResetCmd();

}  // namespace bootstrap_unittest_util

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOTSTRAP_UNITTEST_UTIL_H_
