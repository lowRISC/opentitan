// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/spi_device.h"

#include <cstring>
#include <limits>

#include "gtest/gtest.h"
#include "sw/device/lib/base/testing/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "spi_device_regs.h"

namespace spi_device_unittest {
namespace {

class SpiDeviceTest : public mask_rom_test::MaskRomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR;
  mask_rom_test::MockAbsMmio mmio_;
};

class InitTest : public SpiDeviceTest {};

TEST_F(InitTest, Init) {
  EXPECT_ABS_WRITE32(base_ + SPI_DEVICE_CFG_REG_OFFSET,
                     {
                         {SPI_DEVICE_CFG_CPOL_BIT, 0},
                         {SPI_DEVICE_CFG_CPHA_BIT, 0},
                         {SPI_DEVICE_CFG_TX_ORDER_BIT, 0},
                         {SPI_DEVICE_CFG_RX_ORDER_BIT, 0},
                         {SPI_DEVICE_CFG_TIMER_V_OFFSET, 0x7f},
                         {SPI_DEVICE_CFG_ADDR_4B_EN_BIT, 0},
                         {SPI_DEVICE_CFG_MAILBOX_EN_BIT, 0},
                     });

  EXPECT_ABS_WRITE32(
      base_ + SPI_DEVICE_JEDEC_CC_REG_OFFSET,
      {
          {SPI_DEVICE_JEDEC_CC_CC_OFFSET, kSpiDeviceJedecContCode},
          {SPI_DEVICE_JEDEC_CC_NUM_CC_OFFSET, kSpiDeviceJedecContCodeCount},
      });
  EXPECT_ABS_WRITE32(
      base_ + SPI_DEVICE_JEDEC_ID_REG_OFFSET,
      {
          {SPI_DEVICE_DEV_ID_CHIP_REV_FIELD.index, 0},
          {SPI_DEVICE_DEV_ID_ROM_BOOTSTRAP_BIT, 1},
          {SPI_DEVICE_DEV_ID_CHIP_GEN_FIELD.index, 0},
          {SPI_DEVICE_DEV_ID_DENSITY_FIELD.index, kSpiDeviceJedecDensity},
          {SPI_DEVICE_JEDEC_ID_MF_OFFSET, kSpiDeviceJedecManufId},
      });

  EXPECT_ABS_WRITE32(
      base_ + SPI_DEVICE_CMD_INFO_3_REG_OFFSET,
      {
          {SPI_DEVICE_CMD_INFO_3_OPCODE_3_OFFSET, kSpiDeviceCmdReadJedecId},
          {SPI_DEVICE_CMD_INFO_3_VALID_3_BIT, 1},
      });

  EXPECT_ABS_WRITE32(
      base_ + SPI_DEVICE_CMD_INFO_4_REG_OFFSET,
      {
          {SPI_DEVICE_CMD_INFO_4_OPCODE_4_OFFSET, kSpiDeviceCmdReadSfdp},
          {SPI_DEVICE_CMD_INFO_4_ADDR_MODE_4_OFFSET,
           SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDR3B},
          {SPI_DEVICE_CMD_INFO_4_DUMMY_SIZE_4_OFFSET, 7},
          {SPI_DEVICE_CMD_INFO_4_DUMMY_EN_4_BIT, 1},
          {SPI_DEVICE_CMD_INFO_4_VALID_4_BIT, 1},
      });

  std::array<uint32_t, kSpiDeviceSfdpAreaNumBytes / sizeof(uint32_t)>
      sfdp_buffer;
  sfdp_buffer.fill(std::numeric_limits<uint32_t>::max());
  std::memcpy(sfdp_buffer.data(), &kSpiDeviceSfdpTable,
              sizeof(kSpiDeviceSfdpTable));
  uint32_t offset =
      base_ + SPI_DEVICE_BUFFER_REG_OFFSET + kSpiDeviceSfdpAreaOffset;
  for (size_t i = 0; i < sfdp_buffer.size(); ++i) {
    EXPECT_ABS_WRITE32(offset, sfdp_buffer[i]);
    offset += sizeof(uint32_t);
  }

  EXPECT_ABS_WRITE32(base_ + SPI_DEVICE_FLASH_STATUS_REG_OFFSET, 0);

  uint32_t control_reg = std::numeric_limits<uint32_t>::max();
  EXPECT_ABS_READ32(base_ + SPI_DEVICE_CONTROL_REG_OFFSET, control_reg);
  EXPECT_ABS_WRITE32(base_ + SPI_DEVICE_CONTROL_REG_OFFSET,
                     control_reg ^ 1 << SPI_DEVICE_CONTROL_SRAM_CLK_EN_BIT);
  EXPECT_ABS_WRITE32(base_ + SPI_DEVICE_CONTROL_REG_OFFSET,
                     {
                         {SPI_DEVICE_CONTROL_MODE_OFFSET,
                          SPI_DEVICE_CONTROL_MODE_VALUE_FLASHMODE},
                         {SPI_DEVICE_CONTROL_SRAM_CLK_EN_BIT, 0},
                     });
  EXPECT_ABS_WRITE32(base_ + SPI_DEVICE_CONTROL_REG_OFFSET,
                     {
                         {SPI_DEVICE_CONTROL_MODE_OFFSET,
                          SPI_DEVICE_CONTROL_MODE_VALUE_FLASHMODE},
                         {SPI_DEVICE_CONTROL_SRAM_CLK_EN_BIT, 1},
                     });

  spi_device_init();
}

}  // namespace
}  // namespace spi_device_unittest
