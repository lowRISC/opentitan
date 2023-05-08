// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/spi_device.h"

#include <array>
#include <cstring>
#include <limits>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/mock_lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "spi_device_regs.h"

namespace spi_device_unittest {
namespace {
using ::testing::NotNull;
using ::testing::SetArgPointee;

class SpiDeviceTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR;
  rom_test::MockAbsMmio mmio_;
  rom_test::MockLifecycle lifecycle_;
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
  lifecycle_hw_rev_t hw_rev{
      .silicon_creator_id = 5,  // TODO: unused in the mapping at the moment
      .product_id = 1,
      .revision_id = 3,
  };
  EXPECT_CALL(lifecycle_, HwRev(NotNull())).WillOnce(SetArgPointee<0>(hw_rev));

  EXPECT_ABS_WRITE32(
      base_ + SPI_DEVICE_JEDEC_ID_REG_OFFSET,
      {
          {SPI_DEVICE_DEV_ID_CHIP_REV_FIELD.index, hw_rev.revision_id},
          {SPI_DEVICE_DEV_ID_ROM_BOOTSTRAP_BIT, 1},
          {SPI_DEVICE_DEV_ID_CHIP_GEN_FIELD.index, hw_rev.product_id},
          {SPI_DEVICE_DEV_ID_DENSITY_FIELD.index,
           (uint32_t)bitfield_count_trailing_zeroes32(
               FLASH_CTRL_PARAM_REG_NUM_BANKS *
               FLASH_CTRL_PARAM_BYTES_PER_BANK)},
          {SPI_DEVICE_JEDEC_ID_MF_OFFSET, kSpiDeviceJedecManufId},
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

  offset = base_ + SPI_DEVICE_BUFFER_REG_OFFSET + kSpiDevicePayloadAreaOffset;
  for (size_t i = 0; i < kSpiDevicePayloadAreaNumWords; ++i) {
    EXPECT_ABS_WRITE32(offset, 0);
    offset += sizeof(uint32_t);
  }

  EXPECT_ABS_WRITE32(base_ + SPI_DEVICE_FLASH_STATUS_REG_OFFSET, 0);

  EXPECT_ABS_WRITE32(
      base_ + SPI_DEVICE_CMD_INFO_0_REG_OFFSET,
      {
          {SPI_DEVICE_CMD_INFO_0_OPCODE_0_OFFSET, kSpiDeviceOpcodeReadStatus},
          {SPI_DEVICE_CMD_INFO_0_VALID_0_BIT, 1},
      });

  EXPECT_ABS_WRITE32(
      base_ + SPI_DEVICE_CMD_INFO_3_REG_OFFSET,
      {
          {SPI_DEVICE_CMD_INFO_3_OPCODE_3_OFFSET, kSpiDeviceOpcodeReadJedecId},
          {SPI_DEVICE_CMD_INFO_3_VALID_3_BIT, 1},
      });

  EXPECT_ABS_WRITE32(
      base_ + SPI_DEVICE_CMD_INFO_4_REG_OFFSET,
      {
          {SPI_DEVICE_CMD_INFO_4_OPCODE_4_OFFSET, kSpiDeviceOpcodeReadSfdp},
          {SPI_DEVICE_CMD_INFO_4_ADDR_MODE_4_OFFSET,
           SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDR3B},
          {SPI_DEVICE_CMD_INFO_4_DUMMY_SIZE_4_OFFSET, 7},
          {SPI_DEVICE_CMD_INFO_4_DUMMY_EN_4_BIT, 1},
          {SPI_DEVICE_CMD_INFO_4_VALID_4_BIT, 1},
      });

  EXPECT_ABS_WRITE32(
      base_ + SPI_DEVICE_CMD_INFO_11_REG_OFFSET,
      {
          {SPI_DEVICE_CMD_INFO_11_OPCODE_11_OFFSET, kSpiDeviceOpcodeChipErase},
          {SPI_DEVICE_CMD_INFO_11_UPLOAD_11_BIT, 1},
          {SPI_DEVICE_CMD_INFO_11_BUSY_11_BIT, 1},
          {SPI_DEVICE_CMD_INFO_11_VALID_11_BIT, 1},
      });

  EXPECT_ABS_WRITE32(base_ + SPI_DEVICE_CMD_INFO_12_REG_OFFSET,
                     {
                         {SPI_DEVICE_CMD_INFO_12_OPCODE_12_OFFSET,
                          kSpiDeviceOpcodeSectorErase},
                         {SPI_DEVICE_CMD_INFO_12_ADDR_MODE_12_OFFSET,
                          SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDR3B},
                         {SPI_DEVICE_CMD_INFO_12_UPLOAD_12_BIT, 1},
                         {SPI_DEVICE_CMD_INFO_12_BUSY_12_BIT, 1},
                         {SPI_DEVICE_CMD_INFO_12_VALID_12_BIT, 1},
                     });

  EXPECT_ABS_WRITE32(base_ + SPI_DEVICE_CMD_INFO_13_REG_OFFSET,
                     {
                         {SPI_DEVICE_CMD_INFO_13_OPCODE_13_OFFSET,
                          kSpiDeviceOpcodePageProgram},
                         {SPI_DEVICE_CMD_INFO_13_ADDR_MODE_13_OFFSET,
                          SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDR3B},
                         {SPI_DEVICE_CMD_INFO_13_UPLOAD_13_BIT, 1},
                         {SPI_DEVICE_CMD_INFO_13_BUSY_13_BIT, 1},
                         {SPI_DEVICE_CMD_INFO_13_VALID_13_BIT, 1},
                     });

  EXPECT_ABS_WRITE32(
      base_ + SPI_DEVICE_CMD_INFO_14_REG_OFFSET,
      {
          {SPI_DEVICE_CMD_INFO_14_OPCODE_14_OFFSET, kSpiDeviceOpcodeReset},
          {SPI_DEVICE_CMD_INFO_14_UPLOAD_14_BIT, 1},
          {SPI_DEVICE_CMD_INFO_14_BUSY_14_BIT, 1},
          {SPI_DEVICE_CMD_INFO_14_VALID_14_BIT, 1},
      });

  EXPECT_ABS_WRITE32(
      base_ + SPI_DEVICE_CMD_INFO_WREN_REG_OFFSET,
      {
          {SPI_DEVICE_CMD_INFO_WREN_OPCODE_OFFSET, kSpiDeviceOpcodeWriteEnable},
          {SPI_DEVICE_CMD_INFO_WREN_VALID_BIT, 1},
      });

  EXPECT_ABS_WRITE32(base_ + SPI_DEVICE_CMD_INFO_WRDI_REG_OFFSET,
                     {
                         {SPI_DEVICE_CMD_INFO_WRDI_OPCODE_OFFSET,
                          kSpiDeviceOpcodeWriteDisable},
                         {SPI_DEVICE_CMD_INFO_WRDI_VALID_BIT, 1},
                     });

  spi_device_init();
}

TEST_F(SpiDeviceTest, FlashStatusClear) {
  EXPECT_ABS_WRITE32(base_ + SPI_DEVICE_FLASH_STATUS_REG_OFFSET, 0);

  spi_device_flash_status_clear();
}

TEST_F(SpiDeviceTest, FlashStatusGet) {
  EXPECT_ABS_READ32(base_ + SPI_DEVICE_FLASH_STATUS_REG_OFFSET, 0xa5);

  EXPECT_EQ(0xa5, spi_device_flash_status_get());
}

struct CmdGetTestCase {
  spi_device_opcode_t opcode;
  uint32_t address;
  std::vector<uint8_t> payload;
};

class CmdGetTest : public SpiDeviceTest,
                   public testing::WithParamInterface<CmdGetTestCase> {};

TEST_F(CmdGetTest, PayloadOverflow) {
  EXPECT_ABS_READ32(base_ + SPI_DEVICE_INTR_STATE_REG_OFFSET, 0);
  EXPECT_ABS_READ32(base_ + SPI_DEVICE_INTR_STATE_REG_OFFSET,
                    {
                        {SPI_DEVICE_INTR_STATE_UPLOAD_CMDFIFO_NOT_EMPTY_BIT, 1},
                        {SPI_DEVICE_INTR_STATE_UPLOAD_PAYLOAD_OVERFLOW_BIT, 1},
                    });
  EXPECT_ABS_WRITE32(base_ + SPI_DEVICE_INTR_STATE_REG_OFFSET,
                     std::numeric_limits<uint32_t>::max());

  spi_device_cmd_t cmd;
  EXPECT_EQ(spi_device_cmd_get(&cmd), kErrorSpiDevicePayloadOverflow);
}

TEST_P(CmdGetTest, CmdGet) {
  bool has_address = GetParam().address != kSpiDeviceNoAddress;

  EXPECT_ABS_READ32(base_ + SPI_DEVICE_INTR_STATE_REG_OFFSET, 0);
  EXPECT_ABS_READ32(base_ + SPI_DEVICE_INTR_STATE_REG_OFFSET,
                    {{SPI_DEVICE_INTR_STATE_UPLOAD_CMDFIFO_NOT_EMPTY_BIT, 1}});
  EXPECT_ABS_WRITE32(base_ + SPI_DEVICE_INTR_STATE_REG_OFFSET,
                     std::numeric_limits<uint32_t>::max());

  EXPECT_ABS_READ32(base_ + SPI_DEVICE_UPLOAD_CMDFIFO_REG_OFFSET,
                    GetParam().opcode);

  EXPECT_ABS_READ32(
      base_ + SPI_DEVICE_UPLOAD_STATUS_REG_OFFSET,
      {{SPI_DEVICE_UPLOAD_STATUS_ADDRFIFO_NOTEMPTY_BIT, has_address}});
  if (has_address) {
    EXPECT_ABS_READ32(base_ + SPI_DEVICE_UPLOAD_ADDRFIFO_REG_OFFSET,
                      GetParam().address);
  }

  std::vector<uint32_t> payload_area(kSpiDevicePayloadAreaNumWords,
                                     std::numeric_limits<uint32_t>::max());
  std::memcpy(payload_area.data(), GetParam().payload.data(),
              GetParam().payload.size());
  EXPECT_ABS_READ32(base_ + SPI_DEVICE_UPLOAD_STATUS2_REG_OFFSET,
                    {{SPI_DEVICE_UPLOAD_STATUS2_PAYLOAD_DEPTH_OFFSET,
                      GetParam().payload.size()}});
  uint32_t offset =
      base_ + SPI_DEVICE_BUFFER_REG_OFFSET + kSpiDevicePayloadAreaOffset;
  for (size_t i = 0; i < GetParam().payload.size(); i += sizeof(uint32_t)) {
    EXPECT_ABS_READ32(offset + i, payload_area[i / sizeof(uint32_t)]);
  }

  spi_device_cmd_t cmd;
  EXPECT_EQ(spi_device_cmd_get(&cmd), kErrorOk);
  EXPECT_EQ(cmd.opcode, GetParam().opcode);
  EXPECT_EQ(cmd.address, GetParam().address);
  EXPECT_EQ(cmd.payload_byte_count, GetParam().payload.size());
  std::vector<uint8_t> payload(cmd.payload, std::end(cmd.payload));
  payload.resize(cmd.payload_byte_count);
  EXPECT_THAT(payload, GetParam().payload);
}

INSTANTIATE_TEST_SUITE_P(
    CmdGetTestCases, CmdGetTest,
    testing::Values(
        CmdGetTestCase{
            .opcode = kSpiDeviceOpcodeChipErase,
            .address = kSpiDeviceNoAddress,
            .payload = {},
        },
        CmdGetTestCase{
            .opcode = kSpiDeviceOpcodeSectorErase,
            .address = 0x00,
            .payload = {},
        },
        CmdGetTestCase{
            .opcode = kSpiDeviceOpcodePageProgram,
            .address = 0x0a0b0c,
            .payload = {0x01, 0x02, 0x03, 0x04},
        },
        CmdGetTestCase{
            .opcode = kSpiDeviceOpcodePageProgram,
            .address = 0x0a0b0c,
            .payload = {0x01, 0x02, 0x03, 0x04, 0x05},
        },
        CmdGetTestCase{
            .opcode = kSpiDeviceOpcodePageProgram,
            .address = 0x0a0b0c,
            .payload = {0x01, 0x02, 0x03, 0x04, 0x05, 0x06},
        },
        CmdGetTestCase{
            .opcode = kSpiDeviceOpcodePageProgram,
            .address = 0x0a0b0c,
            .payload = {0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07},
        },
        CmdGetTestCase{
            .opcode = kSpiDeviceOpcodePageProgram,
            .address = 0x0a0b0c,
            .payload = {0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08},
        }));

}  // namespace
}  // namespace spi_device_unittest
