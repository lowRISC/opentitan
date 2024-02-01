// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_spi_device.h"

#include <limits>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "spi_device_regs.h"  // Generated.

namespace dif_spi_device_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;

class SpiTest : public testing::Test, public MmioTest {
 public:
  static constexpr uint16_t kFifoLen = 0x800;

 protected:
  dif_spi_device_handle_t spi_ = {
      .dev = {.base_addr = dev().region()},
  };
};

static constexpr dif_spi_device_config_t kDefaultConfig = {
    .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
    .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
    .device_mode = kDifSpiDeviceModeDisabled,
};

class ConfigTest : public SpiTest {};

TEST_F(ConfigTest, BasicInit) {
  EXPECT_WRITE32(SPI_DEVICE_CFG_REG_OFFSET,
                 {
                     {SPI_DEVICE_CFG_TX_ORDER_BIT, 0},
                     {SPI_DEVICE_CFG_RX_ORDER_BIT, 0},
                 });
  EXPECT_READ32(SPI_DEVICE_CONTROL_REG_OFFSET,
                {
                    {SPI_DEVICE_CONTROL_MODE_OFFSET, 3},
                });
  EXPECT_WRITE32(SPI_DEVICE_CONTROL_REG_OFFSET,
                 {
                     {SPI_DEVICE_CONTROL_MODE_OFFSET, 0},
                 });
  EXPECT_DIF_OK(dif_spi_device_configure(&spi_, kDefaultConfig));
}

TEST_F(ConfigTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_spi_device_configure(nullptr, kDefaultConfig));
  EXPECT_DIF_BADARG(
      dif_spi_device_set_passthrough_mode(nullptr, kDifToggleEnabled));
}

class FlashTest : public SpiTest {
  void SetUp() {
    const dif_spi_device_config_t config = {
        .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
        .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
        .device_mode = kDifSpiDeviceModePassthrough,
    };
    EXPECT_DIF_OK(dif_spi_device_init_handle(dev().region(), &spi_));
    EXPECT_WRITE32(SPI_DEVICE_CFG_REG_OFFSET,
                   {
                       {SPI_DEVICE_CFG_TX_ORDER_BIT, 0},
                       {SPI_DEVICE_CFG_RX_ORDER_BIT, 0},
                   });
    EXPECT_READ32(SPI_DEVICE_CONTROL_REG_OFFSET,
                  {
                      {SPI_DEVICE_CONTROL_MODE_OFFSET, 0},
                  });
    EXPECT_WRITE32(SPI_DEVICE_CONTROL_REG_OFFSET,
                   {
                       {SPI_DEVICE_CONTROL_MODE_OFFSET,
                        SPI_DEVICE_CONTROL_MODE_VALUE_PASSTHROUGH},
                   });
    EXPECT_DIF_OK(dif_spi_device_configure(&spi_, config));
  };
};

TEST_F(FlashTest, NullArgs) {
  dif_toggle_t toggle_arg;
  uint32_t uint32_arg;
  uint16_t uint16_arg;
  uint8_t uint8_arg;
  dif_spi_device_flash_id_t id_arg;
  dif_spi_device_flash_command_t command_arg;
  dif_spi_device_passthrough_intercept_config_t intercept_config;
  EXPECT_DIF_BADARG(dif_spi_device_init_handle(dev().region(), nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_enable_mailbox(nullptr, /*address=*/0x1000));
  EXPECT_DIF_BADARG(dif_spi_device_disable_mailbox(nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_get_mailbox_configuration(
      nullptr, &toggle_arg, &uint32_arg));
  EXPECT_DIF_BADARG(
      dif_spi_device_get_mailbox_configuration(&spi_, nullptr, &uint32_arg));
  EXPECT_DIF_BADARG(
      dif_spi_device_get_mailbox_configuration(&spi_, &toggle_arg, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_set_4b_address_mode(nullptr, kDifToggleEnabled));
  EXPECT_DIF_BADARG(dif_spi_device_get_4b_address_mode(nullptr, &toggle_arg));
  EXPECT_DIF_BADARG(dif_spi_device_get_4b_address_mode(&spi_, nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_clear_flash_status_request(nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_get_flash_id(nullptr, &id_arg));
  EXPECT_DIF_BADARG(dif_spi_device_get_flash_id(&spi_, nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_set_flash_id(nullptr, id_arg));
  EXPECT_DIF_BADARG(dif_spi_device_set_passthrough_intercept_config(
      nullptr, intercept_config));
  EXPECT_DIF_BADARG(dif_spi_device_get_last_read_address(nullptr, &uint32_arg));
  EXPECT_DIF_BADARG(dif_spi_device_get_last_read_address(&spi_, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_set_eflash_read_threshold(nullptr, /*address=*/0));
  EXPECT_DIF_BADARG(dif_spi_device_reset_eflash_buffer(nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_get_flash_command_slot(
      nullptr, /*slot=*/0, &toggle_arg, &command_arg));
  EXPECT_DIF_BADARG(dif_spi_device_get_flash_command_slot(
      &spi_, /*slot=*/0, nullptr, &command_arg));
  EXPECT_DIF_BADARG(dif_spi_device_get_flash_command_slot(
      &spi_, /*slot=*/0, &toggle_arg, nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_set_flash_command_slot(
      nullptr, /*slot=*/0, kDifToggleEnabled, command_arg));
  EXPECT_DIF_BADARG(dif_spi_device_configure_flash_en4b_command(
      nullptr, kDifToggleEnabled, /*opcode=*/0));
  EXPECT_DIF_BADARG(dif_spi_device_configure_flash_ex4b_command(
      nullptr, kDifToggleEnabled, /*opcode=*/0));
  EXPECT_DIF_BADARG(dif_spi_device_configure_flash_wren_command(
      nullptr, kDifToggleEnabled, /*opcode=*/0));
  EXPECT_DIF_BADARG(dif_spi_device_configure_flash_wrdi_command(
      nullptr, kDifToggleEnabled, /*opcode=*/0));
  EXPECT_DIF_BADARG(dif_spi_device_set_flash_address_swap(nullptr, /*mask=*/0,
                                                          /*replacement=*/0));
  EXPECT_DIF_BADARG(dif_spi_device_set_flash_payload_swap(nullptr, /*mask=*/0,
                                                          /*replacement=*/0));
  EXPECT_DIF_BADARG(
      dif_spi_device_get_flash_command_fifo_occupancy(nullptr, &uint8_arg));
  EXPECT_DIF_BADARG(
      dif_spi_device_get_flash_command_fifo_occupancy(&spi_, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_get_flash_address_fifo_occupancy(nullptr, &uint8_arg));
  EXPECT_DIF_BADARG(
      dif_spi_device_get_flash_address_fifo_occupancy(&spi_, nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_get_flash_payload_fifo_occupancy(
      nullptr, &uint16_arg, &uint32_arg));
  EXPECT_DIF_BADARG(dif_spi_device_get_flash_payload_fifo_occupancy(
      &spi_, nullptr, &uint32_arg));
  EXPECT_DIF_BADARG(dif_spi_device_get_flash_payload_fifo_occupancy(
      &spi_, &uint16_arg, nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_pop_flash_command_fifo(nullptr, &uint8_arg));
  EXPECT_DIF_BADARG(dif_spi_device_pop_flash_command_fifo(&spi_, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_pop_flash_address_fifo(nullptr, &uint32_arg));
  EXPECT_DIF_BADARG(dif_spi_device_pop_flash_address_fifo(&spi_, nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_read_flash_payload_buffer(
      nullptr, /*offset=*/0, /*length=*/1, &uint8_arg));
  EXPECT_DIF_BADARG(dif_spi_device_read_flash_payload_buffer(
      &spi_, /*offset=*/0, /*length=*/1, nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_write_flash_buffer(
      nullptr, kDifSpiDeviceFlashBufferTypeSfdp, /*offset=*/0, /*length=*/1,
      &uint8_arg));
  EXPECT_DIF_BADARG(
      dif_spi_device_write_flash_buffer(&spi_, kDifSpiDeviceFlashBufferTypeSfdp,
                                        /*offset=*/0, /*length=*/1, nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_get_passthrough_command_filter(
      nullptr, /*command=*/0, &toggle_arg));
  EXPECT_DIF_BADARG(dif_spi_device_get_passthrough_command_filter(
      &spi_, /*command=*/0, nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_set_passthrough_command_filter(
      nullptr, /*command=*/0, kDifToggleEnabled));
  EXPECT_DIF_BADARG(dif_spi_device_set_all_passthrough_command_filters(
      nullptr, kDifToggleEnabled));
  EXPECT_DIF_BADARG(dif_spi_device_clear_flash_busy_bit(nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_set_flash_status_registers(nullptr, /*value=*/0));
  EXPECT_DIF_BADARG(
      dif_spi_device_get_flash_status_registers(nullptr, &uint32_arg));
  EXPECT_DIF_BADARG(dif_spi_device_get_flash_status_registers(&spi_, nullptr));
}

TEST_F(FlashTest, CsbGpio) {
  bool csb;
  EXPECT_READ32(SPI_DEVICE_STATUS_REG_OFFSET,
                {
                    {SPI_DEVICE_STATUS_CSB_BIT, 1},
                });
  EXPECT_DIF_OK(dif_spi_device_get_csb_status(&spi_, &csb));
  EXPECT_TRUE(csb);

  EXPECT_READ32(SPI_DEVICE_STATUS_REG_OFFSET,
                {
                    {SPI_DEVICE_STATUS_CSB_BIT, 0},
                });
  EXPECT_DIF_OK(dif_spi_device_get_csb_status(&spi_, &csb));
  EXPECT_FALSE(csb);
}

TEST_F(FlashTest, PassthroughToggle) {
  EXPECT_READ32(SPI_DEVICE_CONTROL_REG_OFFSET,
                {
                    {SPI_DEVICE_CONTROL_MODE_OFFSET,
                     SPI_DEVICE_CONTROL_MODE_VALUE_PASSTHROUGH},
                });
  EXPECT_WRITE32(SPI_DEVICE_CONTROL_REG_OFFSET,
                 {
                     {SPI_DEVICE_CONTROL_MODE_OFFSET,
                      SPI_DEVICE_CONTROL_MODE_VALUE_FLASHMODE},
                 });
  EXPECT_DIF_OK(dif_spi_device_set_passthrough_mode(&spi_, kDifToggleDisabled));
  EXPECT_READ32(SPI_DEVICE_CONTROL_REG_OFFSET,
                {
                    {SPI_DEVICE_CONTROL_MODE_OFFSET,
                     SPI_DEVICE_CONTROL_MODE_VALUE_FLASHMODE},
                });
  EXPECT_WRITE32(SPI_DEVICE_CONTROL_REG_OFFSET,
                 {
                     {SPI_DEVICE_CONTROL_MODE_OFFSET,
                      SPI_DEVICE_CONTROL_MODE_VALUE_PASSTHROUGH},
                 });
  EXPECT_DIF_OK(dif_spi_device_set_passthrough_mode(&spi_, kDifToggleEnabled));
}

TEST_F(FlashTest, MailboxConfigTest) {
  dif_toggle_t toggle;
  uint32_t address = 0x3f0000;
  EXPECT_WRITE32(SPI_DEVICE_MAILBOX_ADDR_REG_OFFSET, address);
  EXPECT_READ32(SPI_DEVICE_CFG_REG_OFFSET, {
                                               {SPI_DEVICE_CFG_TX_ORDER_BIT, 1},
                                               {SPI_DEVICE_CFG_RX_ORDER_BIT, 1},
                                           });
  EXPECT_WRITE32(SPI_DEVICE_CFG_REG_OFFSET,
                 {
                     {SPI_DEVICE_CFG_MAILBOX_EN_BIT, 1},
                     {SPI_DEVICE_CFG_TX_ORDER_BIT, 1},
                     {SPI_DEVICE_CFG_RX_ORDER_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_spi_device_enable_mailbox(&spi_, address));
  EXPECT_READ32(SPI_DEVICE_CFG_REG_OFFSET,
                {
                    {SPI_DEVICE_CFG_MAILBOX_EN_BIT, 1},
                    {SPI_DEVICE_CFG_TX_ORDER_BIT, 0},
                    {SPI_DEVICE_CFG_RX_ORDER_BIT, 1},
                });
  EXPECT_WRITE32(SPI_DEVICE_CFG_REG_OFFSET,
                 {
                     {SPI_DEVICE_CFG_MAILBOX_EN_BIT, 0},
                     {SPI_DEVICE_CFG_TX_ORDER_BIT, 0},
                     {SPI_DEVICE_CFG_RX_ORDER_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_spi_device_disable_mailbox(&spi_));
  EXPECT_READ32(SPI_DEVICE_CFG_REG_OFFSET,
                {
                    {SPI_DEVICE_CFG_MAILBOX_EN_BIT, 1},
                    {SPI_DEVICE_CFG_TX_ORDER_BIT, 1},
                });
  EXPECT_READ32(SPI_DEVICE_MAILBOX_ADDR_REG_OFFSET, 0x100000);
  EXPECT_DIF_OK(
      dif_spi_device_get_mailbox_configuration(&spi_, &toggle, &address));
  EXPECT_EQ(toggle, kDifToggleEnabled);
  EXPECT_EQ(address, 0x100000);
  EXPECT_READ32(SPI_DEVICE_CFG_REG_OFFSET,
                {
                    {SPI_DEVICE_CFG_MAILBOX_EN_BIT, 0},
                });
  EXPECT_READ32(SPI_DEVICE_MAILBOX_ADDR_REG_OFFSET, 0x100000);
  EXPECT_DIF_OK(
      dif_spi_device_get_mailbox_configuration(&spi_, &toggle, &address));
  EXPECT_EQ(toggle, kDifToggleDisabled);
}

TEST_F(FlashTest, Addr4bConfig) {
  dif_toggle_t toggle;
  EXPECT_READ32(SPI_DEVICE_ADDR_MODE_REG_OFFSET,
                {
                    {SPI_DEVICE_ADDR_MODE_PENDING_BIT, 1},
                });
  EXPECT_DIF_OK(dif_spi_device_get_4b_address_mode(&spi_, &toggle));
  EXPECT_EQ(toggle, kDifToggleDisabled);

  EXPECT_READ32(SPI_DEVICE_ADDR_MODE_REG_OFFSET,
                {
                    {SPI_DEVICE_ADDR_MODE_PENDING_BIT, 1},
                    {SPI_DEVICE_ADDR_MODE_ADDR_4B_EN_BIT, 1},
                });
  EXPECT_DIF_OK(dif_spi_device_get_4b_address_mode(&spi_, &toggle));
  EXPECT_EQ(toggle, kDifToggleEnabled);

  EXPECT_WRITE32(SPI_DEVICE_ADDR_MODE_REG_OFFSET,
                 {
                     {SPI_DEVICE_ADDR_MODE_ADDR_4B_EN_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_spi_device_set_4b_address_mode(&spi_, kDifToggleEnabled));
  EXPECT_WRITE32(SPI_DEVICE_ADDR_MODE_REG_OFFSET,
                 {
                     {SPI_DEVICE_ADDR_MODE_ADDR_4B_EN_BIT, 0},
                 });
  EXPECT_DIF_OK(dif_spi_device_set_4b_address_mode(&spi_, kDifToggleDisabled));
}

TEST_F(FlashTest, DeviceId) {
  dif_spi_device_flash_id_t id;
  EXPECT_READ32(SPI_DEVICE_JEDEC_CC_REG_OFFSET,
                {
                    {SPI_DEVICE_JEDEC_CC_NUM_CC_OFFSET, 10},
                    {SPI_DEVICE_JEDEC_CC_CC_OFFSET, 0x5a},
                });
  EXPECT_READ32(SPI_DEVICE_JEDEC_ID_REG_OFFSET,
                {
                    {SPI_DEVICE_JEDEC_ID_MF_OFFSET, 0xca},
                    {SPI_DEVICE_JEDEC_ID_ID_OFFSET, 0x1234},
                });
  EXPECT_DIF_OK(dif_spi_device_get_flash_id(&spi_, &id));
  EXPECT_EQ(id.num_continuation_code, 10);
  EXPECT_EQ(id.continuation_code, 0x5a);
  EXPECT_EQ(id.manufacturer_id, 0xca);
  EXPECT_EQ(id.device_id, 0x1234);

  id = (dif_spi_device_flash_id_t){
      .device_id = 0x2202,
      .manufacturer_id = 0xd7,
      .continuation_code = 0x7f,
      .num_continuation_code = 7,
  };
  EXPECT_WRITE32(SPI_DEVICE_JEDEC_CC_REG_OFFSET,
                 {
                     {SPI_DEVICE_JEDEC_CC_NUM_CC_OFFSET, 7},
                     {SPI_DEVICE_JEDEC_CC_CC_OFFSET, 0x7f},
                 });
  EXPECT_WRITE32(SPI_DEVICE_JEDEC_ID_REG_OFFSET,
                 {
                     {SPI_DEVICE_JEDEC_ID_MF_OFFSET, 0xd7},
                     {SPI_DEVICE_JEDEC_ID_ID_OFFSET, 0x2202},
                 });
  EXPECT_DIF_OK(dif_spi_device_set_flash_id(&spi_, id));
}

TEST_F(FlashTest, InterceptConfig) {
  dif_spi_device_passthrough_intercept_config_t config = {
      .status = false,
      .jedec_id = true,
      .sfdp = false,
      .mailbox = true,
  };
  EXPECT_WRITE32(SPI_DEVICE_INTERCEPT_EN_REG_OFFSET,
                 {
                     {SPI_DEVICE_INTERCEPT_EN_STATUS_BIT, 0},
                     {SPI_DEVICE_INTERCEPT_EN_JEDEC_BIT, 1},
                     {SPI_DEVICE_INTERCEPT_EN_SFDP_BIT, 0},
                     {SPI_DEVICE_INTERCEPT_EN_MBX_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_spi_device_set_passthrough_intercept_config(&spi_, config));

  config = (dif_spi_device_passthrough_intercept_config_t){
      .status = true,
      .jedec_id = false,
      .sfdp = true,
      .mailbox = false,
  };
  EXPECT_WRITE32(SPI_DEVICE_INTERCEPT_EN_REG_OFFSET,
                 {
                     {SPI_DEVICE_INTERCEPT_EN_STATUS_BIT, 1},
                     {SPI_DEVICE_INTERCEPT_EN_JEDEC_BIT, 0},
                     {SPI_DEVICE_INTERCEPT_EN_SFDP_BIT, 1},
                     {SPI_DEVICE_INTERCEPT_EN_MBX_BIT, 0},
                 });
  EXPECT_DIF_OK(dif_spi_device_set_passthrough_intercept_config(&spi_, config));
}

TEST_F(FlashTest, FlashWatermark) {
  uint32_t address;
  EXPECT_READ32(SPI_DEVICE_LAST_READ_ADDR_REG_OFFSET, 0x1000);
  EXPECT_DIF_OK(dif_spi_device_get_last_read_address(&spi_, &address));
  EXPECT_EQ(address, 0x1000);

  EXPECT_DIF_BADARG(dif_spi_device_set_eflash_read_threshold(&spi_, 0x800));

  EXPECT_WRITE32(SPI_DEVICE_READ_THRESHOLD_REG_OFFSET, 0x26a);
  EXPECT_DIF_OK(dif_spi_device_set_eflash_read_threshold(&spi_, 0x26a));

  EXPECT_WRITE32(SPI_DEVICE_CONTROL_REG_OFFSET,
                 {
                     {SPI_DEVICE_CONTROL_MODE_OFFSET,
                      SPI_DEVICE_CONTROL_MODE_VALUE_PASSTHROUGH},
                     {SPI_DEVICE_CONTROL_FLASH_READ_BUFFER_CLR_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_spi_device_reset_eflash_buffer(&spi_));
}

TEST_F(FlashTest, CommandInfo) {
  dif_spi_device_flash_command_t command_info;
  dif_toggle_t toggle;
  EXPECT_READ32(SPI_DEVICE_CMD_INFO_0_REG_OFFSET,
                {
                    {SPI_DEVICE_CMD_INFO_0_OPCODE_0_OFFSET, 0x6b},
                    {SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_OFFSET,
                     SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDRCFG},
                    {SPI_DEVICE_CMD_INFO_0_DUMMY_EN_0_BIT, 1},
                    {SPI_DEVICE_CMD_INFO_0_DUMMY_SIZE_0_OFFSET, 7},
                    {SPI_DEVICE_CMD_INFO_0_PAYLOAD_EN_0_OFFSET, 0xf},
                    {SPI_DEVICE_CMD_INFO_0_PAYLOAD_DIR_0_BIT, 1},
                    {SPI_DEVICE_CMD_INFO_0_ADDR_SWAP_EN_0_BIT, 0},
                    {SPI_DEVICE_CMD_INFO_0_PAYLOAD_SWAP_EN_0_BIT, 0},
                    {SPI_DEVICE_CMD_INFO_0_UPLOAD_0_BIT, 0},
                    {SPI_DEVICE_CMD_INFO_0_BUSY_0_BIT, 0},
                    {SPI_DEVICE_CMD_INFO_0_VALID_0_BIT, 0},
                });
  EXPECT_DIF_OK(dif_spi_device_get_flash_command_slot(&spi_, /*slot=*/0,
                                                      &toggle, &command_info));
  EXPECT_EQ(toggle, kDifToggleDisabled);

  EXPECT_READ32(SPI_DEVICE_CMD_INFO_1_REG_OFFSET,
                {
                    {SPI_DEVICE_CMD_INFO_1_OPCODE_1_OFFSET, 0x6b},
                    {SPI_DEVICE_CMD_INFO_1_ADDR_MODE_1_OFFSET,
                     SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDRCFG},
                    {SPI_DEVICE_CMD_INFO_1_DUMMY_EN_1_BIT, 1},
                    {SPI_DEVICE_CMD_INFO_1_DUMMY_SIZE_1_OFFSET, 7},
                    {SPI_DEVICE_CMD_INFO_1_PAYLOAD_EN_1_OFFSET, 0xf},
                    {SPI_DEVICE_CMD_INFO_1_PAYLOAD_DIR_1_BIT, 1},
                    {SPI_DEVICE_CMD_INFO_1_ADDR_SWAP_EN_1_BIT, 0},
                    {SPI_DEVICE_CMD_INFO_1_PAYLOAD_SWAP_EN_1_BIT, 0},
                    {SPI_DEVICE_CMD_INFO_1_UPLOAD_1_BIT, 0},
                    {SPI_DEVICE_CMD_INFO_1_BUSY_1_BIT, 0},
                    {SPI_DEVICE_CMD_INFO_1_VALID_1_BIT, 1},
                });
  EXPECT_DIF_OK(dif_spi_device_get_flash_command_slot(&spi_, /*slot=*/1,
                                                      &toggle, &command_info));
  EXPECT_EQ(toggle, kDifToggleEnabled);
  EXPECT_EQ(command_info.opcode, 0x6b);
  EXPECT_EQ(command_info.address_type, kDifSpiDeviceFlashAddrCfg);
  EXPECT_EQ(command_info.dummy_cycles, 8);
  EXPECT_EQ(command_info.payload_io_type, kDifSpiDevicePayloadIoQuad);
  EXPECT_FALSE(command_info.passthrough_swap_address);
  EXPECT_TRUE(command_info.payload_dir_to_host);
  EXPECT_FALSE(command_info.payload_swap_enable);
  EXPECT_FALSE(command_info.upload);
  EXPECT_FALSE(command_info.set_busy_status);

  EXPECT_READ32(SPI_DEVICE_CMD_INFO_1_REG_OFFSET,
                {
                    {SPI_DEVICE_CMD_INFO_1_OPCODE_1_OFFSET, 0x12},
                    {SPI_DEVICE_CMD_INFO_1_ADDR_MODE_1_OFFSET,
                     SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDR4B},
                    {SPI_DEVICE_CMD_INFO_1_DUMMY_EN_1_BIT, 0},
                    {SPI_DEVICE_CMD_INFO_1_DUMMY_SIZE_1_OFFSET, 7},
                    {SPI_DEVICE_CMD_INFO_1_PAYLOAD_EN_1_OFFSET, 0x1},
                    {SPI_DEVICE_CMD_INFO_1_PAYLOAD_DIR_1_BIT, 0},
                    {SPI_DEVICE_CMD_INFO_1_ADDR_SWAP_EN_1_BIT, 1},
                    {SPI_DEVICE_CMD_INFO_1_PAYLOAD_SWAP_EN_1_BIT, 1},
                    {SPI_DEVICE_CMD_INFO_1_UPLOAD_1_BIT, 1},
                    {SPI_DEVICE_CMD_INFO_1_BUSY_1_BIT, 1},
                    {SPI_DEVICE_CMD_INFO_1_VALID_1_BIT, 1},
                });
  EXPECT_DIF_OK(dif_spi_device_get_flash_command_slot(&spi_, /*slot=*/1,
                                                      &toggle, &command_info));
  EXPECT_EQ(toggle, kDifToggleEnabled);
  EXPECT_EQ(command_info.opcode, 0x12);
  EXPECT_EQ(command_info.address_type, kDifSpiDeviceFlashAddr4Byte);
  EXPECT_EQ(command_info.dummy_cycles, 0);
  EXPECT_EQ(command_info.payload_io_type, kDifSpiDevicePayloadIoSingle);
  EXPECT_TRUE(command_info.passthrough_swap_address);
  EXPECT_FALSE(command_info.payload_dir_to_host);
  EXPECT_TRUE(command_info.payload_swap_enable);
  EXPECT_TRUE(command_info.upload);
  EXPECT_TRUE(command_info.set_busy_status);

  command_info = (dif_spi_device_flash_command_t){
      .opcode = 0x06,
      .address_type = kDifSpiDeviceFlashAddrDisabled,
      .dummy_cycles = 0,
      .payload_io_type = kDifSpiDevicePayloadIoSingle,
      .passthrough_swap_address = false,
      .payload_dir_to_host = false,
      .payload_swap_enable = true,
      .upload = true,
      .set_busy_status = true,
  };
  EXPECT_WRITE32(SPI_DEVICE_CMD_INFO_1_REG_OFFSET,
                 {
                     {SPI_DEVICE_CMD_INFO_1_OPCODE_1_OFFSET, 0x06},
                     {SPI_DEVICE_CMD_INFO_1_ADDR_MODE_1_OFFSET,
                      SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDRDISABLED},
                     {SPI_DEVICE_CMD_INFO_1_DUMMY_EN_1_BIT, 0},
                     {SPI_DEVICE_CMD_INFO_1_DUMMY_SIZE_1_OFFSET, 0},
                     {SPI_DEVICE_CMD_INFO_1_PAYLOAD_EN_1_OFFSET, 0x1},
                     {SPI_DEVICE_CMD_INFO_1_PAYLOAD_DIR_1_BIT, 0},
                     {SPI_DEVICE_CMD_INFO_1_ADDR_SWAP_EN_1_BIT, 0},
                     {SPI_DEVICE_CMD_INFO_1_PAYLOAD_SWAP_EN_1_BIT, 1},
                     {SPI_DEVICE_CMD_INFO_1_UPLOAD_1_BIT, 1},
                     {SPI_DEVICE_CMD_INFO_1_BUSY_1_BIT, 1},
                     {SPI_DEVICE_CMD_INFO_1_VALID_1_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_spi_device_set_flash_command_slot(
      &spi_, /*slot=*/1, kDifToggleEnabled, command_info));
  command_info = (dif_spi_device_flash_command_t){
      .opcode = 0x5a,
      .address_type = kDifSpiDeviceFlashAddr3Byte,
      .dummy_cycles = 8,
      .payload_io_type = kDifSpiDevicePayloadIoSingle,
      .passthrough_swap_address = false,
      .payload_dir_to_host = true,
      .payload_swap_enable = false,
      .upload = false,
      .set_busy_status = false,
  };
  EXPECT_WRITE32(SPI_DEVICE_CMD_INFO_1_REG_OFFSET,
                 {
                     {SPI_DEVICE_CMD_INFO_1_OPCODE_1_OFFSET, 0x5a},
                     {SPI_DEVICE_CMD_INFO_1_ADDR_MODE_1_OFFSET,
                      SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDR3B},
                     {SPI_DEVICE_CMD_INFO_1_DUMMY_EN_1_BIT, 1},
                     {SPI_DEVICE_CMD_INFO_1_DUMMY_SIZE_1_OFFSET, 7},
                     {SPI_DEVICE_CMD_INFO_1_PAYLOAD_EN_1_OFFSET, 0x2},
                     {SPI_DEVICE_CMD_INFO_1_PAYLOAD_DIR_1_BIT, 1},
                     {SPI_DEVICE_CMD_INFO_1_ADDR_SWAP_EN_1_BIT, 0},
                     {SPI_DEVICE_CMD_INFO_1_PAYLOAD_SWAP_EN_1_BIT, 0},
                     {SPI_DEVICE_CMD_INFO_1_UPLOAD_1_BIT, 0},
                     {SPI_DEVICE_CMD_INFO_1_BUSY_1_BIT, 0},
                     {SPI_DEVICE_CMD_INFO_1_VALID_1_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_spi_device_set_flash_command_slot(
      &spi_, /*slot=*/1, kDifToggleEnabled, command_info));
}

TEST_F(FlashTest, HardwareCommandInfo) {
  EXPECT_WRITE32(SPI_DEVICE_CMD_INFO_EN4B_REG_OFFSET,
                 {
                     {SPI_DEVICE_CMD_INFO_EN4B_OPCODE_OFFSET, 0xb7},
                     {SPI_DEVICE_CMD_INFO_EN4B_VALID_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_spi_device_configure_flash_en4b_command(
      &spi_, kDifToggleEnabled, /*opcode=*/0xb7));
  EXPECT_WRITE32(SPI_DEVICE_CMD_INFO_EX4B_REG_OFFSET,
                 {
                     {SPI_DEVICE_CMD_INFO_EX4B_OPCODE_OFFSET, 0xe9},
                     {SPI_DEVICE_CMD_INFO_EX4B_VALID_BIT, 0},
                 });
  EXPECT_DIF_OK(dif_spi_device_configure_flash_ex4b_command(
      &spi_, kDifToggleDisabled, /*opcode=*/0xe9));
  EXPECT_WRITE32(SPI_DEVICE_CMD_INFO_WREN_REG_OFFSET,
                 {
                     {SPI_DEVICE_CMD_INFO_WREN_OPCODE_OFFSET, 0x06},
                     {SPI_DEVICE_CMD_INFO_WREN_VALID_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_spi_device_configure_flash_wren_command(
      &spi_, kDifToggleEnabled, /*opcode=*/0x06));
  EXPECT_WRITE32(SPI_DEVICE_CMD_INFO_WRDI_REG_OFFSET,
                 {
                     {SPI_DEVICE_CMD_INFO_WRDI_OPCODE_OFFSET, 0x04},
                     {SPI_DEVICE_CMD_INFO_WRDI_VALID_BIT, 0},
                 });
  EXPECT_DIF_OK(dif_spi_device_configure_flash_wrdi_command(
      &spi_, kDifToggleDisabled, /*opcode=*/0x04));
}

TEST_F(FlashTest, Swaps) {
  EXPECT_WRITE32(SPI_DEVICE_ADDR_SWAP_MASK_REG_OFFSET, 0x10203456u);
  EXPECT_WRITE32(SPI_DEVICE_ADDR_SWAP_DATA_REG_OFFSET, 0xffff0000u);
  EXPECT_DIF_OK(
      dif_spi_device_set_flash_address_swap(&spi_, 0x10203456u, 0xffff0000u));

  EXPECT_WRITE32(SPI_DEVICE_PAYLOAD_SWAP_MASK_REG_OFFSET, 0x24587001u);
  EXPECT_WRITE32(SPI_DEVICE_PAYLOAD_SWAP_DATA_REG_OFFSET, 0xa5a5f00fu);
  EXPECT_DIF_OK(
      dif_spi_device_set_flash_payload_swap(&spi_, 0x24587001u, 0xa5a5f00fu));
}

TEST_F(FlashTest, FifoOccupancy) {
  uint8_t cmd_fifo_occupancy, addr_fifo_occupancy;
  uint16_t payload_fifo_occupancy;
  uint32_t payload_start_offset;
  EXPECT_READ32(SPI_DEVICE_UPLOAD_STATUS_REG_OFFSET,
                {
                    {SPI_DEVICE_UPLOAD_STATUS_CMDFIFO_DEPTH_OFFSET, 3},
                    {SPI_DEVICE_UPLOAD_STATUS_CMDFIFO_NOTEMPTY_BIT, 1},
                    {SPI_DEVICE_UPLOAD_STATUS_ADDRFIFO_DEPTH_OFFSET, 2},
                    {SPI_DEVICE_UPLOAD_STATUS_ADDRFIFO_NOTEMPTY_BIT, 1},
                });
  EXPECT_DIF_OK(dif_spi_device_get_flash_command_fifo_occupancy(
      &spi_, &cmd_fifo_occupancy));
  EXPECT_EQ(cmd_fifo_occupancy, 3);

  EXPECT_READ32(SPI_DEVICE_UPLOAD_STATUS_REG_OFFSET,
                {
                    {SPI_DEVICE_UPLOAD_STATUS_CMDFIFO_DEPTH_OFFSET, 0},
                    {SPI_DEVICE_UPLOAD_STATUS_CMDFIFO_NOTEMPTY_BIT, 0},
                    {SPI_DEVICE_UPLOAD_STATUS_ADDRFIFO_DEPTH_OFFSET, 2},
                    {SPI_DEVICE_UPLOAD_STATUS_ADDRFIFO_NOTEMPTY_BIT, 1},
                });
  EXPECT_DIF_OK(dif_spi_device_get_flash_address_fifo_occupancy(
      &spi_, &addr_fifo_occupancy));
  EXPECT_EQ(addr_fifo_occupancy, 2);

  EXPECT_READ32(SPI_DEVICE_UPLOAD_STATUS2_REG_OFFSET,
                {
                    {SPI_DEVICE_UPLOAD_STATUS2_PAYLOAD_DEPTH_OFFSET, 256},
                    {SPI_DEVICE_UPLOAD_STATUS2_PAYLOAD_START_IDX_OFFSET, 3},
                });
  EXPECT_DIF_OK(dif_spi_device_get_flash_payload_fifo_occupancy(
      &spi_, &payload_fifo_occupancy, &payload_start_offset));
  EXPECT_EQ(payload_fifo_occupancy, 256);
  EXPECT_EQ(payload_start_offset, 3);
}

TEST_F(FlashTest, FifoPop) {
  uint8_t command;
  uint32_t address;
  EXPECT_READ32(SPI_DEVICE_UPLOAD_STATUS_REG_OFFSET,
                {
                    {SPI_DEVICE_UPLOAD_STATUS_CMDFIFO_NOTEMPTY_BIT, 0},
                    {SPI_DEVICE_UPLOAD_STATUS_ADDRFIFO_NOTEMPTY_BIT, 1},
                });
  EXPECT_EQ(dif_spi_device_pop_flash_command_fifo(&spi_, &command),
            kDifUnavailable);

  EXPECT_READ32(SPI_DEVICE_UPLOAD_STATUS_REG_OFFSET,
                {
                    {SPI_DEVICE_UPLOAD_STATUS_CMDFIFO_NOTEMPTY_BIT, 1},
                    {SPI_DEVICE_UPLOAD_STATUS_ADDRFIFO_NOTEMPTY_BIT, 1},
                });
  EXPECT_READ32(SPI_DEVICE_UPLOAD_CMDFIFO_REG_OFFSET, 0x06);
  EXPECT_DIF_OK(dif_spi_device_pop_flash_command_fifo(&spi_, &command));
  EXPECT_EQ(command, 0x06);

  EXPECT_READ32(SPI_DEVICE_UPLOAD_STATUS_REG_OFFSET,
                {
                    {SPI_DEVICE_UPLOAD_STATUS_CMDFIFO_NOTEMPTY_BIT, 1},
                    {SPI_DEVICE_UPLOAD_STATUS_ADDRFIFO_NOTEMPTY_BIT, 0},
                });
  EXPECT_EQ(dif_spi_device_pop_flash_address_fifo(&spi_, &address),
            kDifUnavailable);

  EXPECT_READ32(SPI_DEVICE_UPLOAD_STATUS_REG_OFFSET,
                {
                    {SPI_DEVICE_UPLOAD_STATUS_CMDFIFO_NOTEMPTY_BIT, 1},
                    {SPI_DEVICE_UPLOAD_STATUS_ADDRFIFO_NOTEMPTY_BIT, 1},
                });
  EXPECT_READ32(SPI_DEVICE_UPLOAD_ADDRFIFO_REG_OFFSET, 0x76543210);
  EXPECT_DIF_OK(dif_spi_device_pop_flash_address_fifo(&spi_, &address));
  EXPECT_EQ(address, 0x76543210);
}

TEST_F(FlashTest, MemoryOps) {
  constexpr uint32_t kSfdpOffset = 3072;

  uint32_t buf[64];
  for (uint32_t i = 0; i < (sizeof(buf) / sizeof(buf[0])); i++) {
    buf[i] = i;
    EXPECT_WRITE32(SPI_DEVICE_EGRESS_BUFFER_REG_OFFSET + kSfdpOffset +
                       i * sizeof(uint32_t),
                   i);
  }
  EXPECT_DIF_OK(dif_spi_device_write_flash_buffer(
      &spi_, kDifSpiDeviceFlashBufferTypeSfdp, /*offset=*/0,
      /*length=*/sizeof(buf), reinterpret_cast<uint8_t *>(buf)));
  for (uint32_t i = 4; i < (sizeof(buf) / sizeof(buf[0])); i++) {
    EXPECT_READ32(SPI_DEVICE_INGRESS_BUFFER_REG_OFFSET + i * sizeof(uint32_t),
                  0x1000u - i);
  }
  EXPECT_DIF_OK(dif_spi_device_read_flash_payload_buffer(
      &spi_, /*offset=*/16,
      /*length=*/sizeof(buf) - 16, reinterpret_cast<uint8_t *>(buf)));
  for (uint32_t i = 4; i < (sizeof(buf) / sizeof(buf[0])); i++) {
    EXPECT_EQ(buf[i - 4], 0x1000u - i);
  }
}

TEST_F(FlashTest, CommandFilters) {
  dif_toggle_t toggle;
  EXPECT_READ32(SPI_DEVICE_CMD_FILTER_0_REG_OFFSET, 0xa5642301u);
  EXPECT_DIF_OK(dif_spi_device_get_passthrough_command_filter(
      &spi_, /*opcode=*/18, &toggle));
  EXPECT_EQ(toggle, kDifToggleEnabled);

  EXPECT_READ32(SPI_DEVICE_CMD_FILTER_3_REG_OFFSET, 0xa5642301u);
  EXPECT_DIF_OK(dif_spi_device_get_passthrough_command_filter(
      &spi_, /*opcode=*/(3 * 32 + 19), &toggle));
  EXPECT_EQ(toggle, kDifToggleDisabled);

  EXPECT_READ32(SPI_DEVICE_CMD_FILTER_0_REG_OFFSET, 0xa5a5a5a5u);
  EXPECT_WRITE32(SPI_DEVICE_CMD_FILTER_0_REG_OFFSET, 0xa585a5a5u);
  EXPECT_DIF_OK(dif_spi_device_set_passthrough_command_filter(
      &spi_, /*opcode=*/21, kDifToggleDisabled));

  EXPECT_READ32(SPI_DEVICE_CMD_FILTER_7_REG_OFFSET, 0x5555aaaau);
  EXPECT_WRITE32(SPI_DEVICE_CMD_FILTER_7_REG_OFFSET, 0x5555aaabu);
  EXPECT_DIF_OK(dif_spi_device_set_passthrough_command_filter(
      &spi_, /*opcode=*/224, kDifToggleEnabled));

  for (int i = 0; i < 8; i++) {
    EXPECT_WRITE32(SPI_DEVICE_CMD_FILTER_0_REG_OFFSET + i * sizeof(uint32_t),
                   0);
  }
  EXPECT_DIF_OK(dif_spi_device_set_all_passthrough_command_filters(
      &spi_, kDifToggleDisabled));

  for (int i = 0; i < 8; i++) {
    EXPECT_WRITE32(SPI_DEVICE_CMD_FILTER_0_REG_OFFSET + i * sizeof(uint32_t),
                   UINT32_MAX);
  }
  EXPECT_DIF_OK(dif_spi_device_set_all_passthrough_command_filters(
      &spi_, kDifToggleEnabled));
}

TEST_F(FlashTest, StatusRegisters) {
  uint32_t status;
  EXPECT_READ32(SPI_DEVICE_FLASH_STATUS_REG_OFFSET,
                {
                    {SPI_DEVICE_FLASH_STATUS_BUSY_BIT, 1},
                    {SPI_DEVICE_FLASH_STATUS_STATUS_OFFSET, 0x143200},
                });
  EXPECT_WRITE32(SPI_DEVICE_FLASH_STATUS_REG_OFFSET,
                 {
                     {SPI_DEVICE_FLASH_STATUS_BUSY_BIT, 0},
                     {SPI_DEVICE_FLASH_STATUS_STATUS_OFFSET, 0x143200},
                 });
  EXPECT_DIF_OK(dif_spi_device_clear_flash_busy_bit(&spi_));

  EXPECT_WRITE32(SPI_DEVICE_FLASH_STATUS_REG_OFFSET, 0x198234);
  EXPECT_DIF_OK(
      dif_spi_device_set_flash_status_registers(&spi_, /*status=*/0x198234));

  EXPECT_READ32(SPI_DEVICE_FLASH_STATUS_REG_OFFSET, 0x765432);
  EXPECT_DIF_OK(dif_spi_device_get_flash_status_registers(&spi_, &status));
  EXPECT_EQ(status, 0x765432);

  EXPECT_WRITE32(SPI_DEVICE_CONTROL_REG_OFFSET,
                 {
                     {SPI_DEVICE_CONTROL_MODE_OFFSET,
                      SPI_DEVICE_CONTROL_MODE_VALUE_PASSTHROUGH},
                     {SPI_DEVICE_CONTROL_FLASH_STATUS_FIFO_CLR_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_spi_device_clear_flash_status_request(&spi_));
}

class TpmTest : public SpiTest {};

TEST_F(TpmTest, NullArgs) {
  dif_spi_device_tpm_caps_t caps;
  dif_spi_device_tpm_config_t config;
  dif_spi_device_tpm_data_status_t status;
  dif_spi_device_tpm_id id;
  uint8_t uint8_arg;
  uint32_t uint32_arg;
  EXPECT_DIF_BADARG(dif_spi_device_get_tpm_capabilities(nullptr, &caps));
  EXPECT_DIF_BADARG(dif_spi_device_get_tpm_capabilities(&spi_, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_configure(nullptr, kDifToggleEnabled, config));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_get_data_status(nullptr, &status));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_get_data_status(&spi_, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_set_access_reg(nullptr, /*locality=*/0, /*value=*/0));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_get_access_reg(nullptr, /*locality=*/0, &uint8_arg));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_get_access_reg(&spi_, /*locality=*/0, nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_set_sts_reg(nullptr, /*value=*/0));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_get_sts_reg(nullptr, &uint32_arg));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_get_sts_reg(&spi_, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_set_intf_capability_reg(nullptr, /*value=*/0));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_get_intf_capability_reg(nullptr, &uint32_arg));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_get_intf_capability_reg(&spi_, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_set_int_enable_reg(nullptr, /*value=*/0));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_get_int_enable_reg(nullptr, &uint32_arg));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_get_int_enable_reg(&spi_, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_set_int_vector_reg(nullptr, /*value=*/0));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_get_int_vector_reg(nullptr, &uint32_arg));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_get_int_vector_reg(&spi_, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_set_int_status_reg(nullptr, /*value=*/0));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_get_int_status_reg(nullptr, &uint32_arg));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_get_int_status_reg(&spi_, nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_set_id(nullptr, id));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_get_id(nullptr, &id));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_get_id(&spi_, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_get_command(nullptr, &uint8_arg, &uint32_arg));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_get_command(&spi_, nullptr, &uint32_arg));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_get_command(&spi_, &uint8_arg, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_write_data(nullptr, /*length=*/0, &uint8_arg));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_write_data(&spi_, /*length=*/0, nullptr));
  EXPECT_DIF_BADARG(
      dif_spi_device_tpm_read_data(nullptr, /*length=*/0, &uint8_arg));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_read_data(&spi_, /*length=*/0, nullptr));
  EXPECT_DIF_BADARG(dif_spi_device_tpm_free_write_fifo(nullptr));
}

TEST_F(TpmTest, InitDevice) {
  dif_spi_device_tpm_caps_t caps;
  EXPECT_READ32(SPI_DEVICE_TPM_CAP_REG_OFFSET,
                {{SPI_DEVICE_TPM_CAP_REV_OFFSET, 3},
                 {SPI_DEVICE_TPM_CAP_LOCALITY_BIT, 1},
                 {SPI_DEVICE_TPM_CAP_MAX_WR_SIZE_OFFSET, 6},
                 {SPI_DEVICE_TPM_CAP_MAX_RD_SIZE_OFFSET, 6}});
  EXPECT_DIF_OK(dif_spi_device_get_tpm_capabilities(&spi_, &caps));
  EXPECT_EQ(caps.revision, 3);
  EXPECT_TRUE(caps.multi_locality);
  EXPECT_EQ(caps.max_write_size, 6);
  EXPECT_EQ(caps.max_read_size, 6);

  dif_spi_device_tpm_config_t config = {
      .interface = kDifSpiDeviceTpmInterfaceFifo,
      .disable_return_by_hardware = false,
      .disable_address_prefix_check = true,
      .disable_locality_check = true,
  };
  EXPECT_WRITE32(SPI_DEVICE_TPM_CFG_REG_OFFSET,
                 {
                     {SPI_DEVICE_TPM_CFG_EN_BIT, 1},
                     {SPI_DEVICE_TPM_CFG_TPM_MODE_BIT, 0},
                     {SPI_DEVICE_TPM_CFG_HW_REG_DIS_BIT, 0},
                     {SPI_DEVICE_TPM_CFG_TPM_REG_CHK_DIS_BIT, 1},
                     {SPI_DEVICE_TPM_CFG_INVALID_LOCALITY_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_spi_device_tpm_configure(&spi_, kDifToggleEnabled, config));
  EXPECT_WRITE32(SPI_DEVICE_TPM_CFG_REG_OFFSET,
                 {
                     {SPI_DEVICE_TPM_CFG_EN_BIT, 0},
                 });
  EXPECT_DIF_OK(
      dif_spi_device_tpm_configure(&spi_, kDifToggleDisabled, config));
}

TEST_F(TpmTest, TpmAccess) {
  uint8_t access;
  EXPECT_READ32(SPI_DEVICE_TPM_ACCESS_0_REG_OFFSET,
                {
                    {SPI_DEVICE_TPM_ACCESS_0_ACCESS_0_OFFSET, 6},
                    {SPI_DEVICE_TPM_ACCESS_0_ACCESS_1_OFFSET, 9},
                    {SPI_DEVICE_TPM_ACCESS_0_ACCESS_2_OFFSET, 10},
                    {SPI_DEVICE_TPM_ACCESS_0_ACCESS_3_OFFSET, 5},
                });
  EXPECT_WRITE32(SPI_DEVICE_TPM_ACCESS_0_REG_OFFSET,
                 {
                     {SPI_DEVICE_TPM_ACCESS_0_ACCESS_0_OFFSET, 6},
                     {SPI_DEVICE_TPM_ACCESS_0_ACCESS_1_OFFSET, 9},
                     {SPI_DEVICE_TPM_ACCESS_0_ACCESS_2_OFFSET, 78},
                     {SPI_DEVICE_TPM_ACCESS_0_ACCESS_3_OFFSET, 5},
                 });
  EXPECT_DIF_OK(dif_spi_device_tpm_set_access_reg(&spi_, 2, 78));

  EXPECT_READ32(SPI_DEVICE_TPM_ACCESS_1_REG_OFFSET,
                {{SPI_DEVICE_TPM_ACCESS_1_ACCESS_4_OFFSET, 3}});
  EXPECT_WRITE32(SPI_DEVICE_TPM_ACCESS_1_REG_OFFSET,
                 {{SPI_DEVICE_TPM_ACCESS_1_ACCESS_4_OFFSET, 92}});
  EXPECT_DIF_OK(dif_spi_device_tpm_set_access_reg(&spi_, 4, 92));

  EXPECT_READ32(SPI_DEVICE_TPM_ACCESS_0_REG_OFFSET,
                {
                    {SPI_DEVICE_TPM_ACCESS_0_ACCESS_0_OFFSET, 0},
                    {SPI_DEVICE_TPM_ACCESS_0_ACCESS_1_OFFSET, 1},
                    {SPI_DEVICE_TPM_ACCESS_0_ACCESS_2_OFFSET, 2},
                    {SPI_DEVICE_TPM_ACCESS_0_ACCESS_3_OFFSET, 3},
                });
  EXPECT_DIF_OK(dif_spi_device_tpm_get_access_reg(&spi_, 3, &access));
  EXPECT_EQ(access, 3);

  EXPECT_READ32(SPI_DEVICE_TPM_ACCESS_1_REG_OFFSET,
                {{SPI_DEVICE_TPM_ACCESS_1_ACCESS_4_OFFSET, 4}});
  EXPECT_DIF_OK(dif_spi_device_tpm_get_access_reg(&spi_, 4, &access));
  EXPECT_EQ(access, 4);
}

TEST_F(TpmTest, HardwareRegs32) {
  uint32_t reg_val;
  EXPECT_WRITE32(SPI_DEVICE_TPM_STS_REG_OFFSET, 0x12345678);
  EXPECT_DIF_OK(dif_spi_device_tpm_set_sts_reg(&spi_, 0x12345678));
  EXPECT_READ32(SPI_DEVICE_TPM_STS_REG_OFFSET, 0x76543210);
  EXPECT_DIF_OK(dif_spi_device_tpm_get_sts_reg(&spi_, &reg_val));
  EXPECT_EQ(reg_val, 0x76543210);

  EXPECT_WRITE32(SPI_DEVICE_TPM_INTF_CAPABILITY_REG_OFFSET, 0x12345678);
  EXPECT_DIF_OK(dif_spi_device_tpm_set_intf_capability_reg(&spi_, 0x12345678));
  EXPECT_READ32(SPI_DEVICE_TPM_INTF_CAPABILITY_REG_OFFSET, 0x76543210);
  EXPECT_DIF_OK(dif_spi_device_tpm_get_intf_capability_reg(&spi_, &reg_val));
  EXPECT_EQ(reg_val, 0x76543210);

  EXPECT_WRITE32(SPI_DEVICE_TPM_INT_ENABLE_REG_OFFSET, 0x12345678);
  EXPECT_DIF_OK(dif_spi_device_tpm_set_int_enable_reg(&spi_, 0x12345678));
  EXPECT_READ32(SPI_DEVICE_TPM_INT_ENABLE_REG_OFFSET, 0x76543210);
  EXPECT_DIF_OK(dif_spi_device_tpm_get_int_enable_reg(&spi_, &reg_val));
  EXPECT_EQ(reg_val, 0x76543210);

  EXPECT_WRITE32(SPI_DEVICE_TPM_INT_VECTOR_REG_OFFSET, 0x12345678);
  EXPECT_DIF_OK(dif_spi_device_tpm_set_int_vector_reg(&spi_, 0x12345678));
  EXPECT_READ32(SPI_DEVICE_TPM_INT_VECTOR_REG_OFFSET, 0x76543210);
  EXPECT_DIF_OK(dif_spi_device_tpm_get_int_vector_reg(&spi_, &reg_val));
  EXPECT_EQ(reg_val, 0x76543210);

  EXPECT_WRITE32(SPI_DEVICE_TPM_INT_STATUS_REG_OFFSET, 0x12345678);
  EXPECT_DIF_OK(dif_spi_device_tpm_set_int_status_reg(&spi_, 0x12345678));
  EXPECT_READ32(SPI_DEVICE_TPM_INT_STATUS_REG_OFFSET, 0x76543210);
  EXPECT_DIF_OK(dif_spi_device_tpm_get_int_status_reg(&spi_, &reg_val));
  EXPECT_EQ(reg_val, 0x76543210);
}

TEST_F(TpmTest, IdRegs) {
  dif_spi_device_tpm_id_t tpm_id = {
      .vendor_id = 0x1234,
      .device_id = 0x5678,
      .revision = 0xa5,
  };
  EXPECT_WRITE32(SPI_DEVICE_TPM_DID_VID_REG_OFFSET,
                 {
                     {SPI_DEVICE_TPM_DID_VID_VID_OFFSET, tpm_id.vendor_id},
                     {SPI_DEVICE_TPM_DID_VID_DID_OFFSET, tpm_id.device_id},
                 });
  EXPECT_WRITE32(SPI_DEVICE_TPM_RID_REG_OFFSET,
                 {{SPI_DEVICE_TPM_RID_RID_OFFSET, tpm_id.revision}});
  EXPECT_DIF_OK(dif_spi_device_tpm_set_id(&spi_, tpm_id));

  EXPECT_READ32(SPI_DEVICE_TPM_DID_VID_REG_OFFSET,
                {
                    {SPI_DEVICE_TPM_DID_VID_VID_OFFSET, 0x7654},
                    {SPI_DEVICE_TPM_DID_VID_DID_OFFSET, 0x3210},
                });
  EXPECT_READ32(SPI_DEVICE_TPM_RID_REG_OFFSET,
                {{SPI_DEVICE_TPM_RID_RID_OFFSET, 0x68}});
  EXPECT_DIF_OK(dif_spi_device_tpm_get_id(&spi_, &tpm_id));
  EXPECT_EQ(tpm_id.vendor_id, 0x7654);
  EXPECT_EQ(tpm_id.device_id, 0x3210);
  EXPECT_EQ(tpm_id.revision, 0x68);
}

TEST_F(TpmTest, CommandAndData) {
  dif_spi_device_tpm_data_status_t status;
  uint8_t command;
  uint32_t address;
  uint8_t data[4] = {17, 34, 51, 68};
  uint32_t read_data[4];
  EXPECT_READ32(SPI_DEVICE_TPM_STATUS_REG_OFFSET,
                {
                    {SPI_DEVICE_TPM_STATUS_CMDADDR_NOTEMPTY_BIT, 0},
                    {SPI_DEVICE_TPM_STATUS_WRFIFO_PENDING_BIT, 1},
                });
  EXPECT_DIF_OK(dif_spi_device_tpm_get_data_status(&spi_, &status));
  EXPECT_FALSE(status.cmd_addr_valid);
  EXPECT_TRUE(status.wrfifo_acquired);

  EXPECT_READ32(SPI_DEVICE_TPM_STATUS_REG_OFFSET,
                {
                    {SPI_DEVICE_TPM_STATUS_CMDADDR_NOTEMPTY_BIT, 1},
                    {SPI_DEVICE_TPM_STATUS_WRFIFO_PENDING_BIT, 0},
                });
  EXPECT_DIF_OK(dif_spi_device_tpm_get_data_status(&spi_, &status));
  EXPECT_TRUE(status.cmd_addr_valid);
  EXPECT_FALSE(status.wrfifo_acquired);

  EXPECT_READ32(SPI_DEVICE_TPM_CMD_ADDR_REG_OFFSET,
                {
                    {SPI_DEVICE_TPM_CMD_ADDR_CMD_OFFSET, 0x43},
                    {SPI_DEVICE_TPM_CMD_ADDR_ADDR_OFFSET, 0xd40124},
                });
  EXPECT_DIF_OK(dif_spi_device_tpm_get_command(&spi_, &command, &address));
  EXPECT_EQ(command, 0x43);
  EXPECT_EQ(address, 0xd40124);

  EXPECT_READ32(SPI_DEVICE_TPM_STATUS_REG_OFFSET,
                {
                    {SPI_DEVICE_TPM_STATUS_CMDADDR_NOTEMPTY_BIT, 0},
                    {SPI_DEVICE_TPM_STATUS_WRFIFO_PENDING_BIT, 0},
                });
  EXPECT_WRITE32(SPI_DEVICE_TPM_READ_FIFO_REG_OFFSET,
                 (data[3] << 24) | (data[2] << 16) | (data[1] << 8) | data[0]);

  EXPECT_DIF_OK(dif_spi_device_tpm_write_data(&spi_, /*length=*/3, data));

  for (uint32_t i = 0; i < 4; i++) {
    constexpr uint32_t kSpiDeviceTpmWriteFifoOffset =
        SPI_DEVICE_INGRESS_BUFFER_REG_OFFSET +
        SPI_DEVICE_PARAM_SRAM_TPM_WR_FIFO_OFFSET * sizeof(uint32_t);
    EXPECT_READ32(kSpiDeviceTpmWriteFifoOffset + i * sizeof(uint32_t), 18 * i);
  }
  EXPECT_DIF_OK(
      dif_spi_device_tpm_read_data(&spi_, /*length=*/16, (uint8_t *)read_data));
  for (int i = 0; i < 4; i++) {
    EXPECT_EQ(read_data[i], 18 * i);
  }
  EXPECT_WRITE32(SPI_DEVICE_TPM_STATUS_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_spi_device_tpm_free_write_fifo(&spi_));
}

}  // namespace
}  // namespace dif_spi_device_unittest
