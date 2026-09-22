// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_usbdev.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "hw/top/usbdev_regs.h"  // Generated.

namespace dif_usbdev_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

class UsbdevTest : public Test, public MmioTest {
 protected:
  dif_usbdev_t usbdev_ = {
      .base_addr = dev().region(),
  };
};

TEST_F(UsbdevTest, NullArgsTest) {
  dif_usbdev_config_t config;
  dif_usbdev_buffer_pool_t buffer_pool;
  bool bool_arg, bool_arg2;
  dif_usbdev_rx_packet_info_t packet_info;
  dif_usbdev_buffer_t buffer;
  uint8_t uint8_arg, uint8_arg2;
  size_t size_arg;
  dif_usbdev_endpoint_id_t endpoint_id;
  dif_usbdev_tx_status_t tx_status;
  uint16_t uint16_arg;
  dif_usbdev_link_state_t link_state;
  dif_usbdev_wake_status_t wake_status;
  dif_usbdev_phy_pins_sense_t phy_pins_status;
  dif_usbdev_phy_pins_drive_t phy_pins_drive;

  EXPECT_DIF_BADARG(dif_usbdev_configure(nullptr, &buffer_pool, config));
  EXPECT_DIF_BADARG(dif_usbdev_configure(&usbdev_, nullptr, config));
  EXPECT_DIF_BADARG(dif_usbdev_fill_available_fifos(nullptr, &buffer_pool));
  EXPECT_DIF_BADARG(dif_usbdev_fill_available_fifos(&usbdev_, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_endpoint_setup_enable(nullptr, /*endpoint=*/0,
                                                     kDifToggleEnabled));
  EXPECT_DIF_BADARG(dif_usbdev_endpoint_out_enable(nullptr, /*endpoint=*/0,
                                                   kDifToggleEnabled));
  EXPECT_DIF_BADARG(dif_usbdev_endpoint_set_nak_out_enable(
      nullptr, /*endpoint=*/0, kDifToggleEnabled));
  EXPECT_DIF_BADARG(dif_usbdev_endpoint_stall_enable(nullptr, endpoint_id,
                                                     kDifToggleEnabled));
  EXPECT_DIF_BADARG(
      dif_usbdev_endpoint_stall_get(nullptr, endpoint_id, &bool_arg));
  EXPECT_DIF_BADARG(
      dif_usbdev_endpoint_stall_get(&usbdev_, endpoint_id, nullptr));
  EXPECT_DIF_BADARG(
      dif_usbdev_endpoint_iso_enable(nullptr, endpoint_id, kDifToggleEnabled));
  EXPECT_DIF_BADARG(
      dif_usbdev_endpoint_enable(nullptr, endpoint_id, kDifToggleEnabled));
  EXPECT_DIF_BADARG(dif_usbdev_interface_enable(nullptr, kDifToggleEnabled));
  EXPECT_DIF_BADARG(dif_usbdev_recv(nullptr, &packet_info, &buffer));
  EXPECT_DIF_BADARG(dif_usbdev_recv(&usbdev_, nullptr, &buffer));
  EXPECT_DIF_BADARG(dif_usbdev_recv(&usbdev_, &packet_info, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_read(
      nullptr, &buffer_pool, &buffer, &uint8_arg, /*dst_len=*/1, &size_arg));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_read(
      &usbdev_, nullptr, &buffer, &uint8_arg, /*dst_len=*/1, &size_arg));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_read(
      &usbdev_, &buffer_pool, nullptr, &uint8_arg, /*dst_len=*/1, &size_arg));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_read(&usbdev_, &buffer_pool, &buffer,
                                           nullptr, /*dst_len=*/1, &size_arg));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_read(&usbdev_, &buffer_pool, &buffer,
                                           &uint8_arg, /*dst_len=*/1, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_return(nullptr, &buffer_pool, &buffer));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_return(&usbdev_, nullptr, &buffer));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_return(&usbdev_, &buffer_pool, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_request(nullptr, &buffer_pool, &buffer));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_request(&usbdev_, nullptr, &buffer));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_request(&usbdev_, &buffer_pool, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_write(nullptr, &buffer, &uint8_arg,
                                            /*src_len=*/1, &size_arg));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_write(&usbdev_, nullptr, &uint8_arg,
                                            /*src_len=*/1, &size_arg));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_write(&usbdev_, &buffer, nullptr,
                                            /*src_len=*/1, &size_arg));
  EXPECT_DIF_BADARG(dif_usbdev_buffer_write(&usbdev_, &buffer, &uint8_arg,
                                            /*src_len=*/1, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_send(nullptr, /*endpoint=*/0, &buffer));
  EXPECT_DIF_BADARG(dif_usbdev_send(&usbdev_, /*endpoint=*/0, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_get_tx_sent(nullptr, &uint16_arg));
  EXPECT_DIF_BADARG(dif_usbdev_get_tx_sent(&usbdev_, nullptr));
  EXPECT_DIF_BADARG(
      dif_usbdev_clear_tx_status(nullptr, &buffer_pool, /*endpoint=*/0));
  EXPECT_DIF_BADARG(
      dif_usbdev_clear_tx_status(&usbdev_, nullptr, /*endpoint=*/0));
  EXPECT_DIF_BADARG(
      dif_usbdev_get_tx_status(nullptr, /*endpoint=*/0, &tx_status));
  EXPECT_DIF_BADARG(
      dif_usbdev_get_tx_status(&usbdev_, /*endpoint=*/0, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_address_set(nullptr, /*addr=*/1));
  EXPECT_DIF_BADARG(dif_usbdev_address_get(nullptr, &uint8_arg));
  EXPECT_DIF_BADARG(dif_usbdev_address_get(&usbdev_, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_clear_data_toggle(nullptr, /*endpoint=*/1));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_frame(nullptr, &uint16_arg));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_frame(&usbdev_, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_host_lost(nullptr, &bool_arg));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_host_lost(&usbdev_, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_link_state(nullptr, &link_state));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_link_state(&usbdev_, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_sense(nullptr, &bool_arg));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_sense(&usbdev_, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_available_fifo_depths(
      nullptr, &uint8_arg, &uint8_arg2));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_available_fifo_depths(
      &usbdev_, nullptr, &uint8_arg));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_available_fifo_depths(
      &usbdev_, &uint8_arg, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_available_fifo_full(
      nullptr, &bool_arg, &bool_arg2));
  EXPECT_DIF_BADARG(
      dif_usbdev_status_get_available_fifo_full(&usbdev_, nullptr, &bool_arg));
  EXPECT_DIF_BADARG(
      dif_usbdev_status_get_available_fifo_full(&usbdev_, &bool_arg, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_rx_fifo_depth(nullptr, &uint8_arg));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_rx_fifo_depth(&usbdev_, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_rx_fifo_empty(nullptr, &bool_arg));
  EXPECT_DIF_BADARG(dif_usbdev_status_get_rx_fifo_empty(&usbdev_, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_set_test_mode(nullptr, kDifUsbdevTestModeNone));
  EXPECT_DIF_BADARG(dif_usbdev_set_wake_enable(nullptr, kDifToggleEnabled));
  EXPECT_DIF_BADARG(dif_usbdev_get_wake_status(nullptr, &wake_status));
  EXPECT_DIF_BADARG(dif_usbdev_get_wake_status(&usbdev_, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_resume_link_to_active(nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_get_phy_pins_status(nullptr, &phy_pins_status));
  EXPECT_DIF_BADARG(dif_usbdev_get_phy_pins_status(&usbdev_, nullptr));
  EXPECT_DIF_BADARG(dif_usbdev_set_phy_pins_state(nullptr, kDifToggleEnabled,
                                                  phy_pins_drive));
}

TEST_F(UsbdevTest, PhyConfig) {
  dif_usbdev_buffer_pool_t buffer_pool;
  dif_usbdev_config_t phy_config = {
      .have_differential_receiver = kDifToggleEnabled,
      .use_tx_d_se0 = kDifToggleDisabled,
      .single_bit_eop = kDifToggleDisabled,
      .pin_flip = kDifToggleEnabled,
      .clock_sync_signals = kDifToggleEnabled,
  };
  EXPECT_WRITE32(USBDEV_PHY_CONFIG_REG_OFFSET,
                 {
                     {USBDEV_PHY_CONFIG_USE_DIFF_RCVR_BIT, 1},
                     {USBDEV_PHY_CONFIG_TX_USE_D_SE0_BIT, 0},
                     {USBDEV_PHY_CONFIG_EOP_SINGLE_BIT_BIT, 0},
                     {USBDEV_PHY_CONFIG_PINFLIP_BIT, 1},
                     {USBDEV_PHY_CONFIG_USB_REF_DISABLE_BIT, 0},
                 });
  EXPECT_DIF_OK(dif_usbdev_configure(&usbdev_, &buffer_pool, phy_config));

  dif_usbdev_phy_pins_sense_t phy_pins_status;
  EXPECT_READ32(USBDEV_PHY_PINS_SENSE_REG_OFFSET,
                {
                    {USBDEV_PHY_PINS_SENSE_RX_DP_I_BIT, 1},
                    {USBDEV_PHY_PINS_SENSE_RX_DN_I_BIT, 0},
                    {USBDEV_PHY_PINS_SENSE_RX_D_I_BIT, 1},
                    {USBDEV_PHY_PINS_SENSE_TX_DP_O_BIT, 0},
                    {USBDEV_PHY_PINS_SENSE_TX_DN_O_BIT, 1},
                    {USBDEV_PHY_PINS_SENSE_TX_D_O_BIT, 0},
                    {USBDEV_PHY_PINS_SENSE_TX_SE0_O_BIT, 0},
                    {USBDEV_PHY_PINS_SENSE_TX_OE_O_BIT, 1},
                    {USBDEV_PHY_PINS_SENSE_PWR_SENSE_BIT, 1},
                });
  EXPECT_DIF_OK(dif_usbdev_get_phy_pins_status(&usbdev_, &phy_pins_status));
  EXPECT_TRUE(phy_pins_status.rx_dp);
  EXPECT_FALSE(phy_pins_status.rx_dn);
  EXPECT_TRUE(phy_pins_status.rx_d);
  EXPECT_FALSE(phy_pins_status.tx_dp);
  EXPECT_TRUE(phy_pins_status.tx_dn);
  EXPECT_FALSE(phy_pins_status.tx_d);
  EXPECT_FALSE(phy_pins_status.tx_se0);
  EXPECT_TRUE(phy_pins_status.output_enable);
  EXPECT_TRUE(phy_pins_status.vbus_sense);

  dif_usbdev_phy_pins_drive_t overrides = {
      .dp = 0,
      .dn = 1,
      .data = 0,
      .se0 = 1,
      .output_enable = 1,
      .diff_receiver_enable = 0,
      .dp_pullup_en = 1,
      .dn_pullup_en = 0,
  };
  EXPECT_WRITE32(
      USBDEV_PHY_PINS_DRIVE_REG_OFFSET,
      {
          {USBDEV_PHY_PINS_DRIVE_DP_O_BIT, overrides.dp},
          {USBDEV_PHY_PINS_DRIVE_DN_O_BIT, overrides.dn},
          {USBDEV_PHY_PINS_DRIVE_D_O_BIT, overrides.data},
          {USBDEV_PHY_PINS_DRIVE_SE0_O_BIT, overrides.se0},
          {USBDEV_PHY_PINS_DRIVE_OE_O_BIT, overrides.output_enable},
          {USBDEV_PHY_PINS_DRIVE_RX_ENABLE_O_BIT,
           overrides.diff_receiver_enable},
          {USBDEV_PHY_PINS_DRIVE_DP_PULLUP_EN_O_BIT, overrides.dp_pullup_en},
          {USBDEV_PHY_PINS_DRIVE_DN_PULLUP_EN_O_BIT, overrides.dn_pullup_en},
          {USBDEV_PHY_PINS_DRIVE_EN_BIT, 1},
      });
  EXPECT_DIF_OK(
      dif_usbdev_set_phy_pins_state(&usbdev_, kDifToggleEnabled, overrides));

  EXPECT_WRITE32(USBDEV_PHY_PINS_DRIVE_REG_OFFSET, 0);
  EXPECT_DIF_OK(
      dif_usbdev_set_phy_pins_state(&usbdev_, kDifToggleDisabled, overrides));

  EXPECT_READ32(USBDEV_PHY_CONFIG_REG_OFFSET,
                {
                    {USBDEV_PHY_CONFIG_USE_DIFF_RCVR_BIT, 1},
                    {USBDEV_PHY_CONFIG_TX_USE_D_SE0_BIT, 0},
                    {USBDEV_PHY_CONFIG_EOP_SINGLE_BIT_BIT, 0},
                    {USBDEV_PHY_CONFIG_PINFLIP_BIT, 1},
                    {USBDEV_PHY_CONFIG_USB_REF_DISABLE_BIT, 0},
                    {USBDEV_PHY_CONFIG_TX_OSC_TEST_MODE_BIT, 0},
                    {USBDEV_PHY_CONFIG_TX_PKT_TEST_MODE_BIT, 0},
                });
  EXPECT_WRITE32(USBDEV_PHY_CONFIG_REG_OFFSET,
                 {
                     {USBDEV_PHY_CONFIG_USE_DIFF_RCVR_BIT, 1},
                     {USBDEV_PHY_CONFIG_TX_USE_D_SE0_BIT, 0},
                     {USBDEV_PHY_CONFIG_EOP_SINGLE_BIT_BIT, 0},
                     {USBDEV_PHY_CONFIG_PINFLIP_BIT, 1},
                     {USBDEV_PHY_CONFIG_USB_REF_DISABLE_BIT, 0},
                     {USBDEV_PHY_CONFIG_TX_OSC_TEST_MODE_BIT, 1},
                     {USBDEV_PHY_CONFIG_TX_PKT_TEST_MODE_BIT, 0},
                 });
  EXPECT_DIF_OK(dif_usbdev_set_test_mode(&usbdev_, kDifUsbdevTestModeTxOsc));

  EXPECT_READ32(USBDEV_PHY_CONFIG_REG_OFFSET,
                {
                    {USBDEV_PHY_CONFIG_USE_DIFF_RCVR_BIT, 1},
                    {USBDEV_PHY_CONFIG_TX_USE_D_SE0_BIT, 0},
                    {USBDEV_PHY_CONFIG_EOP_SINGLE_BIT_BIT, 0},
                    {USBDEV_PHY_CONFIG_PINFLIP_BIT, 1},
                    {USBDEV_PHY_CONFIG_USB_REF_DISABLE_BIT, 0},
                    {USBDEV_PHY_CONFIG_TX_OSC_TEST_MODE_BIT, 1},
                    {USBDEV_PHY_CONFIG_TX_PKT_TEST_MODE_BIT, 0},
                });
  EXPECT_WRITE32(USBDEV_PHY_CONFIG_REG_OFFSET,
                 {
                     {USBDEV_PHY_CONFIG_USE_DIFF_RCVR_BIT, 1},
                     {USBDEV_PHY_CONFIG_TX_USE_D_SE0_BIT, 0},
                     {USBDEV_PHY_CONFIG_EOP_SINGLE_BIT_BIT, 0},
                     {USBDEV_PHY_CONFIG_PINFLIP_BIT, 1},
                     {USBDEV_PHY_CONFIG_USB_REF_DISABLE_BIT, 0},
                     {USBDEV_PHY_CONFIG_TX_OSC_TEST_MODE_BIT, 0},
                     {USBDEV_PHY_CONFIG_TX_PKT_TEST_MODE_BIT, 1},
                 });

  EXPECT_DIF_OK(dif_usbdev_set_test_mode(&usbdev_, kDifUsbdevTestModeTxPacket));

  EXPECT_READ32(USBDEV_PHY_CONFIG_REG_OFFSET,
                {
                    {USBDEV_PHY_CONFIG_USE_DIFF_RCVR_BIT, 1},
                    {USBDEV_PHY_CONFIG_TX_USE_D_SE0_BIT, 0},
                    {USBDEV_PHY_CONFIG_EOP_SINGLE_BIT_BIT, 0},
                    {USBDEV_PHY_CONFIG_PINFLIP_BIT, 1},
                    {USBDEV_PHY_CONFIG_USB_REF_DISABLE_BIT, 0},
                    {USBDEV_PHY_CONFIG_TX_OSC_TEST_MODE_BIT, 0},
                    {USBDEV_PHY_CONFIG_TX_PKT_TEST_MODE_BIT, 1},
                });
  EXPECT_WRITE32(USBDEV_PHY_CONFIG_REG_OFFSET,
                 {
                     {USBDEV_PHY_CONFIG_USE_DIFF_RCVR_BIT, 1},
                     {USBDEV_PHY_CONFIG_TX_USE_D_SE0_BIT, 0},
                     {USBDEV_PHY_CONFIG_EOP_SINGLE_BIT_BIT, 0},
                     {USBDEV_PHY_CONFIG_PINFLIP_BIT, 1},
                     {USBDEV_PHY_CONFIG_USB_REF_DISABLE_BIT, 0},
                     {USBDEV_PHY_CONFIG_TX_OSC_TEST_MODE_BIT, 0},
                     {USBDEV_PHY_CONFIG_TX_PKT_TEST_MODE_BIT, 0},
                 });
  EXPECT_DIF_OK(dif_usbdev_set_test_mode(&usbdev_, kDifUsbdevTestModeNone));
}

TEST_F(UsbdevTest, ConnectAndConfig) {
  // Connect the interface.
  EXPECT_READ32(USBDEV_USBCTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(USBDEV_USBCTRL_REG_OFFSET, {{USBDEV_USBCTRL_ENABLE_BIT, 1}});
  EXPECT_DIF_OK(dif_usbdev_interface_enable(&usbdev_, kDifToggleEnabled));

  // Disconnect the interface.
  EXPECT_READ32(USBDEV_USBCTRL_REG_OFFSET,
                {
                    {USBDEV_USBCTRL_ENABLE_BIT, 1},
                    {USBDEV_USBCTRL_DEVICE_ADDRESS_OFFSET, 127},
                });
  EXPECT_WRITE32(USBDEV_USBCTRL_REG_OFFSET,
                 {
                     {USBDEV_USBCTRL_ENABLE_BIT, 0},
                     {USBDEV_USBCTRL_DEVICE_ADDRESS_OFFSET, 127},
                 });
  EXPECT_DIF_OK(dif_usbdev_interface_enable(&usbdev_, kDifToggleDisabled));

  dif_usbdev_endpoint_id_t endpoint = {
      .number = 2,
      .direction = 1,
  };
  EXPECT_READ32(USBDEV_EP_IN_ENABLE_REG_OFFSET,
                {
                    {USBDEV_EP_IN_ENABLE_ENABLE_0_BIT, 1},
                });
  EXPECT_WRITE32(USBDEV_EP_IN_ENABLE_REG_OFFSET,
                 {
                     {USBDEV_EP_IN_ENABLE_ENABLE_0_BIT, 1},
                     {USBDEV_EP_IN_ENABLE_ENABLE_2_BIT, 1},
                 });
  EXPECT_DIF_OK(
      dif_usbdev_endpoint_enable(&usbdev_, endpoint, kDifToggleEnabled));

  endpoint.number = 6;
  endpoint.direction = 0;
  EXPECT_READ32(USBDEV_EP_OUT_ENABLE_REG_OFFSET,
                {
                    {USBDEV_EP_OUT_ENABLE_ENABLE_5_BIT, 1},
                    {USBDEV_EP_OUT_ENABLE_ENABLE_6_BIT, 1},
                });
  EXPECT_WRITE32(USBDEV_EP_OUT_ENABLE_REG_OFFSET,
                 {
                     {USBDEV_EP_OUT_ENABLE_ENABLE_5_BIT, 1},
                 });
  EXPECT_DIF_OK(
      dif_usbdev_endpoint_enable(&usbdev_, endpoint, kDifToggleDisabled));

  endpoint.number = 11;
  endpoint.direction = 0;
  EXPECT_READ32(USBDEV_OUT_ISO_REG_OFFSET, {
                                               {USBDEV_OUT_ISO_ISO_5_BIT, 1},
                                           });
  EXPECT_WRITE32(USBDEV_OUT_ISO_REG_OFFSET, {
                                                {USBDEV_OUT_ISO_ISO_5_BIT, 1},
                                                {USBDEV_OUT_ISO_ISO_11_BIT, 1},
                                            });
  EXPECT_DIF_OK(
      dif_usbdev_endpoint_iso_enable(&usbdev_, endpoint, kDifToggleEnabled));

  endpoint.number = 7;
  endpoint.direction = 1;
  EXPECT_READ32(USBDEV_IN_ISO_REG_OFFSET, {
                                              {USBDEV_IN_ISO_ISO_1_BIT, 1},
                                              {USBDEV_IN_ISO_ISO_7_BIT, 1},
                                          });
  EXPECT_WRITE32(USBDEV_IN_ISO_REG_OFFSET, {
                                               {USBDEV_IN_ISO_ISO_1_BIT, 1},
                                           });
  EXPECT_DIF_OK(
      dif_usbdev_endpoint_iso_enable(&usbdev_, endpoint, kDifToggleDisabled));
}

TEST_F(UsbdevTest, OutEndpointConfig) {
  EXPECT_READ32(USBDEV_RXENABLE_SETUP_REG_OFFSET,
                {
                    {USBDEV_RXENABLE_SETUP_SETUP_0_BIT, 1},
                    {USBDEV_RXENABLE_SETUP_SETUP_10_BIT, 1},
                    {USBDEV_RXENABLE_SETUP_SETUP_11_BIT, 1},
                });
  EXPECT_WRITE32(USBDEV_RXENABLE_SETUP_REG_OFFSET,
                 {
                     {USBDEV_RXENABLE_SETUP_SETUP_0_BIT, 1},
                     {USBDEV_RXENABLE_SETUP_SETUP_9_BIT, 1},
                     {USBDEV_RXENABLE_SETUP_SETUP_10_BIT, 1},
                     {USBDEV_RXENABLE_SETUP_SETUP_11_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_usbdev_endpoint_setup_enable(&usbdev_, /*endpoint=*/9,
                                                 kDifToggleEnabled));

  EXPECT_READ32(USBDEV_RXENABLE_SETUP_REG_OFFSET,
                {
                    {USBDEV_RXENABLE_SETUP_SETUP_8_BIT, 1},
                    {USBDEV_RXENABLE_SETUP_SETUP_9_BIT, 1},
                    {USBDEV_RXENABLE_SETUP_SETUP_10_BIT, 1},
                });
  EXPECT_WRITE32(USBDEV_RXENABLE_SETUP_REG_OFFSET,
                 {
                     {USBDEV_RXENABLE_SETUP_SETUP_8_BIT, 1},
                     {USBDEV_RXENABLE_SETUP_SETUP_9_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_usbdev_endpoint_setup_enable(&usbdev_, /*endpoint=*/10,
                                                 kDifToggleDisabled));

  EXPECT_READ32(USBDEV_RXENABLE_OUT_REG_OFFSET,
                {
                    {USBDEV_RXENABLE_OUT_OUT_OFFSET, 0x205},
                });
  EXPECT_WRITE32(USBDEV_RXENABLE_OUT_REG_OFFSET,
                 {
                     {USBDEV_RXENABLE_OUT_OUT_OFFSET, 0x225},
                     // Register writes specify '1' in PRESERVE to leave an
                     // endpoint unchanged.
                     {USBDEV_RXENABLE_OUT_PRESERVE_OFFSET, 0xfdf},
                 });
  EXPECT_DIF_OK(dif_usbdev_endpoint_out_enable(&usbdev_, /*endpoint=*/5,
                                               kDifToggleEnabled));

  EXPECT_READ32(USBDEV_RXENABLE_OUT_REG_OFFSET,
                {
                    {USBDEV_RXENABLE_OUT_OUT_OFFSET, 0x8a},
                });
  EXPECT_WRITE32(USBDEV_RXENABLE_OUT_REG_OFFSET,
                 {
                     {USBDEV_RXENABLE_OUT_OUT_OFFSET, 0x82},
                     // Register writes specify '1' in PRESERVE to leave an
                     // endpoint unchanged.
                     {USBDEV_RXENABLE_OUT_PRESERVE_OFFSET, 0xff7},
                 });
  EXPECT_DIF_OK(dif_usbdev_endpoint_out_enable(&usbdev_, /*endpoint=*/3,
                                               kDifToggleDisabled));

  EXPECT_READ32(USBDEV_SET_NAK_OUT_REG_OFFSET,
                {
                    {USBDEV_SET_NAK_OUT_ENABLE_10_BIT, 1},
                });
  EXPECT_WRITE32(USBDEV_SET_NAK_OUT_REG_OFFSET,
                 {
                     {USBDEV_SET_NAK_OUT_ENABLE_9_BIT, 1},
                     {USBDEV_SET_NAK_OUT_ENABLE_10_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_usbdev_endpoint_set_nak_out_enable(&usbdev_, /*endpoint=*/9,
                                                       kDifToggleEnabled));

  EXPECT_READ32(USBDEV_SET_NAK_OUT_REG_OFFSET,
                {
                    {USBDEV_SET_NAK_OUT_ENABLE_8_BIT, 1},
                    {USBDEV_SET_NAK_OUT_ENABLE_9_BIT, 1},
                });
  EXPECT_WRITE32(USBDEV_SET_NAK_OUT_REG_OFFSET,
                 {
                     {USBDEV_SET_NAK_OUT_ENABLE_9_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_usbdev_endpoint_set_nak_out_enable(&usbdev_, /*endpoint=*/8,
                                                       kDifToggleDisabled));
}

TEST_F(UsbdevTest, StallConfig) {
  dif_usbdev_endpoint_id_t endpoint = {
      .number = 1,
      .direction = 1,
  };
  EXPECT_READ32(USBDEV_IN_STALL_REG_OFFSET,
                {
                    {USBDEV_IN_STALL_ENDPOINT_0_BIT, 1},
                });
  EXPECT_WRITE32(USBDEV_IN_STALL_REG_OFFSET,
                 {
                     {USBDEV_IN_STALL_ENDPOINT_0_BIT, 1},
                     {USBDEV_IN_STALL_ENDPOINT_1_BIT, 1},
                 });
  EXPECT_DIF_OK(
      dif_usbdev_endpoint_stall_enable(&usbdev_, endpoint, kDifToggleEnabled));

  endpoint.number = 3;
  endpoint.direction = 0;
  EXPECT_READ32(USBDEV_OUT_STALL_REG_OFFSET,
                {
                    {USBDEV_OUT_STALL_ENDPOINT_5_BIT, 1},
                });
  EXPECT_WRITE32(USBDEV_OUT_STALL_REG_OFFSET,
                 {
                     {USBDEV_OUT_STALL_ENDPOINT_3_BIT, 1},
                     {USBDEV_OUT_STALL_ENDPOINT_5_BIT, 1},
                 });
  EXPECT_DIF_OK(
      dif_usbdev_endpoint_stall_enable(&usbdev_, endpoint, kDifToggleEnabled));

  bool enabled;
  endpoint.number = 5;
  endpoint.direction = 1;
  EXPECT_READ32(USBDEV_IN_STALL_REG_OFFSET,
                {
                    {USBDEV_IN_STALL_ENDPOINT_5_BIT, 1},
                });
  EXPECT_DIF_OK(dif_usbdev_endpoint_stall_get(&usbdev_, endpoint, &enabled));
  EXPECT_TRUE(enabled);

  endpoint.number = 11;
  endpoint.direction = 0;
  EXPECT_READ32(USBDEV_OUT_STALL_REG_OFFSET,
                {
                    {USBDEV_OUT_STALL_ENDPOINT_5_BIT, 1},
                    {USBDEV_OUT_STALL_ENDPOINT_9_BIT, 1},
                    {USBDEV_OUT_STALL_ENDPOINT_10_BIT, 1},
                });
  EXPECT_DIF_OK(dif_usbdev_endpoint_stall_get(&usbdev_, endpoint, &enabled));
  EXPECT_FALSE(enabled);
}

TEST_F(UsbdevTest, OutPacket) {
  // Note: the DIF only strives to ensure that at least 2 SETUP buffers are
  // available, in an effort to prevent buffer exhaustion; the FIFO physically
  // has more entries, as a contingency.
  constexpr uint32_t kMaxAvSetupBuffers = 2u;
  constexpr uint32_t kMaxAvOutBuffers = 8u;
  dif_usbdev_buffer_pool_t buffer_pool;
  dif_usbdev_config_t phy_config = {
      .have_differential_receiver = kDifToggleEnabled,
      .use_tx_d_se0 = kDifToggleDisabled,
      .single_bit_eop = kDifToggleDisabled,
      .pin_flip = kDifToggleDisabled,
      .clock_sync_signals = kDifToggleEnabled,
  };
  EXPECT_WRITE32(USBDEV_PHY_CONFIG_REG_OFFSET,
                 {
                     {USBDEV_PHY_CONFIG_USE_DIFF_RCVR_BIT, 1},
                     {USBDEV_PHY_CONFIG_TX_USE_D_SE0_BIT, 0},
                     {USBDEV_PHY_CONFIG_EOP_SINGLE_BIT_BIT, 0},
                     {USBDEV_PHY_CONFIG_PINFLIP_BIT, 0},
                     {USBDEV_PHY_CONFIG_USB_REF_DISABLE_BIT, 0},
                 });
  EXPECT_DIF_OK(dif_usbdev_configure(&usbdev_, &buffer_pool, phy_config));

  // Add buffers to the AV SETUP FIFO and Av OUT FIFO to receive.
  for (uint32_t i = 0u; i < kMaxAvSetupBuffers + kMaxAvOutBuffers; ++i) {
    uint8_t setup_depth = (i >= kMaxAvSetupBuffers) ? kMaxAvSetupBuffers : i;
    uint8_t out_depth =
        (i >= kMaxAvSetupBuffers) ? (i - kMaxAvSetupBuffers) : 0u;
    int top = buffer_pool.top;
    EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                  {
                      {USBDEV_USBSTAT_FRAME_OFFSET, 10},
                      {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                       USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE},
                      {USBDEV_USBSTAT_SENSE_BIT, 1},
                      {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, out_depth},
                      {USBDEV_USBSTAT_AV_SETUP_DEPTH_OFFSET, setup_depth},
                      {USBDEV_USBSTAT_AV_OUT_FULL_BIT, 0},
                      {USBDEV_USBSTAT_AV_SETUP_FULL_BIT, 0},
                  });
    if (i >= kMaxAvSetupBuffers) {
      EXPECT_WRITE32(
          USBDEV_AVOUTBUFFER_REG_OFFSET,
          {{USBDEV_AVOUTBUFFER_BUFFER_OFFSET, buffer_pool.buffers[top - i]}});
    } else {
      EXPECT_WRITE32(
          USBDEV_AVSETUPBUFFER_REG_OFFSET,
          {{USBDEV_AVSETUPBUFFER_BUFFER_OFFSET, buffer_pool.buffers[top - i]}});
    }
  }
  EXPECT_READ32(
      USBDEV_USBSTAT_REG_OFFSET,
      {
          {USBDEV_USBSTAT_FRAME_OFFSET, 10},
          {USBDEV_USBSTAT_LINK_STATE_OFFSET,
           USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE},
          {USBDEV_USBSTAT_SENSE_BIT, 1},
          {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, kMaxAvOutBuffers},
          {USBDEV_USBSTAT_AV_SETUP_DEPTH_OFFSET, kMaxAvSetupBuffers},
          {USBDEV_USBSTAT_AV_OUT_FULL_BIT, 1},
          {USBDEV_USBSTAT_AV_SETUP_FULL_BIT, 0},  // FIFO is physically larger
      });
  EXPECT_DIF_OK(dif_usbdev_fill_available_fifos(&usbdev_, &buffer_pool));

  // No read data available yet.
  dif_usbdev_rx_packet_info_t rx_packet_info;
  dif_usbdev_buffer_t buffer;
  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_FRAME_OFFSET, 15},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE},
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, kMaxAvOutBuffers},
                    {USBDEV_USBSTAT_AV_SETUP_DEPTH_OFFSET, kMaxAvSetupBuffers},
                    {USBDEV_USBSTAT_AV_OUT_FULL_BIT, 1},
                    {USBDEV_USBSTAT_AV_SETUP_FULL_BIT, 0},
                    {USBDEV_USBSTAT_RX_EMPTY_BIT, 1},
                });
  EXPECT_EQ(dif_usbdev_recv(&usbdev_, &rx_packet_info, &buffer),
            kDifUnavailable);

  // Receive OUT packet all at once.
  uint32_t expected_data[4], recvd_data[4];
  for (size_t i = 0; i < sizeof(expected_data) / sizeof(expected_data[0]);
       i++) {
    expected_data[i] = i * 1023;
  }
  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_FRAME_OFFSET, 15},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE},
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, kMaxAvOutBuffers - 1},
                    {USBDEV_USBSTAT_AV_SETUP_DEPTH_OFFSET, kMaxAvSetupBuffers},
                    {USBDEV_USBSTAT_AV_OUT_FULL_BIT, 0},
                    {USBDEV_USBSTAT_AV_SETUP_FULL_BIT, 0},
                    {USBDEV_USBSTAT_RX_EMPTY_BIT, 0},
                });
  EXPECT_READ32(USBDEV_RXFIFO_REG_OFFSET,
                {
                    {USBDEV_RXFIFO_EP_OFFSET, 1},
                    {USBDEV_RXFIFO_SETUP_BIT, 0},
                    {USBDEV_RXFIFO_SIZE_OFFSET, sizeof(expected_data)},
                    {USBDEV_RXFIFO_BUFFER_OFFSET, 0},
                });
  EXPECT_DIF_OK(dif_usbdev_recv(&usbdev_, &rx_packet_info, &buffer));
  EXPECT_EQ(rx_packet_info.endpoint, 1);
  EXPECT_EQ(rx_packet_info.length, sizeof(expected_data));
  EXPECT_FALSE(rx_packet_info.is_setup);
  EXPECT_EQ(buffer.id, 0);
  EXPECT_EQ(buffer.offset, 0);
  EXPECT_EQ(buffer.remaining_bytes, sizeof(expected_data));
  EXPECT_EQ(buffer.type, kDifUsbdevBufferTypeRead);

  size_t bytes_written;
  for (size_t i = 0; i < sizeof(expected_data) / sizeof(expected_data[0]);
       i++) {
    EXPECT_READ32(USBDEV_BUFFER_REG_OFFSET + buffer.id * 64 + 4 * i,
                  expected_data[i]);
  }
  EXPECT_DIF_OK(dif_usbdev_buffer_read(&usbdev_, &buffer_pool, &buffer,
                                       reinterpret_cast<uint8_t *>(recvd_data),
                                       sizeof(recvd_data), &bytes_written));
  EXPECT_EQ(bytes_written, sizeof(recvd_data));
  EXPECT_EQ(memcmp(expected_data, recvd_data, sizeof(expected_data)), 0);

  // One more received packet to test other offsets and the Av SETUP Buffer FIFO
  EXPECT_READ32(
      USBDEV_USBSTAT_REG_OFFSET,
      {
          {USBDEV_USBSTAT_FRAME_OFFSET, 25},
          {USBDEV_USBSTAT_LINK_STATE_OFFSET,
           USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE},
          {USBDEV_USBSTAT_SENSE_BIT, 1},
          {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, kMaxAvOutBuffers - 1},
          {USBDEV_USBSTAT_AV_SETUP_DEPTH_OFFSET, kMaxAvSetupBuffers - 1},
          {USBDEV_USBSTAT_AV_OUT_FULL_BIT, 0},
          {USBDEV_USBSTAT_AV_SETUP_FULL_BIT, 0},
          {USBDEV_USBSTAT_RX_EMPTY_BIT, 0},
      });
  EXPECT_READ32(USBDEV_RXFIFO_REG_OFFSET,
                {
                    {USBDEV_RXFIFO_EP_OFFSET, 0},
                    {USBDEV_RXFIFO_SETUP_BIT, 1},  // SETUP packet this time
                    {USBDEV_RXFIFO_SIZE_OFFSET, sizeof(expected_data) - 1},
                    {USBDEV_RXFIFO_BUFFER_OFFSET, 1},
                });
  EXPECT_DIF_OK(dif_usbdev_recv(&usbdev_, &rx_packet_info, &buffer));
  EXPECT_EQ(rx_packet_info.endpoint, 0);
  EXPECT_EQ(rx_packet_info.length, sizeof(expected_data) - 1);
  EXPECT_TRUE(rx_packet_info.is_setup);
  EXPECT_EQ(buffer.id, 1);
  EXPECT_EQ(buffer.offset, 0);
  EXPECT_EQ(buffer.remaining_bytes, sizeof(expected_data) - 1);
  EXPECT_EQ(buffer.type, kDifUsbdevBufferTypeRead);

  memset(recvd_data, 0, sizeof(recvd_data));
  for (size_t i = 0; i < sizeof(expected_data) / sizeof(expected_data[0]);
       i++) {
    EXPECT_READ32(USBDEV_BUFFER_REG_OFFSET + buffer.id * 64 + 4 * i,
                  expected_data[i]);
  }
  EXPECT_DIF_OK(dif_usbdev_buffer_read(&usbdev_, &buffer_pool, &buffer,
                                       reinterpret_cast<uint8_t *>(recvd_data),
                                       4, &bytes_written));
  EXPECT_EQ(bytes_written, 4);
  EXPECT_DIF_OK(dif_usbdev_buffer_read(
      &usbdev_, &buffer_pool, &buffer,
      reinterpret_cast<uint8_t *>(recvd_data) + bytes_written,
      sizeof(recvd_data) - bytes_written, &bytes_written));
  EXPECT_EQ(bytes_written, sizeof(recvd_data) - 4 - 1);
  EXPECT_EQ(memcmp(expected_data, recvd_data, sizeof(expected_data)), 0);
}

TEST_F(UsbdevTest, InPacket) {
  dif_usbdev_buffer_pool_t buffer_pool;
  dif_usbdev_config_t phy_config = {
      .have_differential_receiver = kDifToggleEnabled,
      .use_tx_d_se0 = kDifToggleDisabled,
      .single_bit_eop = kDifToggleDisabled,
      .pin_flip = kDifToggleDisabled,
      .clock_sync_signals = kDifToggleEnabled,
  };
  EXPECT_WRITE32(USBDEV_PHY_CONFIG_REG_OFFSET,
                 {
                     {USBDEV_PHY_CONFIG_USE_DIFF_RCVR_BIT, 1},
                     {USBDEV_PHY_CONFIG_TX_USE_D_SE0_BIT, 0},
                     {USBDEV_PHY_CONFIG_EOP_SINGLE_BIT_BIT, 0},
                     {USBDEV_PHY_CONFIG_PINFLIP_BIT, 0},
                     {USBDEV_PHY_CONFIG_USB_REF_DISABLE_BIT, 0},
                 });
  EXPECT_DIF_OK(dif_usbdev_configure(&usbdev_, &buffer_pool, phy_config));

  dif_usbdev_buffer_t buffer;
  EXPECT_DIF_OK(dif_usbdev_buffer_request(&usbdev_, &buffer_pool, &buffer));
  EXPECT_EQ(buffer.type, kDifUsbdevBufferTypeWrite);

  uint32_t data[16];
  uint8_t *bytes = reinterpret_cast<uint8_t *>(data);
  size_t bytes_written;
  EXPECT_DIF_OK(dif_usbdev_buffer_return(&usbdev_, &buffer_pool, &buffer));
  EXPECT_EQ(buffer.type, kDifUsbdevBufferTypeStale);
  // Can't return a stale buffer.
  EXPECT_DIF_BADARG(dif_usbdev_buffer_return(&usbdev_, &buffer_pool, &buffer));
  // Can't submit a stale buffer.
  EXPECT_DIF_BADARG(dif_usbdev_buffer_write(&usbdev_, &buffer, bytes,
                                            sizeof(data), &bytes_written));

  // Request the buffer.
  EXPECT_DIF_OK(dif_usbdev_buffer_request(&usbdev_, &buffer_pool, &buffer));
  for (size_t i = 0; i < sizeof(data); i++) {
    bytes[i] = i;
    if (i % 4 == 3) {
      EXPECT_WRITE32(USBDEV_BUFFER_REG_OFFSET + buffer.id * 64 + i - 3,
                     data[i / 4]);
    }
  }
  EXPECT_DIF_OK(dif_usbdev_buffer_write(&usbdev_, &buffer, bytes, sizeof(data),
                                        &bytes_written));
  EXPECT_EQ(bytes_written, sizeof(data));

  // Queue up the buffer for transmission.
  EXPECT_WRITE32(USBDEV_CONFIGIN_5_REG_OFFSET,
                 {
                     {USBDEV_CONFIGIN_5_BUFFER_5_OFFSET, buffer.id},
                     {USBDEV_CONFIGIN_5_SIZE_5_OFFSET, bytes_written},
                 });
  EXPECT_WRITE32(USBDEV_CONFIGIN_5_REG_OFFSET,
                 {
                     {USBDEV_CONFIGIN_5_BUFFER_5_OFFSET, buffer.id},
                     {USBDEV_CONFIGIN_5_SIZE_5_OFFSET, bytes_written},
                     {USBDEV_CONFIGIN_5_RDY_5_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_usbdev_send(&usbdev_, /*endpoint=*/5, &buffer));

  // Get TX status for a buffer with a transmission that had to be canceled. The
  // buffer is returned to the free pool.
  dif_usbdev_tx_status_t tx_status;
  EXPECT_READ32(USBDEV_CONFIGIN_0_REG_OFFSET,
                {
                    {USBDEV_CONFIGIN_0_BUFFER_0_OFFSET, buffer.id},
                    {USBDEV_CONFIGIN_0_SIZE_0_OFFSET, sizeof(data)},
                    {USBDEV_CONFIGIN_0_RDY_0_BIT, 0},
                    {USBDEV_CONFIGIN_0_PEND_0_BIT, 1},
                });
  EXPECT_READ32(USBDEV_IN_SENT_REG_OFFSET, {
                                               {USBDEV_IN_SENT_SENT_0_BIT, 0},
                                           });
  EXPECT_DIF_OK(dif_usbdev_get_tx_status(&usbdev_, /*endpoint=*/0, &tx_status));
  EXPECT_EQ(tx_status, kDifUsbdevTxStatusCancelled);
  EXPECT_READ32(USBDEV_CONFIGIN_0_REG_OFFSET,
                {
                    {USBDEV_CONFIGIN_0_BUFFER_0_OFFSET, buffer.id},
                    {USBDEV_CONFIGIN_0_SIZE_0_OFFSET, sizeof(data)},
                    {USBDEV_CONFIGIN_0_RDY_0_BIT, 0},
                    {USBDEV_CONFIGIN_0_PEND_0_BIT, 1},
                });
  EXPECT_WRITE32(USBDEV_CONFIGIN_0_REG_OFFSET,
                 {{USBDEV_CONFIGIN_0_PEND_0_BIT, 1}});
  EXPECT_WRITE32(USBDEV_IN_SENT_REG_OFFSET, {{USBDEV_IN_SENT_SENT_0_BIT, 1}});
  EXPECT_DIF_OK(
      dif_usbdev_clear_tx_status(&usbdev_, &buffer_pool, /*endpoint=*/0));

  // Request a new buffer.
  EXPECT_DIF_OK(dif_usbdev_buffer_request(&usbdev_, &buffer_pool, &buffer));
  for (size_t i = 0; i < sizeof(data); i++) {
    bytes[i] = i;
    if (i % 4 == 3) {
      EXPECT_WRITE32(USBDEV_BUFFER_REG_OFFSET + buffer.id * 64 + i - 3,
                     data[i / 4]);
    }
  }
  EXPECT_DIF_OK(dif_usbdev_buffer_write(&usbdev_, &buffer, bytes, sizeof(data),
                                        &bytes_written));

  // Queue the buffer for transmission.
  EXPECT_WRITE32(USBDEV_CONFIGIN_4_REG_OFFSET,
                 {
                     {USBDEV_CONFIGIN_4_BUFFER_4_OFFSET, buffer.id},
                     {USBDEV_CONFIGIN_4_SIZE_4_OFFSET, sizeof(data)},
                 });
  EXPECT_WRITE32(USBDEV_CONFIGIN_4_REG_OFFSET,
                 {
                     {USBDEV_CONFIGIN_4_BUFFER_4_OFFSET, buffer.id},
                     {USBDEV_CONFIGIN_4_SIZE_4_OFFSET, sizeof(data)},
                     {USBDEV_CONFIGIN_4_RDY_4_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_usbdev_send(&usbdev_, /*endpoint=*/4, &buffer));

  // Get status of an endpoint without a buffer queued for transmission.
  EXPECT_READ32(USBDEV_CONFIGIN_7_REG_OFFSET,
                {
                    {USBDEV_CONFIGIN_7_BUFFER_7_OFFSET, buffer.id},
                    {USBDEV_CONFIGIN_7_SIZE_7_OFFSET, sizeof(data)},
                    {USBDEV_CONFIGIN_7_RDY_7_BIT, 0},
                });
  EXPECT_READ32(USBDEV_IN_SENT_REG_OFFSET, {
                                               {USBDEV_IN_SENT_SENT_7_BIT, 0},
                                           });
  EXPECT_DIF_OK(dif_usbdev_get_tx_status(&usbdev_, /*endpoint=*/7, &tx_status));
  EXPECT_EQ(tx_status, kDifUsbdevTxStatusNoPacket);

  // Get TX status for a queued, but not sent buffer.
  EXPECT_READ32(USBDEV_CONFIGIN_8_REG_OFFSET,
                {
                    {USBDEV_CONFIGIN_8_BUFFER_8_OFFSET, buffer.id},
                    {USBDEV_CONFIGIN_8_SIZE_8_OFFSET, sizeof(data)},
                    {USBDEV_CONFIGIN_8_RDY_8_BIT, 1},
                });
  EXPECT_DIF_OK(dif_usbdev_get_tx_status(&usbdev_, /*endpoint=*/8, &tx_status));
  EXPECT_EQ(tx_status, kDifUsbdevTxStatusPending);

  // Buffer was transmitted successfully.
  uint16_t endpoints_done;
  EXPECT_READ32(USBDEV_IN_SENT_REG_OFFSET, {
                                               {USBDEV_IN_SENT_SENT_3_BIT, 1},
                                               {USBDEV_IN_SENT_SENT_5_BIT, 1},
                                           });
  EXPECT_DIF_OK(dif_usbdev_get_tx_sent(&usbdev_, &endpoints_done));
  EXPECT_EQ(endpoints_done, (1u << 3) | (1u << 5));

  EXPECT_READ32(USBDEV_CONFIGIN_5_REG_OFFSET,
                {
                    {USBDEV_CONFIGIN_5_BUFFER_5_OFFSET, buffer.id},
                    {USBDEV_CONFIGIN_5_SIZE_5_OFFSET, sizeof(data)},
                    {USBDEV_CONFIGIN_5_RDY_5_BIT, 0},
                });
  EXPECT_READ32(USBDEV_IN_SENT_REG_OFFSET, {
                                               {USBDEV_IN_SENT_SENT_3_BIT, 1},
                                               {USBDEV_IN_SENT_SENT_5_BIT, 1},
                                           });
  EXPECT_DIF_OK(dif_usbdev_get_tx_status(&usbdev_, /*endpoint=*/5, &tx_status));
  EXPECT_EQ(tx_status, kDifUsbdevTxStatusSent);
  EXPECT_EQ(buffer.type, kDifUsbdevBufferTypeStale);

  EXPECT_READ32(USBDEV_CONFIGIN_5_REG_OFFSET,
                {
                    {USBDEV_CONFIGIN_5_BUFFER_5_OFFSET, buffer.id},
                    {USBDEV_CONFIGIN_5_SIZE_5_OFFSET, sizeof(data)},
                    {USBDEV_CONFIGIN_5_RDY_5_BIT, 0},
                });
  EXPECT_WRITE32(USBDEV_CONFIGIN_5_REG_OFFSET,
                 {{USBDEV_CONFIGIN_5_PEND_5_BIT, 1}});
  EXPECT_WRITE32(USBDEV_IN_SENT_REG_OFFSET, {{USBDEV_IN_SENT_SENT_5_BIT, 1}});
  EXPECT_DIF_OK(
      dif_usbdev_clear_tx_status(&usbdev_, &buffer_pool, /*endpoint=*/5));
}

TEST_F(UsbdevTest, DeviceAddresses) {
  uint8_t address = 101;
  EXPECT_READ32(USBDEV_USBCTRL_REG_OFFSET,
                {
                    {USBDEV_USBCTRL_ENABLE_BIT, 1},
                    {USBDEV_USBCTRL_DEVICE_ADDRESS_OFFSET, 0},
                });
  EXPECT_WRITE32(USBDEV_USBCTRL_REG_OFFSET,
                 {
                     {USBDEV_USBCTRL_ENABLE_BIT, 1},
                     {USBDEV_USBCTRL_DEVICE_ADDRESS_OFFSET, address},
                 });
  EXPECT_DIF_OK(dif_usbdev_address_set(&usbdev_, address));

  EXPECT_READ32(USBDEV_USBCTRL_REG_OFFSET,
                {
                    {USBDEV_USBCTRL_ENABLE_BIT, 1},
                    {USBDEV_USBCTRL_DEVICE_ADDRESS_OFFSET, 58},
                });
  EXPECT_DIF_OK(dif_usbdev_address_get(&usbdev_, &address));
  EXPECT_EQ(address, 58);
}

TEST_F(UsbdevTest, Status) {
  // dif_usbdev_clear_data_toggle compatibility with earlier implementations
  EXPECT_WRITE32(USBDEV_OUT_DATA_TOGGLE_REG_OFFSET,
                 {
                     {USBDEV_OUT_DATA_TOGGLE_STATUS_OFFSET, 0u},
                     {USBDEV_OUT_DATA_TOGGLE_MASK_OFFSET, 1u << 3},
                 });
  EXPECT_WRITE32(USBDEV_IN_DATA_TOGGLE_REG_OFFSET,
                 {
                     {USBDEV_IN_DATA_TOGGLE_STATUS_OFFSET, 0u},
                     {USBDEV_IN_DATA_TOGGLE_MASK_OFFSET, 1u << 3},
                 });
  EXPECT_DIF_OK(dif_usbdev_clear_data_toggle(&usbdev_, /*endpoint=*/3));
  EXPECT_WRITE32(USBDEV_OUT_DATA_TOGGLE_REG_OFFSET,
                 {
                     {USBDEV_OUT_DATA_TOGGLE_STATUS_OFFSET, 0u},
                     {USBDEV_OUT_DATA_TOGGLE_MASK_OFFSET, 1u << 9},
                 });
  EXPECT_WRITE32(USBDEV_IN_DATA_TOGGLE_REG_OFFSET,
                 {
                     {USBDEV_IN_DATA_TOGGLE_STATUS_OFFSET, 0u},
                     {USBDEV_IN_DATA_TOGGLE_MASK_OFFSET, 1u << 9},
                 });
  EXPECT_DIF_OK(dif_usbdev_clear_data_toggle(&usbdev_, /*endpoint=*/9));
  // Setting of all data toggles to known values; eg. restoring after Deep Sleep
  const uint16_t all_endpoints = (1u << USBDEV_NUM_ENDPOINTS) - 1u;
  const uint16_t even_endpoints = (0x40000000u / 3) & all_endpoints;
  const uint16_t odd_endpoints = even_endpoints << 1;
  EXPECT_WRITE32(USBDEV_OUT_DATA_TOGGLE_REG_OFFSET,
                 {
                     {USBDEV_OUT_DATA_TOGGLE_STATUS_OFFSET, even_endpoints},
                     {USBDEV_OUT_DATA_TOGGLE_MASK_OFFSET, all_endpoints},
                 });
  EXPECT_DIF_OK(dif_usbdev_data_toggle_out_write(&usbdev_, all_endpoints,
                                                 even_endpoints));
  EXPECT_WRITE32(USBDEV_IN_DATA_TOGGLE_REG_OFFSET,
                 {
                     {USBDEV_IN_DATA_TOGGLE_STATUS_OFFSET, odd_endpoints},
                     {USBDEV_IN_DATA_TOGGLE_MASK_OFFSET, all_endpoints},
                 });
  EXPECT_DIF_OK(
      dif_usbdev_data_toggle_in_write(&usbdev_, all_endpoints, odd_endpoints));
  // Saving of data toggles; eg. capturing at entry to Deep Sleep
  uint16_t out_toggles;
  EXPECT_READ32(USBDEV_OUT_DATA_TOGGLE_REG_OFFSET,
                {
                    {USBDEV_OUT_DATA_TOGGLE_STATUS_OFFSET, odd_endpoints},
                    {USBDEV_OUT_DATA_TOGGLE_MASK_OFFSET, 0u},  // Reads as zero
                });
  EXPECT_DIF_OK(dif_usbdev_data_toggle_out_read(&usbdev_, &out_toggles));
  EXPECT_EQ(out_toggles, odd_endpoints);
  uint16_t in_toggles;
  EXPECT_READ32(USBDEV_IN_DATA_TOGGLE_REG_OFFSET,
                {
                    {USBDEV_IN_DATA_TOGGLE_STATUS_OFFSET, even_endpoints},
                    {USBDEV_OUT_DATA_TOGGLE_MASK_OFFSET, 0u},  // Reads as zero
                });
  EXPECT_DIF_OK(dif_usbdev_data_toggle_in_read(&usbdev_, &in_toggles));
  EXPECT_EQ(in_toggles, even_endpoints);

  uint16_t frame;
  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_FRAME_OFFSET, 92},
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE},
                    {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, 2},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_frame(&usbdev_, &frame));
  EXPECT_EQ(frame, 92);

  bool host_lost;
  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_FRAME_OFFSET, 18},
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE_NOSOF},
                    {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, 2},
                    {USBDEV_USBSTAT_HOST_LOST_BIT, 1},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_host_lost(&usbdev_, &host_lost));
  EXPECT_TRUE(host_lost);
  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_FRAME_OFFSET, 18},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE_NOSOF},
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, 2},
                    {USBDEV_USBSTAT_HOST_LOST_BIT, 0},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_host_lost(&usbdev_, &host_lost));
  EXPECT_FALSE(host_lost);

  bool vbus_sense;
  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_FRAME_OFFSET, 31},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE_NOSOF},
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_sense(&usbdev_, &vbus_sense));
  EXPECT_TRUE(vbus_sense);

  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_FRAME_OFFSET, 31},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_DISCONNECTED},
                    {USBDEV_USBSTAT_SENSE_BIT, 0},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_sense(&usbdev_, &vbus_sense));
  EXPECT_FALSE(vbus_sense);

  uint8_t av_setup_fifo_depth;
  uint8_t av_out_fifo_depth;
  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_FRAME_OFFSET, 11},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE},
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, 3},
                    {USBDEV_USBSTAT_RX_EMPTY_BIT, 1},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_available_fifo_depths(
      &usbdev_, &av_setup_fifo_depth, &av_out_fifo_depth));
  EXPECT_EQ(av_out_fifo_depth, 3);

  bool av_setup_fifo_full;
  bool av_out_fifo_full;
  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_FRAME_OFFSET, 12},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE},
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, 4},
                    {USBDEV_USBSTAT_AV_OUT_FULL_BIT, 1},
                    {USBDEV_USBSTAT_RX_EMPTY_BIT, 1},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_available_fifo_full(
      &usbdev_, &av_setup_fifo_full, &av_out_fifo_full));
  EXPECT_TRUE(av_out_fifo_full);

  uint8_t rx_fifo_depth;
  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_FRAME_OFFSET, 12},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE},
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, 4},
                    {USBDEV_USBSTAT_AV_OUT_FULL_BIT, 1},
                    {USBDEV_USBSTAT_RX_EMPTY_BIT, 0},
                    {USBDEV_USBSTAT_RX_DEPTH_OFFSET, 2},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_rx_fifo_depth(&usbdev_, &rx_fifo_depth));
  EXPECT_EQ(rx_fifo_depth, 2);

  bool rx_fifo_empty;
  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_FRAME_OFFSET, 12},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE},
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, 4},
                    {USBDEV_USBSTAT_AV_OUT_FULL_BIT, 1},
                    {USBDEV_USBSTAT_RX_EMPTY_BIT, 1},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_rx_fifo_empty(&usbdev_, &rx_fifo_empty));
  EXPECT_TRUE(rx_fifo_empty);
}

TEST_F(UsbdevTest, LinkState) {
  dif_usbdev_link_state_t link_state;
  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_FRAME_OFFSET, 27},
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE},
                    {USBDEV_USBSTAT_AV_OUT_DEPTH_OFFSET, 2},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_link_state(&usbdev_, &link_state));
  EXPECT_EQ(link_state, kDifUsbdevLinkStateActive);

  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_DISCONNECTED},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_link_state(&usbdev_, &link_state));
  EXPECT_EQ(link_state, kDifUsbdevLinkStateDisconnected);

  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_POWERED},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_link_state(&usbdev_, &link_state));
  EXPECT_EQ(link_state, kDifUsbdevLinkStatePowered);

  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_POWERED_SUSPENDED},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_link_state(&usbdev_, &link_state));
  EXPECT_EQ(link_state, kDifUsbdevLinkStatePoweredSuspended);

  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_SUSPENDED},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_link_state(&usbdev_, &link_state));
  EXPECT_EQ(link_state, kDifUsbdevLinkStateSuspended);

  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_ACTIVE_NOSOF},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_link_state(&usbdev_, &link_state));
  EXPECT_EQ(link_state, kDifUsbdevLinkStateActiveNoSof);

  EXPECT_READ32(USBDEV_USBSTAT_REG_OFFSET,
                {
                    {USBDEV_USBSTAT_SENSE_BIT, 1},
                    {USBDEV_USBSTAT_LINK_STATE_OFFSET,
                     USBDEV_USBSTAT_LINK_STATE_VALUE_RESUMING},
                });
  EXPECT_DIF_OK(dif_usbdev_status_get_link_state(&usbdev_, &link_state));
  EXPECT_EQ(link_state, kDifUsbdevLinkStateResuming);
}

TEST_F(UsbdevTest, WakeFromSleep) {
  EXPECT_WRITE32(USBDEV_WAKE_CONTROL_REG_OFFSET,
                 {{USBDEV_WAKE_CONTROL_SUSPEND_REQ_BIT, 1}});
  EXPECT_DIF_OK(dif_usbdev_set_wake_enable(&usbdev_, kDifToggleEnabled));

  dif_usbdev_wake_status_t wake_status;
  EXPECT_READ32(USBDEV_WAKE_EVENTS_REG_OFFSET,
                {
                    {USBDEV_WAKE_EVENTS_MODULE_ACTIVE_BIT, 1},
                    {USBDEV_WAKE_EVENTS_DISCONNECTED_BIT, 0},
                    {USBDEV_WAKE_EVENTS_BUS_RESET_BIT, 1},
                });
  EXPECT_DIF_OK(dif_usbdev_get_wake_status(&usbdev_, &wake_status));
  EXPECT_TRUE(wake_status.active);
  EXPECT_FALSE(wake_status.disconnected);
  EXPECT_TRUE(wake_status.bus_reset);

  EXPECT_READ32(USBDEV_USBCTRL_REG_OFFSET,
                {
                    {USBDEV_USBCTRL_ENABLE_BIT, 1},
                    {USBDEV_USBCTRL_DEVICE_ADDRESS_OFFSET, 88},
                    {USBDEV_USBCTRL_RESUME_LINK_ACTIVE_BIT, 0},
                });
  EXPECT_WRITE32(USBDEV_USBCTRL_REG_OFFSET,
                 {
                     {USBDEV_USBCTRL_ENABLE_BIT, 1},
                     {USBDEV_USBCTRL_DEVICE_ADDRESS_OFFSET, 88},
                     {USBDEV_USBCTRL_RESUME_LINK_ACTIVE_BIT, 1},
                 });
  EXPECT_DIF_OK(dif_usbdev_resume_link_to_active(&usbdev_));

  EXPECT_WRITE32(USBDEV_WAKE_CONTROL_REG_OFFSET,
                 {{USBDEV_WAKE_CONTROL_WAKE_ACK_BIT, 1}});
  EXPECT_DIF_OK(dif_usbdev_set_wake_enable(&usbdev_, kDifToggleDisabled));
}

}  // namespace
}  // namespace dif_usbdev_unittest
