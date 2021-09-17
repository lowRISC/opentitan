// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_UART_UNITTEST_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_UART_UNITTEST_H_

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_uart.h"

#include "uart_regs.h"  // Generated.

namespace dif_uart_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

const std::vector<uint8_t> kBytesArray = {
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a',
    'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l',
    'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v',
};

class UartTest : public Test, public MmioTest {
 protected:
  void ExpectDeviceReset() {
    EXPECT_WRITE32(UART_CTRL_REG_OFFSET, 0);
    EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET,
                   {
                       {UART_FIFO_CTRL_RXRST_BIT, true},
                       {UART_FIFO_CTRL_TXRST_BIT, true},
                   });
    EXPECT_WRITE32(UART_OVRD_REG_OFFSET, 0);
    EXPECT_WRITE32(UART_TIMEOUT_CTRL_REG_OFFSET, 0);
    EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
    EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET,
                   std::numeric_limits<uint32_t>::max());
  }

  dif_uart_t uart_ = {
      .base_addr = dev().region(),
  };

  // NCO is calculated as NCO = 2^20 * fbaud / fpclk, so the following values
  // should result in NCO of 1. This is the default configuration, which will
  // be used unless the values are overridden.
  dif_uart_config_t config_ = {
      .baudrate = 1,
      .clk_freq_hz = 1048576,
      .parity_enable = kDifToggleDisabled,
      .parity = kDifUartParityEven,
  };
};

}  // namespace
}  // namespace dif_uart_unittest

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_UART_UNITTEST_H_
