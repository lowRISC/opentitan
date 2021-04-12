// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/uart.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "uart_regs.h"  // Generated.

namespace uart_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Each;
using testing::Eq;
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

  uart_t uart_ = {
      .base_addr = dev().region(),
      .baudrate = 1,
      .clk_freq_hz = 1048576,
  };
};

class InitTest : public UartTest {};

TEST_F(InitTest, NullArgs) {
  // FIXME: add tests with `uart_` misconfigured.
  EXPECT_EQ(uart_init(nullptr), kErrorUartInvalidArgument);
}

TEST_F(InitTest, Initialize) {
  ExpectDeviceReset();

  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_TX_BIT, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  EXPECT_EQ(uart_init(&uart_), kErrorOk);
}

class BytesSendTest : public UartTest {
 protected:
  /**
   * Sets TX bytes expectations.
   *
   * Every sent byte by the "send bytes" routine is expected to result in the
   * STATUS read of 0 (FIFO not full), and write to WDATA.
   */
  void ExpectSendBytes(int num_elements = kBytesArray.size()) {
    ASSERT_LE(num_elements, kBytesArray.size());
    for (int i = 0; i < num_elements; ++i) {
      uint32_t value = static_cast<uint32_t>(kBytesArray[i]);
      EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL_BIT, false}});
      EXPECT_WRITE32(UART_WDATA_REG_OFFSET, value);
      EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXIDLE_BIT, true}});
    }
  }
};

TEST_F(BytesSendTest, SendBuffer) {
  ExpectSendBytes();
  // Calling uart_write implicitly tests uart_putchar.
  EXPECT_EQ(uart_write(&uart_, kBytesArray.data(), kBytesArray.size()),
            kBytesArray.size());
}

TEST_F(BytesSendTest, SendByteBusy) {
  // FIFO full for one cycle, then empty.
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL_BIT, true}});
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL_BIT, false}});

  // The value sent is 'X'
  EXPECT_WRITE32(UART_WDATA_REG_OFFSET, 'X');

  // Transmitter busy for one cycle, then idle.
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXIDLE_BIT, false}});
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXIDLE_BIT, true}});

  uart_putchar(&uart_, 'X');
}

}  // namespace
}  // namespace uart_unittest
