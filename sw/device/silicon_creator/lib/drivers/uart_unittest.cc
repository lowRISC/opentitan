// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/uart.h"

#include <time.h>

#include "gtest/gtest.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "uart_regs.h"  // Generated.

namespace uart_unittest {
namespace {

#if 0
// We supply `ibex_mcycle` and `to_cpu_cycles` because these target-specific
// functions do not exist in the host environment.  Because their purpose is
// to measure time for timeouts, we simply return time in microseconds.

extern "C" {
uint64_t ibex_mcycle() {
  struct timespec tp;
  clock_gettime(CLOCK_MONOTONIC, &tp);
  return tp.tv_sec * 1000000 + tp.tv_nsec / 1000;
}

uint64_t to_cpu_cycles(uint64_t usec) { return usec; }
}  // extern "C"
#endif

const std::vector<uint8_t> kBytesArray = {
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a',
    'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l',
    'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v',
};

class UartTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_UART0_BASE_ADDR;
  rom_test::MockAbsMmio mmio_;

  void ExpectDeviceReset() {
    EXPECT_ABS_WRITE32(base_ + UART_CTRL_REG_OFFSET, 0);
    EXPECT_ABS_WRITE32(base_ + UART_FIFO_CTRL_REG_OFFSET,
                       {
                           {UART_FIFO_CTRL_RXRST_BIT, true},
                           {UART_FIFO_CTRL_TXRST_BIT, true},
                       });
    EXPECT_ABS_WRITE32(base_ + UART_OVRD_REG_OFFSET, 0);
    EXPECT_ABS_WRITE32(base_ + UART_TIMEOUT_CTRL_REG_OFFSET, 0);
    EXPECT_ABS_WRITE32(base_ + UART_INTR_ENABLE_REG_OFFSET, 0);
    EXPECT_ABS_WRITE32(base_ + UART_INTR_STATE_REG_OFFSET,
                       std::numeric_limits<uint32_t>::max());
  }
};

class InitTest : public UartTest {};

TEST_F(InitTest, Initialize) {
  ExpectDeviceReset();

  EXPECT_ABS_WRITE32(base_ + UART_CTRL_REG_OFFSET,
                     {
                         {UART_CTRL_TX_BIT, true},
                         {UART_CTRL_NCO_OFFSET, 1},
                     });
  EXPECT_ABS_WRITE32(base_ + UART_INTR_ENABLE_REG_OFFSET, 0);

  uart_init(1);
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
      EXPECT_ABS_READ32(base_ + UART_STATUS_REG_OFFSET,
                        {{UART_STATUS_TXFULL_BIT, false}});
      EXPECT_ABS_WRITE32(base_ + UART_WDATA_REG_OFFSET, value);
      EXPECT_ABS_READ32(base_ + UART_STATUS_REG_OFFSET,
                        {{UART_STATUS_TXIDLE_BIT, true}});
    }
  }
};

TEST_F(BytesSendTest, SendBuffer) {
  ExpectSendBytes();
  // Calling uart_write implicitly tests uart_putchar.
  uart_write(kBytesArray.data(), kBytesArray.size());
}

TEST_F(BytesSendTest, SendByteBusy) {
  // FIFO full for one cycle, then empty.
  EXPECT_ABS_READ32(base_ + UART_STATUS_REG_OFFSET,
                    {{UART_STATUS_TXFULL_BIT, true}});
  EXPECT_ABS_READ32(base_ + UART_STATUS_REG_OFFSET,
                    {{UART_STATUS_TXFULL_BIT, false}});

  // The value sent is 'X'
  EXPECT_ABS_WRITE32(base_ + UART_WDATA_REG_OFFSET, 'X');

  // Transmitter busy for one cycle, then idle.
  EXPECT_ABS_READ32(base_ + UART_STATUS_REG_OFFSET,
                    {{UART_STATUS_TXIDLE_BIT, false}});
  EXPECT_ABS_READ32(base_ + UART_STATUS_REG_OFFSET,
                    {{UART_STATUS_TXIDLE_BIT, true}});

  uart_putchar('X');
}

TEST_F(UartTest, RecvByte) {
  EXPECT_ABS_READ32(base_ + UART_STATUS_REG_OFFSET,
                    {{UART_STATUS_RXEMPTY_BIT, false}});
  EXPECT_ABS_READ32(base_ + UART_RDATA_REG_OFFSET, 'A');
  int result = uart_getchar(1);
  EXPECT_EQ(result, 'A');
}

TEST_F(UartTest, RecvTimeout) {
  // The uart receive function will keep polling the status register for RX FIFO
  // status.  Return RXEMPTY every time.
  EXPECT_CALL(::rom_test::MockAbsMmio::Instance(),
              Read32(base_ + UART_STATUS_REG_OFFSET))
      .WillRepeatedly(testing::Return(
          mock_mmio::ToInt<uint32_t>({{UART_STATUS_RXEMPTY_BIT, true}})));
  int result = uart_getchar(1);
  EXPECT_EQ(result, -1);
}

TEST_F(UartTest, BreakDetect) {
  // The break detect function will continuously poll the UART value register to
  // observe the sampled value on the RX line.  A break condition over the
  // measured period will always return a value of zero.
  EXPECT_CALL(::rom_test::MockAbsMmio::Instance(),
              Read32(base_ + UART_VAL_REG_OFFSET))
      .WillRepeatedly(testing::Return(mock_mmio::ToInt<uint32_t>(0)));
  hardened_bool_t result = uart_break_detect(1);
  EXPECT_EQ(result, kHardenedBoolTrue);
}

TEST_F(UartTest, NoBreakDetect) {
  // The break detect function will continuously poll the UART value register to
  // observe the sampled value on the RX line.  Any non-zero bit detected on the
  // RX line means we don't have a break condition.
  EXPECT_ABS_READ32(base_ + UART_VAL_REG_OFFSET, 1);
  hardened_bool_t result = uart_break_detect(1);
  EXPECT_EQ(result, kHardenedBoolFalse);
}

}  // namespace
}  // namespace uart_unittest
