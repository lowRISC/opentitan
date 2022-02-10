// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/log.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/testing/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

namespace log_unittest {

namespace internal {
// Create a mock for shutdown functions.
// TODO: move mock UART into its own header file.
class MockUart : public ::global_mock::GlobalMock<MockUart> {
 public:
  MOCK_METHOD(void, UartPutchar, (char));
};
}  // namespace internal

using MockUart = testing::StrictMock<internal::MockUart>;
extern "C" {
void uart_putchar(uint8_t c) { MockUart::Instance().UartPutchar(c); }
}  // extern "C"

class LogTest : public mask_rom_test::MaskRomTest {
 protected:
  void ExpectPrint(const std::string &str) {
    for (char c : str) {
      EXPECT_CALL(uart_, UartPutchar(c));
    }
  }
  MockUart uart_;
};

TEST_F(LogTest, PrintfFormatOnly) {
  ExpectPrint("A");
  EXPECT_EQ(log_printf("A"), kErrorOk);

  ExpectPrint("1234567890\n");
  EXPECT_EQ(log_printf("1234567890\n"), kErrorOk);
}

TEST_F(LogTest, PrintfHex) {
  ExpectPrint("abcdef01");
  EXPECT_EQ(log_printf("%x", 0xabcdef01), kErrorOk);

  ExpectPrint("0x0102030405060708");
  EXPECT_EQ(log_printf("0x%x%x", 0x01020304, 0x05060708), kErrorOk);
}

TEST_F(LogTest, PrintfString) {
  ExpectPrint("Hello, World!");
  EXPECT_EQ(log_printf("Hello, %s!", "World"), kErrorOk);

  ExpectPrint("OpenTitan");
  EXPECT_EQ(log_printf("%s%s", "Open", "Titan"), kErrorOk);

  ExpectPrint("ABC");
  EXPECT_EQ(log_printf("%s%s%s%s%s", "A", "", "B", "", "C"), kErrorOk);
}

TEST_F(LogTest, PrintfMix) {
  ExpectPrint("OpenTitan0000000a");
  EXPECT_EQ(log_printf("%s%x", "OpenTitan", 0x0000000a), kErrorOk);
}

TEST_F(LogTest, BadFormatSpecifier) {
  // Disable compiler warnings about incorrect format strings so that we can
  // test them (works for both clang and GCC).
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wformat"
  EXPECT_EQ(log_printf("%d", 0x0000000a), kErrorLogBadFormatSpecifier);

  ExpectPrint("abcd");
  EXPECT_EQ(log_printf("abcd%"), kErrorLogBadFormatSpecifier);

  ExpectPrint("abcd");
  EXPECT_EQ(log_printf("abcd%%"), kErrorLogBadFormatSpecifier);
#pragma GCC diagnostic pop
}

}  // namespace log_unittest
