// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/dbg_print.h"

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/error.h"

namespace dbg_printf_unittest {
// We don't use a mock here since it'd be overkill; expectations are easier
// to write on a global string, instead. This also produces a simpler error
// message instead of a tower of failed expectations.
static std::string *uart_buf = new std::string;
extern "C" void uart_putchar(uint8_t c) { uart_buf->push_back(c); }

TEST(LogTest, PrintfFormatOnly) {
  uart_buf->clear();
  dbg_printf("A");
  EXPECT_EQ(*uart_buf, "A");

  uart_buf->clear();
  dbg_printf("1234567890\n");
  EXPECT_EQ(*uart_buf, "1234567890\n");
}

TEST(LogTest, PrintfChar) {
  uart_buf->clear();
  dbg_printf("%c", 'A');
  EXPECT_EQ(*uart_buf, "A");
}

TEST(LogTest, PrintfInt) {
  uart_buf->clear();
  dbg_printf("%d", 0);
  EXPECT_EQ(*uart_buf, "0");

  uart_buf->clear();
  dbg_printf("%d", -123);
  EXPECT_EQ(*uart_buf, "-123");

  uart_buf->clear();
  dbg_printf("%d", 12345);
  EXPECT_EQ(*uart_buf, "12345");
}

TEST(LogTest, PrintfUnsignedInt) {
  uart_buf->clear();
  dbg_printf("%u", 0);
  EXPECT_EQ(*uart_buf, "0");

  uart_buf->clear();
  dbg_printf("%u", 0xFFFFFFFF);
  EXPECT_EQ(*uart_buf, "4294967295");

  uart_buf->clear();
  dbg_printf("%u", 12345);
  EXPECT_EQ(*uart_buf, "12345");
}

TEST(LogTest, PrintfHex) {
  uart_buf->clear();
  dbg_printf("%x", 0xabcdef01);
  EXPECT_EQ(*uart_buf, "abcdef01");

  uart_buf->clear();
  dbg_printf("0x%x%x", 0x01020304, 0x05060708);
  EXPECT_EQ(*uart_buf, "0x0102030405060708");
}

TEST(LogTest, PrintfString) {
  uart_buf->clear();
  dbg_printf("Hello, %s!", "World");
  EXPECT_EQ(*uart_buf, "Hello, World!");

  uart_buf->clear();
  dbg_printf("%s%s", "Open", "Titan");
  EXPECT_EQ(*uart_buf, "OpenTitan");

  uart_buf->clear();
  dbg_printf("%s%s%s%s%s", "A", "", "B", "", "C");
  EXPECT_EQ(*uart_buf, "ABC");
}

TEST(LogTest, PrintfMix) {
  uart_buf->clear();
  dbg_printf("%s%x", "OpenTitan", 0x0000000a);
  EXPECT_EQ(*uart_buf, "OpenTitan0000000a");
}

TEST(LogTest, BadFormatSpecifier) {
  // Disable compiler warnings about incorrect format strings so that we can
  // test them (works for both clang and GCC).
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wformat"
#pragma GCC diagnostic ignored "-Wformat-extra-args"
  uart_buf->clear();
  dbg_printf("%z", 0x0000000a);
  EXPECT_EQ(*uart_buf, "%z");

  uart_buf->clear();
  dbg_printf("abcd%");
  EXPECT_EQ(*uart_buf, "abcd%");

  uart_buf->clear();
  dbg_printf("abcd%%");
  EXPECT_EQ(*uart_buf, "abcd%");
#pragma GCC diagnostic pop
}

}  // namespace dbg_printf_unittest
