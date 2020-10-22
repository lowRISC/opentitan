// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// print.h's polyglotness is not part of its public API at the moment; we wrap
// it in an `extern` here for the time being.
extern "C" {
#include "sw/device/lib/runtime/print.h"
}  // extern "C"

#include <stdint.h>

#include <string>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/dif/dif_uart.h"

// NOTE: This is only present so that print.c can link without pulling in
// dif_uart.c.
extern "C" dif_uart_result_t dif_uart_byte_send_polled(const dif_uart *,
                                                       uint8_t) {
  return kDifUartOk;
}

namespace base {
namespace {

using ::testing::StartsWith;

// A test fixture for automatiocally capturing stdout.
class PrintfTest : public testing::Test {
 protected:
  void SetUp() override {
    base_set_stdout({/*data=*/static_cast<void *>(&buf_),
                     /*sink=*/+[](void *data, const char *buf, size_t len) {
                       static_cast<std::string *>(data)->append(buf, len);
                       return len;
                     }});
  }

  std::string buf_;
};

TEST_F(PrintfTest, EmptyFormat) {
  EXPECT_EQ(base_printf(""), 0);
  EXPECT_EQ(buf_, "");
}

TEST_F(PrintfTest, TrivialText) {
  EXPECT_EQ(base_printf("Hello, World!\n"), 14);
  EXPECT_EQ(buf_, "Hello, World!\n");
}

TEST_F(PrintfTest, PartialPrints) {
  EXPECT_EQ(base_printf("Hello, "), 7);
  EXPECT_EQ(buf_, "Hello, ");
  EXPECT_EQ(base_printf("World!\n"), 7);
  EXPECT_EQ(buf_, "Hello, World!\n");
}

TEST_F(PrintfTest, LiteralPct) {
  EXPECT_EQ(base_printf("Hello, %%!\n"), 10);
  EXPECT_EQ(buf_, "Hello, %!\n");
}

TEST_F(PrintfTest, Character) {
  EXPECT_EQ(base_printf("Hello, %c!\n", 'X'), 10);
  EXPECT_EQ(buf_, "Hello, X!\n");
}

TEST_F(PrintfTest, StringWithNul) {
  EXPECT_EQ(base_printf("Hello, %s!\n", "abcxyz"), 15);
  EXPECT_EQ(buf_, "Hello, abcxyz!\n");
}

TEST_F(PrintfTest, StringWithLen) {
  EXPECT_EQ(base_printf("Hello, %z!\n", 6, "abcxyz"), 15);
  EXPECT_EQ(buf_, "Hello, abcxyz!\n");
}

TEST_F(PrintfTest, StringWithLenPrefix) {
  EXPECT_EQ(base_printf("Hello, %z!\n", 3, "abcxyz"), 12);
  EXPECT_EQ(buf_, "Hello, abc!\n");
}

TEST_F(PrintfTest, StringWithLenZeroLen) {
  EXPECT_EQ(base_printf("Hello, %z!\n", 0, "abcxyz"), 9);
  EXPECT_EQ(buf_, "Hello, !\n");
}

TEST_F(PrintfTest, SignedInt) {
  EXPECT_EQ(base_printf("Hello, %i!\n", 42), 11);
  EXPECT_EQ(buf_, "Hello, 42!\n");
}

TEST_F(PrintfTest, SignedIntAlt) {
  EXPECT_EQ(base_printf("Hello, %d!\n", 42), 11);
  EXPECT_EQ(buf_, "Hello, 42!\n");
}

TEST_F(PrintfTest, SignedIntNegative) {
  EXPECT_EQ(base_printf("Hello, %i!\n", -800), 13);
  EXPECT_EQ(buf_, "Hello, -800!\n");
}

TEST_F(PrintfTest, SignedIntWithWidth) {
  EXPECT_EQ(base_printf("Hello, %3i!\n", 42), 12);
  EXPECT_EQ(buf_, "Hello, 042!\n");
}

TEST_F(PrintfTest, SignedIntWithWidthTooShort) {
  EXPECT_EQ(base_printf("Hello, %3i!\n", 9001), 13);
  EXPECT_EQ(buf_, "Hello, 9001!\n");
}

TEST_F(PrintfTest, UnsignedInt) {
  EXPECT_EQ(base_printf("Hello, %u!\n", 42), 11);
  EXPECT_EQ(buf_, "Hello, 42!\n");
}

TEST_F(PrintfTest, UnsignedIntNegative) {
  EXPECT_EQ(base_printf("Hello, %u!\n", -1), 19);
  EXPECT_EQ(buf_, "Hello, 4294967295!\n");
}

TEST_F(PrintfTest, HexFromDec) {
  EXPECT_EQ(base_printf("Hello, %x!\n", 1024), 12);
  EXPECT_EQ(buf_, "Hello, 400!\n");
}

TEST_F(PrintfTest, HexFromDecWithWidth) {
  EXPECT_EQ(base_printf("Hello, %8x!\n", 1024), 17);
  EXPECT_EQ(buf_, "Hello, 00000400!\n");
}

TEST_F(PrintfTest, HexLower) {
  EXPECT_EQ(base_printf("Hello, %x!\n", 0xdead'beef), 17);
  EXPECT_EQ(buf_, "Hello, deadbeef!\n");
}

TEST_F(PrintfTest, HexUpper) {
  EXPECT_EQ(base_printf("Hello, %X!\n", 0xdead'beef), 17);
  EXPECT_EQ(buf_, "Hello, DEADBEEF!\n");
}

TEST_F(PrintfTest, HexNegative) {
  EXPECT_EQ(base_printf("Hello, %x!\n", -1), 17);
  EXPECT_EQ(buf_, "Hello, ffffffff!\n");
}

TEST_F(PrintfTest, HexSvLower) {
  EXPECT_EQ(base_printf("Hello, %h!\n", 0xdead'beef), 17);
  EXPECT_EQ(buf_, "Hello, deadbeef!\n");
}

TEST_F(PrintfTest, HexSvUpper) {
  EXPECT_EQ(base_printf("Hello, %H!\n", 0xdead'beef), 17);
  EXPECT_EQ(buf_, "Hello, DEADBEEF!\n");
}

TEST_F(PrintfTest, Pointer) {
  auto *ptr = reinterpret_cast<uint32_t *>(0x1234);
  base_printf("Hello, %p!\n", ptr);
  switch (sizeof(uintptr_t)) {
    case 4:
      EXPECT_EQ(buf_, "Hello, 0x00001234!\n");
      break;
    case 8:
      EXPECT_EQ(buf_, "Hello, 0x0000000000001234!\n");
      break;
    default:
      FAIL() << "Unknown pointer size";
      break;
  }
}

TEST_F(PrintfTest, NullPtr) {
  base_printf("Hello, %p!\n", nullptr);
  switch (sizeof(uintptr_t)) {
    case 4:
      EXPECT_EQ(buf_, "Hello, 0x00000000!\n");
      break;
    case 8:
      EXPECT_EQ(buf_, "Hello, 0x0000000000000000!\n");
      break;
    default:
      FAIL() << "Unknown pointer size";
      break;
  }
}

TEST_F(PrintfTest, Octal) {
  EXPECT_EQ(base_printf("Hello, %o!\n", 01234567), 16);
  EXPECT_EQ(buf_, "Hello, 1234567!\n");
}

TEST_F(PrintfTest, Binary) {
  EXPECT_EQ(base_printf("Hello, %b!\n", 0b1010'1010), 17);
  EXPECT_EQ(buf_, "Hello, 10101010!\n");
}

TEST_F(PrintfTest, BinaryWithWidth) {
  EXPECT_EQ(base_printf("Hello, %32b!\n", 0b1010'1010), 41);
  EXPECT_EQ(buf_, "Hello, 00000000000000000000000010101010!\n");
}

TEST_F(PrintfTest, IncompleteSpec) {
  base_printf("Hello, %");
  EXPECT_THAT(buf_, StartsWith("Hello, "));
}

TEST_F(PrintfTest, UnknownSpec) {
  base_printf("Hello, %j");
  EXPECT_THAT(buf_, StartsWith("Hello, "));
}

TEST_F(PrintfTest, WidthTooNarrow) {
  base_printf("Hello, %0x");
  EXPECT_THAT(buf_, StartsWith("Hello, "));
}

TEST_F(PrintfTest, WidthTooWide) {
  base_printf("Hello, %9001x");
  EXPECT_THAT(buf_, StartsWith("Hello, "));
}

TEST_F(PrintfTest, ManySpecifiers) {
  base_printf("%d + %d == %d, also spelled 0x%x", 2, 8, 2 + 8, 2 + 8);
  EXPECT_THAT(buf_, StartsWith("2 + 8 == 10, also spelled 0xa"));
}

TEST(SnprintfTest, SimpleWrite) {
  std::string buf(128, '\0');
  auto len = base_snprintf(&buf[0], buf.size(), "Hello, World!\n");
  buf.resize(len);
  EXPECT_EQ(len, 14);
  EXPECT_EQ(buf, "Hello, World!\n");
}

TEST(SnprintfTest, ComplexFormating) {
  std::string buf(128, '\0');
  auto len =
      base_snprintf(&buf[0], buf.size(), "%d + %d == %d, also spelled 0x%x", 2,
                    8, 2 + 8, 2 + 8);
  buf.resize(len);
  EXPECT_EQ(buf, "2 + 8 == 10, also spelled 0xa");
}

TEST(SnprintfTest, PartialWrite) {
  std::string buf(16, '\0');
  auto len =
      base_snprintf(&buf[0], buf.size(), "%d + %d == %d, also spelled 0x%x", 2,
                    8, 2 + 8, 2 + 8);
  buf.resize(len);
  EXPECT_EQ(len, 16);
  EXPECT_EQ(buf, "2 + 8 == 10, als");
}

}  // namespace
}  // namespace base
