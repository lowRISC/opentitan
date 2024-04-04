// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/hexstr.h"

#include <stdint.h>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace {

TEST(HexStr, Encode) {
  uint32_t value = 0x01020304;
  char buf[9];

  status_t result = hexstr_encode(buf, sizeof(buf), &value, sizeof(value));
  EXPECT_TRUE(status_ok(result));
  EXPECT_EQ(std::string(buf), "04030201");
}

TEST(HexStr, EncodeShortBuf) {
  uint32_t value = 0x01020304;
  // Buf is too short - it omits space for the nul terminator.
  char buf[8];

  status_t result = hexstr_encode(buf, sizeof(buf), &value, sizeof(value));
  EXPECT_FALSE(status_ok(result));
}

TEST(HexStr, Decode) {
  char str[] = "11223344";
  uint32_t value = 0;

  status_t result = hexstr_decode(&value, sizeof(value), str);
  EXPECT_TRUE(status_ok(result));
  EXPECT_EQ(value, 0x44332211);
}

TEST(HexStr, DecodeShortBuf) {
  char str[] = "1122334455667788";
  // 32-bit int is too small to hold the decoded value.
  uint32_t value = 0;

  status_t result = hexstr_decode(&value, sizeof(value), str);
  EXPECT_FALSE(status_ok(result));
}

TEST(HexStr, DecodeShortInput) {
  // The input is an odd length.
  char str[] = "1122334";
  uint32_t value = 0;

  status_t result = hexstr_decode(&value, sizeof(value), str);
  EXPECT_FALSE(status_ok(result));
}

TEST(HexStr, DecodeIllegalInput) {
  // The contains in invalid character.
  char str[] = "1122334x";
  uint32_t value = 0;

  status_t result = hexstr_decode(&value, sizeof(value), str);
  EXPECT_FALSE(status_ok(result));
}

}  // namespace
