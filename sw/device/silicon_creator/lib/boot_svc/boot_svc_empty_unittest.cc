// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_empty.h"

#include <array>
#include <cstring>
#include <numeric>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/boot_svc/mock_boot_svc_header.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

bool operator==(boot_svc_empty_t lhs, boot_svc_empty_t rhs) {
  return std::memcmp(&lhs, &rhs, sizeof(boot_svc_empty_t)) == 0;
}

namespace boot_svc_empty_unittest {
namespace {
using ::testing::ElementsAreArray;
using ::testing::Return;

class BootSvcEmptyTest : public rom_test::RomTest {
 protected:
  rom_test::MockBootSvcHeader boot_svc_header_;
};

TEST_F(BootSvcEmptyTest, Init) {
  std::array<uint32_t, kBootSvcEmptyPayloadWordCount> payload{0};

  boot_svc_empty_t msg{};
  EXPECT_CALL(boot_svc_header_,
              Finalize(kBootSvcEmptyType, sizeof(msg), &msg.header));

  boot_svc_empty_init(&msg);

  EXPECT_THAT(msg.payload, ElementsAreArray(payload));
}

}  // namespace
}  // namespace boot_svc_empty_unittest
