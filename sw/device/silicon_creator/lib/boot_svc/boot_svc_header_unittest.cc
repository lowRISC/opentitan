// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"

#include <cstring>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

bool operator==(boot_svc_header_t lhs, boot_svc_header_t rhs) {
  return std::memcmp(&lhs, &rhs, sizeof(boot_svc_header_t)) == 0;
}

namespace boot_svc_header_unittest {
namespace {
using ::testing::_;
using ::testing::ElementsAreArray;
using ::testing::SetArgPointee;

class BootSvcHeaderTest : public rom_test::RomTest {
 protected:
  rom_test::MockHmac hmac_;
};

TEST_F(BootSvcHeaderTest, Init) {
  struct BootSvcFakeMsg {
    boot_svc_header_t header{};
    uint32_t payload{0xbeefbeef};
  };
  BootSvcFakeMsg fake_msg;
  constexpr uint32_t kType = 0xcafecafe;
  constexpr uint32_t kDigestAreaByteCount =
      sizeof(fake_msg) - sizeof(fake_msg.header.digest);
  constexpr hmac_digest_t kFakeDigest = {
      0x0b00000e, 0x0b01010e, 0x0b02020e, 0x0b03030e,
      0x0b04040e, 0x0b05050e, 0x0b06060e, 0x0b07070e,
  };

  EXPECT_CALL(hmac_,
              sha256(&fake_msg.header.identifier, kDigestAreaByteCount, _))
      .WillOnce(SetArgPointee<2>(kFakeDigest));

  boot_svc_header_finalize(kType, sizeof(fake_msg), &fake_msg.header);

  EXPECT_THAT(fake_msg.header.digest.digest,
              ElementsAreArray(kFakeDigest.digest));
  EXPECT_EQ(fake_msg.header.identifier, kBootSvcIdentifier);
  EXPECT_EQ(fake_msg.header.type, kType);
  EXPECT_EQ(fake_msg.header.length, sizeof(fake_msg));
}

}  // namespace
}  // namespace boot_svc_header_unittest
