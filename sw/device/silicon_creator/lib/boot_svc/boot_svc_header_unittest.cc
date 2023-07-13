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

struct BootSvcTestMsg {
  boot_svc_header_t header;
  uint32_t payload;
};

struct BootSvcHeaderCheckTestCase {
  BootSvcTestMsg msg;
  rom_error_t exp_error;
};

class BootSvcHeaderCheckTest
    : public BootSvcHeaderTest,
      public testing::WithParamInterface<BootSvcHeaderCheckTestCase> {};

constexpr std::array<BootSvcHeaderCheckTestCase, 7> kHeaderCheckTestCases{{
    // A valid message.
    {
        .msg = {.header =
                    {
                        .digest = {},
                        .identifier = kBootSvcIdentifier,
                        .type = 0,
                        .length = sizeof(BootSvcTestMsg),
                    }},
        .exp_error = kErrorOk,
    },
    // Valid message, lower bound of length.
    {
        .msg = {.header =
                    {
                        .digest = {},
                        .identifier = kBootSvcIdentifier,
                        .type = 0,
                        .length = CHIP_BOOT_SVC_MSG_HEADER_SIZE,
                    }},
        .exp_error = kErrorOk,
    },
    // Valid message, upper bound of length.
    {
        .msg = {.header =
                    {
                        .digest = {},
                        .identifier = kBootSvcIdentifier,
                        .type = 0,
                        .length = CHIP_BOOT_SVC_MSG_SIZE_MAX,
                    }},
        .exp_error = kErrorOk,
    },
    // Bad digest.
    {
        .msg = {.header =
                    {
                        .digest = {0x8aadda7a},
                        .identifier = kBootSvcIdentifier,
                        .type = 0,
                        .length = sizeof(BootSvcTestMsg),
                    }},
        .exp_error = kErrorBootSvcBadHeader,
    },
    // Bad identifier.
    {
        .msg = {.header =
                    {
                        .digest = {},
                        .identifier = 0x8aadda7a,
                        .type = 0,
                        .length = sizeof(BootSvcTestMsg),
                    }},
        .exp_error = kErrorBootSvcBadHeader,
    },
    // Bad length (too small).
    {
        .msg = {.header =
                    {
                        .digest = {},
                        .identifier = kBootSvcIdentifier,
                        .type = 0,
                        .length = CHIP_BOOT_SVC_MSG_HEADER_SIZE - 1,
                    }},
        .exp_error = kErrorBootSvcBadHeader,
    },
    // Bad length (too big).
    {
        .msg = {.header =
                    {
                        .digest = {},
                        .identifier = kBootSvcIdentifier,
                        .type = 0,
                        .length = CHIP_BOOT_SVC_MSG_SIZE_MAX + 1,
                    }},
        .exp_error = kErrorBootSvcBadHeader,
    },
}};

TEST_P(BootSvcHeaderCheckTest, Check) {
  // Use an all-zero digest by default.
  EXPECT_CALL(hmac_,
              sha256(&GetParam().msg.header.identifier,
                     GetParam().msg.header.length - sizeof(hmac_digest_t), _))
      .WillOnce(SetArgPointee<2>(hmac_digest_t{}));

  EXPECT_EQ(boot_svc_header_check(&GetParam().msg.header),
            GetParam().exp_error);
}

INSTANTIATE_TEST_SUITE_P(HeaderCheckTestCases, BootSvcHeaderCheckTest,
                         testing::ValuesIn(kHeaderCheckTestCases));

}  // namespace
}  // namespace boot_svc_header_unittest
