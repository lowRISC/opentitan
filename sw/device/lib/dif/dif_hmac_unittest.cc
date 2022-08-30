// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_hmac.h"

#include <array>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "hmac_regs.h"  // Generated

namespace dif_hmac_unittest {

using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

// Base class for the rest fixtures in this file.
class HmacTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  dif_hmac_t hmac_;
  dif_hmac_transaction_t transaction_ = {
      .message_endianness = kDifHmacEndiannessLittle,
      .digest_endianness = kDifHmacEndiannessLittle,
  };

  struct ConfigRegister {
    bool hmac_enable = false;
    bool sha_enable = true;
    bool msg_big_endian = false;
    bool digest_big_endian = false;
  } config_reg_;

  HmacTest() { EXPECT_DIF_OK(dif_hmac_init(dev().region(), &hmac_)); }

  void ExpectConfig(void) {
    EXPECT_WRITE32(
        HMAC_CFG_REG_OFFSET,
        {
            {HMAC_CFG_HMAC_EN_BIT, config_reg_.hmac_enable},
            {HMAC_CFG_SHA_EN_BIT, config_reg_.sha_enable},
            {HMAC_CFG_ENDIAN_SWAP_BIT, config_reg_.msg_big_endian},
            {HMAC_CFG_DIGEST_SWAP_BIT, config_reg_.digest_big_endian},
        });
  }

  void ExpectKey(const uint8_t *key, size_t size) {
    for (size_t i = 0; i < size; i += sizeof(uint32_t)) {
      uint32_t word = 0;
      memcpy(&word, &key[i], sizeof(uint32_t));
      EXPECT_WRITE32(HMAC_KEY_7_REG_OFFSET - i, word);
    }
  }
};

class HmacMacTest : public HmacTest {
 protected:
  static constexpr std::array<uint8_t, 32> kKey = {
      0x68, 0x56, 0x6D, 0x59, 0x71, 0x33, 0x74, 0x36, 0x77, 0x39, 0x7A,
      0x24, 0x43, 0x26, 0x46, 0x29, 0x4A, 0x40, 0x4E, 0x63, 0x51, 0x66,
      0x54, 0x6A, 0x57, 0x6E, 0x5A, 0x72, 0x34, 0x75, 0x37, 0x78};
  HmacMacTest() { config_reg_.hmac_enable = true; }

  void SuccessPath() {
    EXPECT_READ32(HMAC_CFG_REG_OFFSET, 0);
    ExpectKey(kKey.data(), kKey.size());
    ExpectConfig();
    EXPECT_READ32(HMAC_CMD_REG_OFFSET, 0);
    EXPECT_WRITE32(HMAC_CMD_REG_OFFSET, {{HMAC_CMD_HASH_START_BIT, true}});

    EXPECT_DIF_OK(dif_hmac_mode_hmac_start(&hmac_, kKey.data(), transaction_));
  }
};
constexpr std::array<uint8_t, 32> HmacMacTest::kKey;

TEST_F(HmacMacTest, StartSuccess) { SuccessPath(); }

TEST_F(HmacMacTest, StartMsgBigEndianSuccess) {
  config_reg_.msg_big_endian = true;
  transaction_.message_endianness = kDifHmacEndiannessBig;

  SuccessPath();
}

TEST_F(HmacMacTest, StartDigestLittleEndianSuccess) {
  config_reg_.digest_big_endian = false;
  transaction_.digest_endianness = kDifHmacEndiannessLittle;

  SuccessPath();
}

TEST_F(HmacMacTest, StartBadArg) {
  EXPECT_DIF_BADARG(
      dif_hmac_mode_hmac_start(nullptr, kKey.data(), transaction_));

  EXPECT_DIF_BADARG(dif_hmac_mode_hmac_start(&hmac_, nullptr, transaction_));
}

TEST_F(HmacMacTest, StartError) {
  transaction_.message_endianness = static_cast<dif_hmac_endianness_t>(2);

  EXPECT_READ32(HMAC_CFG_REG_OFFSET, 0);
  EXPECT_EQ(dif_hmac_mode_hmac_start(&hmac_, kKey.data(), transaction_),
            kDifError);

  EXPECT_READ32(HMAC_CFG_REG_OFFSET, 0);
  transaction_.digest_endianness = static_cast<dif_hmac_endianness_t>(2);
  EXPECT_EQ(dif_hmac_mode_hmac_start(&hmac_, kKey.data(), transaction_),
            kDifError);
}

class HmacSha256Test : public HmacTest {
 protected:
  HmacSha256Test() { config_reg_.sha_enable = true; }
};

TEST_F(HmacSha256Test, StartSuccess) {
  EXPECT_READ32(HMAC_CFG_REG_OFFSET, 0);
  ExpectConfig();
  EXPECT_READ32(HMAC_CMD_REG_OFFSET, 0);
  EXPECT_WRITE32(HMAC_CMD_REG_OFFSET, {{HMAC_CMD_HASH_START_BIT, true}});

  EXPECT_DIF_OK(dif_hmac_mode_sha256_start(&hmac_, transaction_));
}

TEST_F(HmacSha256Test, StartMsgBigEndianSuccess) {
  config_reg_.msg_big_endian = true;
  transaction_.message_endianness = kDifHmacEndiannessBig;

  EXPECT_READ32(HMAC_CFG_REG_OFFSET, 0);
  ExpectConfig();
  EXPECT_READ32(HMAC_CMD_REG_OFFSET, 0);
  EXPECT_WRITE32(HMAC_CMD_REG_OFFSET, {{HMAC_CMD_HASH_START_BIT, true}});

  EXPECT_DIF_OK(dif_hmac_mode_sha256_start(&hmac_, transaction_));
}

TEST_F(HmacSha256Test, StartDigestLittleEndianSuccess) {
  config_reg_.digest_big_endian = false;
  transaction_.digest_endianness = kDifHmacEndiannessLittle;

  EXPECT_READ32(HMAC_CFG_REG_OFFSET, 0);
  ExpectConfig();
  EXPECT_READ32(HMAC_CMD_REG_OFFSET, 0);
  EXPECT_WRITE32(HMAC_CMD_REG_OFFSET, {{HMAC_CMD_HASH_START_BIT, true}});

  EXPECT_DIF_OK(dif_hmac_mode_sha256_start(&hmac_, transaction_));
}

TEST_F(HmacSha256Test, StartBadArg) {
  EXPECT_DIF_BADARG(dif_hmac_mode_sha256_start(nullptr, transaction_));
}

TEST_F(HmacSha256Test, StartError) {
  transaction_.message_endianness = static_cast<dif_hmac_endianness_t>(2);

  EXPECT_READ32(HMAC_CFG_REG_OFFSET, 0);
  EXPECT_EQ(dif_hmac_mode_sha256_start(&hmac_, transaction_), kDifError);

  EXPECT_READ32(HMAC_CFG_REG_OFFSET, 0);
  transaction_.digest_endianness = static_cast<dif_hmac_endianness_t>(2);
  EXPECT_EQ(dif_hmac_mode_sha256_start(&hmac_, transaction_), kDifError);
}

class HmacProcessTest : public HmacTest {
 protected:
  HmacProcessTest() {}
};

TEST_F(HmacProcessTest, StartSuccess) {
  EXPECT_READ32(HMAC_CMD_REG_OFFSET, 0);
  EXPECT_WRITE32(HMAC_CMD_REG_OFFSET, {{HMAC_CMD_HASH_PROCESS_BIT, true}});
  EXPECT_DIF_OK(dif_hmac_process(&hmac_));
}

TEST_F(HmacProcessTest, ProcessBadArg) {
  EXPECT_DIF_BADARG(dif_hmac_process(nullptr));
}

class HmacGetMessageLengthTest : public HmacTest {
 protected:
  HmacGetMessageLengthTest() {}
};

TEST_F(HmacGetMessageLengthTest, RunSuccess) {
  EXPECT_READ32(HMAC_MSG_LENGTH_LOWER_REG_OFFSET, 0xfd257515);
  EXPECT_READ32(HMAC_MSG_LENGTH_UPPER_REG_OFFSET, 0xaf3975bc);
  uint64_t len = 0;
  EXPECT_DIF_OK(dif_hmac_get_message_length(&hmac_, &len));
  EXPECT_EQ(len, 0xaf3975bcfd257515);
}

TEST_F(HmacGetMessageLengthTest, BadArgHmac) {
  uint64_t len = 0;
  EXPECT_DIF_BADARG(dif_hmac_get_message_length(nullptr, &len));
}

TEST_F(HmacGetMessageLengthTest, BadArgLen) {
  EXPECT_DIF_BADARG(dif_hmac_get_message_length(&hmac_, nullptr));
}

}  // namespace dif_hmac_unittest
