// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/hmac.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"

#include "hmac_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace hmac_unittest {
namespace {
using ::testing::ElementsAreArray;

constexpr uint32_t base_ = TOP_EARLGREY_HMAC_BASE_ADDR;
rom_test::MockAbsMmio mmio_;

static void ExpectHalt() {
  EXPECT_ABS_WRITE32(base_ + HMAC_CFG_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(base_ + HMAC_WIPE_SECRET_REG_OFFSET, 0xffffffff);
  EXPECT_ABS_WRITE32(base_ + HMAC_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(base_ + HMAC_INTR_STATE_REG_OFFSET,
                     std::numeric_limits<uint32_t>::max());
}

static void ExpectInit(bool enable_hmac) {
  uint32_t key_len_256 = HMAC_CFG_KEY_LENGTH_VALUE_KEY_256;
  uint32_t digest_256 = HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_256;

  EXPECT_ABS_WRITE32(base_ + HMAC_CFG_REG_OFFSET,
                     {
                         {HMAC_CFG_DIGEST_SWAP_BIT, true},
                         {HMAC_CFG_ENDIAN_SWAP_BIT, false},
                         {HMAC_CFG_SHA_EN_BIT, true},
                         {HMAC_CFG_HMAC_EN_BIT, enable_hmac},
                         {HMAC_CFG_DIGEST_SIZE_OFFSET, digest_256},
                         {HMAC_CFG_KEY_LENGTH_OFFSET, key_len_256},
                     });

  EXPECT_ABS_WRITE32(base_ + HMAC_CMD_REG_OFFSET,
                     {{HMAC_CMD_HASH_START_BIT, true}});
}

static void ExpectShaInit() {
  ExpectHalt();

  ExpectInit(false);
}

static void ExpectHmacInit(const hmac_key_t *key) {
  ExpectHalt();

  static_assert(ARRAYSIZE(key->key) == 8, "Unexpected HMAC key size.");
  EXPECT_ABS_WRITE32(base_ + HMAC_KEY_0_REG_OFFSET, key->key[0]);
  EXPECT_ABS_WRITE32(base_ + HMAC_KEY_1_REG_OFFSET, key->key[1]);
  EXPECT_ABS_WRITE32(base_ + HMAC_KEY_2_REG_OFFSET, key->key[2]);
  EXPECT_ABS_WRITE32(base_ + HMAC_KEY_3_REG_OFFSET, key->key[3]);
  EXPECT_ABS_WRITE32(base_ + HMAC_KEY_4_REG_OFFSET, key->key[4]);
  EXPECT_ABS_WRITE32(base_ + HMAC_KEY_5_REG_OFFSET, key->key[5]);
  EXPECT_ABS_WRITE32(base_ + HMAC_KEY_6_REG_OFFSET, key->key[6]);
  EXPECT_ABS_WRITE32(base_ + HMAC_KEY_7_REG_OFFSET, key->key[7]);

  ExpectInit(true);
}

static void ExpectDigest(const std::array<uint32_t, 8> &digest) {
  // Request a digest
  EXPECT_ABS_WRITE32(base_ + HMAC_CMD_REG_OFFSET,
                     {{HMAC_CMD_HASH_PROCESS_BIT, true}});
  // Poll a couple of times before returning the result
  EXPECT_ABS_READ32(base_ + HMAC_INTR_STATE_REG_OFFSET,
                    {
                        {HMAC_INTR_STATE_HMAC_DONE_BIT, true},
                    });
  EXPECT_ABS_WRITE32(base_ + HMAC_INTR_STATE_REG_OFFSET,
                     {
                         {HMAC_INTR_STATE_HMAC_DONE_BIT, true},
                     });

  // Read the digest.
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_0_REG_OFFSET, digest[0]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_1_REG_OFFSET, digest[1]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_2_REG_OFFSET, digest[2]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_3_REG_OFFSET, digest[3]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_4_REG_OFFSET, digest[4]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_5_REG_OFFSET, digest[5]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_6_REG_OFFSET, digest[6]);
  EXPECT_ABS_READ32(base_ + HMAC_DIGEST_7_REG_OFFSET, digest[7]);

  ExpectHalt();
}

TEST(Hmac, ShaInit) {
  ExpectShaInit();
  hmac_sha_init();
}

TEST(Hmac, HmacInit) {
  hmac_key_t key;
  ExpectHmacInit(&key);
  hmac_hmac_init(&key);
}

TEST(Hmac, SendData) {
  constexpr std::array<uint8_t, 16> kData = {
      0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
      0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
  };

  // Trigger 8bit aligned writes.
  EXPECT_ABS_WRITE8(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x01);
  EXPECT_ABS_WRITE8(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x02);
  hmac_update(&kData[1], 2);

  // Trigger a single 32bit aligned write.
  EXPECT_ABS_WRITE32(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x03020100);
  hmac_update(&kData[0], 4);

  // Trigger 8bit/32bit/8bit sequence.
  EXPECT_ABS_WRITE8(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x02);
  EXPECT_ABS_WRITE8(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x03);
  EXPECT_ABS_WRITE32(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x07060504);
  EXPECT_ABS_WRITE8(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x08);
  EXPECT_ABS_WRITE8(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x09);
  hmac_update(&kData[2], 8);
}

TEST(Hmac, GetDigest) {
  constexpr std::array<uint32_t, 8> kExpectedDigest = {
      0x00000000, 0x11111111, 0x22222222, 0x33333333,
      0x44444444, 0x55555555, 0x66666666, 0x77777777,
  };
  ExpectDigest(kExpectedDigest);

  hmac_digest_t got_digest;
  hmac_final(&got_digest);
  EXPECT_THAT(got_digest.digest, ElementsAreArray(kExpectedDigest));
}

TEST(Hmac, Sha256) {
  constexpr std::array<uint8_t, 8> kData = {0x0d, 0x0c, 0x0b, 0x0a,
                                            0x04, 0x03, 0x02, 0x01};
  constexpr std::array<uint32_t, 8> kExpectedDigest = {
      0x00000000, 0x11111111, 0x22222222, 0x33333333,
      0x44444444, 0x55555555, 0x66666666, 0x77777777,
  };

  ExpectShaInit();
  hmac_sha_init();

  EXPECT_ABS_WRITE32(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x0a0b0c0d);
  EXPECT_ABS_WRITE32(base_ + HMAC_MSG_FIFO_REG_OFFSET, 0x01020304);
  hmac_update(&kData[0], sizeof(kData));

  hmac_digest_t act_digest;
  ExpectDigest(kExpectedDigest);
  hmac_final(&act_digest);

  EXPECT_THAT(act_digest.digest, ElementsAreArray(kExpectedDigest));
}

}  // namespace
}  // namespace hmac_unittest
