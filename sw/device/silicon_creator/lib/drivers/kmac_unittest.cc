// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/kmac.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"  // Generated.

namespace kmac_unittest {
namespace {
using ::testing::ElementsAreArray;

class KmacTest : public rom_test::RomTest {
 protected:
  /**
   * Sets expectations for polling the KMAC block state.
   *
   * @param flag Flag value being polled.
   * @param err Whether to simulate an error.
   */
  void ExpectPollState(uint32_t flag, bool err) {
    // Test assumption: the status flags idle/absorb/squeeze are bits 0..2.
    static_assert(KMAC_STATUS_SHA3_IDLE_BIT < 3);
    static_assert(KMAC_STATUS_SHA3_ABSORB_BIT < 3);
    static_assert(KMAC_STATUS_SHA3_SQUEEZE_BIT < 3);

    // Calculate the status flags that are not this flag.
    uint32_t other_status_flag1 = (flag + 1) % 3;
    uint32_t other_status_flag2 = (flag + 2) % 3;

    // Return wrong statuses and non-error interrupts a few times; expect to
    // keep polling (even with non-error interrupts visible).
    EXPECT_ABS_READ32(base_ + KMAC_INTR_STATE_REG_OFFSET, 0);
    EXPECT_ABS_READ32(base_ + KMAC_STATUS_REG_OFFSET, 0);
    EXPECT_ABS_READ32(base_ + KMAC_INTR_STATE_REG_OFFSET,
                      1 << KMAC_INTR_STATE_KMAC_DONE_BIT);
    EXPECT_ABS_READ32(base_ + KMAC_STATUS_REG_OFFSET, 1 << other_status_flag1);
    EXPECT_ABS_READ32(base_ + KMAC_INTR_STATE_REG_OFFSET,
                      1 << KMAC_INTR_STATE_FIFO_EMPTY_BIT);
    EXPECT_ABS_READ32(base_ + KMAC_STATUS_REG_OFFSET, 1 << other_status_flag2);

    if (err) {
      // Return an error.
      EXPECT_ABS_READ32(base_ + KMAC_INTR_STATE_REG_OFFSET,
                        1 << KMAC_INTR_STATE_KMAC_ERR_BIT);
      EXPECT_ABS_READ32(base_ + KMAC_STATUS_REG_OFFSET, 1 << flag);
    } else {
      // Set the expected flag.
      EXPECT_ABS_READ32(base_ + KMAC_INTR_STATE_REG_OFFSET, 0);
      EXPECT_ABS_READ32(base_ + KMAC_STATUS_REG_OFFSET, 1 << flag);
    }
  }
  /**
   * Sets expectations for issuing a KMAC command.
   *
   * @param cmd Command value to send.
   */
  void ExpectCmdWrite(uint32_t cmd) {
    EXPECT_ABS_WRITE32(base_ + KMAC_CMD_REG_OFFSET, cmd << KMAC_CMD_CMD_OFFSET);
  }
  uint32_t base_ = TOP_EARLGREY_KMAC_BASE_ADDR;
  const size_t shake256_rate_words_ = (1600 - 512) / 32;
  const uint32_t share0_addr_ = base_ + KMAC_STATE_REG_OFFSET;
  const uint32_t share1_addr_ =
      base_ + KMAC_STATE_REG_OFFSET + (KMAC_STATE_SIZE_BYTES / 2);
  rom_test::MockAbsMmio abs_mmio_;
};

class ConfigureTest : public KmacTest {};

TEST_F(ConfigureTest, Success) {
  ExpectPollState(KMAC_STATUS_SHA3_IDLE_BIT, /*err=*/false);

  EXPECT_ABS_WRITE32(base_ + KMAC_ENTROPY_PERIOD_REG_OFFSET,
                     (KMAC_ENTROPY_PERIOD_WAIT_TIMER_MASK
                      << KMAC_ENTROPY_PERIOD_WAIT_TIMER_OFFSET) |
                         (KMAC_ENTROPY_PERIOD_PRESCALER_MASK
                          << KMAC_ENTROPY_PERIOD_PRESCALER_OFFSET));

  // Expected configuration.
  uint32_t cfg =
      (KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256
       << KMAC_CFG_SHADOWED_KSTRENGTH_OFFSET) |
      (KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE << KMAC_CFG_SHADOWED_MODE_OFFSET) |
      (KMAC_CFG_SHADOWED_ENTROPY_MODE_VALUE_SW_MODE
       << KMAC_CFG_SHADOWED_ENTROPY_MODE_OFFSET) |
      (1 << KMAC_CFG_SHADOWED_ENTROPY_READY_BIT);

  EXPECT_ABS_WRITE32_SHADOWED(base_ + KMAC_CFG_SHADOWED_REG_OFFSET, cfg);
  EXPECT_ABS_WRITE32(base_ + KMAC_ENTROPY_SEED_0_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(base_ + KMAC_ENTROPY_SEED_1_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(base_ + KMAC_ENTROPY_SEED_2_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(base_ + KMAC_ENTROPY_SEED_3_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(base_ + KMAC_ENTROPY_SEED_4_REG_OFFSET, 0);

  EXPECT_EQ(kmac_shake256_configure(), kErrorOk);
}

TEST_F(ConfigureTest, Failure) {
  ExpectPollState(KMAC_STATUS_SHA3_IDLE_BIT, /*err=*/true);
  EXPECT_EQ(kmac_shake256_configure(), kErrorKmacInvalidStatus);
}

class StartTest : public KmacTest {};

TEST_F(StartTest, Success) {
  ExpectPollState(KMAC_STATUS_SHA3_IDLE_BIT, /*err=*/false);
  ExpectCmdWrite(KMAC_CMD_CMD_VALUE_START);

  ExpectPollState(KMAC_STATUS_SHA3_ABSORB_BIT, /*err=*/false);
  EXPECT_EQ(kmac_shake256_start(), kErrorOk);
}

TEST_F(StartTest, ErrorBeforeStart) {
  ExpectPollState(KMAC_STATUS_SHA3_IDLE_BIT, /*err=*/true);
  EXPECT_EQ(kmac_shake256_start(), kErrorKmacInvalidStatus);
}

TEST_F(StartTest, ErrorAfterStart) {
  ExpectPollState(KMAC_STATUS_SHA3_IDLE_BIT, /*err=*/false);
  ExpectCmdWrite(KMAC_CMD_CMD_VALUE_START);

  ExpectPollState(KMAC_STATUS_SHA3_ABSORB_BIT, /*err=*/true);
  EXPECT_EQ(kmac_shake256_start(), kErrorKmacInvalidStatus);
}

class AbsorbTest : public KmacTest {};

TEST_F(AbsorbTest, Success) {
  // Test assumption.
  static_assert(2 * sizeof(uint32_t) <= KMAC_STATUS_FIFO_DEPTH_MASK,
                "Message FIFO is too small.");

  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};

  // Expect all test data to be written to the FIFO.
  EXPECT_ABS_WRITE32(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[1]);

  kmac_shake256_absorb((unsigned char *)test_data.data(),
                       test_data.size() * sizeof(uint32_t));
}

TEST_F(AbsorbTest, Empty) { kmac_shake256_absorb(NULL, 0); }

TEST_F(AbsorbTest, ExtraSpace) {
  std::array<uint32_t, 3> test_data = {0x12345678, 0xabcdef01, 0x02030405};

  // Expect all test data to be written to the FIFO.
  EXPECT_ABS_WRITE32(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[1]);
  EXPECT_ABS_WRITE32(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[2]);

  kmac_shake256_absorb((unsigned char *)test_data.data(),
                       test_data.size() * sizeof(uint32_t));
}

TEST_F(AbsorbTest, SmallInput) {
  // Test assumption.
  static_assert(1 * sizeof(uint32_t) <= KMAC_STATUS_FIFO_DEPTH_MASK,
                "Message FIFO is too small.");

  std::array<uint8_t, 2> test_data = {0x78, 0x56};

  // Input should be written to the FIFO in byte-writes (the input is aligned
  // but too small for word writes).
  EXPECT_ABS_WRITE8(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[0]);
  EXPECT_ABS_WRITE8(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[1]);

  kmac_shake256_absorb(test_data.data(), test_data.size());
}

TEST_F(AbsorbTest, UnalignedStart) {
  // Test assumption.
  static_assert(2 * sizeof(uint32_t) <= KMAC_STATUS_FIFO_DEPTH_MASK,
                "Message FIFO is too small.");

  // Create an aligned array, then create an unaligned pointer to the second
  // byte.
  std::array<uint32_t, 2> data_aligned = {0x12345678, 0xabcdef01};
  unsigned char *test_data = (unsigned char *)data_aligned.data() + 1;
  size_t test_data_len = data_aligned.size() * sizeof(uint32_t) - 1;

  // First (unaligned) bytes should use byte-wide writes.
  EXPECT_ABS_WRITE8(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[0]);
  EXPECT_ABS_WRITE8(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[1]);
  EXPECT_ABS_WRITE8(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[2]);
  // Next (aligned) word of input should use a word-wide write.
  EXPECT_ABS_WRITE32(base_ + KMAC_MSG_FIFO_REG_OFFSET, data_aligned[1]);

  kmac_shake256_absorb(test_data, test_data_len);
}

TEST_F(AbsorbTest, UnalignedStartAndEnd) {
  // Test assumption.
  static_assert(3 * sizeof(uint32_t) <= KMAC_STATUS_FIFO_DEPTH_MASK,
                "Message FIFO is too small.");

  // Create an aligned array, then create an unaligned pointer to the third
  // byte. Use a length which excludes the last two bytes.
  std::array<uint32_t, 3> data_aligned = {0x12345678, 0xabcdef01, 0x02030405};
  unsigned char *test_data = (unsigned char *)data_aligned.data() + 2;
  size_t test_data_len = data_aligned.size() * sizeof(uint32_t) - 4;

  // First (unaligned) bytes should use byte-wide writes.
  EXPECT_ABS_WRITE8(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[0]);
  EXPECT_ABS_WRITE8(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[1]);
  // Expect next word of input (now aligned) to use a word-wide write.
  EXPECT_ABS_WRITE32(base_ + KMAC_MSG_FIFO_REG_OFFSET, data_aligned[1]);
  // Last two bytes should use byte-wide writes.
  EXPECT_ABS_WRITE8(base_ + KMAC_MSG_FIFO_REG_OFFSET,
                    test_data[test_data_len - 2]);
  EXPECT_ABS_WRITE8(base_ + KMAC_MSG_FIFO_REG_OFFSET,
                    test_data[test_data_len - 1]);

  kmac_shake256_absorb(test_data, test_data_len);
}

class AbsorbWordsTest : public KmacTest {};

TEST_F(AbsorbWordsTest, Success) {
  std::array<uint32_t, 3> test_data = {0x12345678, 0xabcdef01, 0x02030405};

  // Expect all test data to be written to the FIFO.
  EXPECT_ABS_WRITE32(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[1]);
  EXPECT_ABS_WRITE32(base_ + KMAC_MSG_FIFO_REG_OFFSET, test_data[2]);

  kmac_shake256_absorb_words(test_data.data(), test_data.size());
}

TEST_F(AbsorbWordsTest, EmptyInput) {
  // Nothing should happen.
  kmac_shake256_absorb_words(NULL, 0);
}

class SqueezeTest : public KmacTest {};

TEST_F(SqueezeTest, Success) {
  std::array<uint32_t, 3> test_data = {0x12345678, 0xabcdef01, 0x02030405};
  std::array<uint32_t, 3> test_mask = {0xabcdef01, 0x02030405, 0x00000000};

  // Test assumption: test data fits in SHAKE-256 rate.
  ASSERT_LE(test_data.size(), shake256_rate_words_);

  ExpectPollState(KMAC_STATUS_SHA3_SQUEEZE_BIT, /*err=*/false);

  // Expect all data to be read from the state, one share at a time.
  for (size_t i = 0; i < test_data.size(); i++) {
    EXPECT_ABS_READ32(share0_addr_ + (i * sizeof(uint32_t)), test_mask[i]);
    EXPECT_ABS_READ32(share1_addr_ + (i * sizeof(uint32_t)),
                      test_data[i] ^ test_mask[i]);
  }

  // End
  ExpectPollState(KMAC_STATUS_SHA3_SQUEEZE_BIT, /*err=*/false);
  ExpectCmdWrite(KMAC_CMD_CMD_VALUE_DONE);

  uint32_t out[test_data.size()];
  EXPECT_EQ(kmac_shake256_squeeze_end(out, test_data.size()), kErrorOk);
  EXPECT_THAT(out, ElementsAreArray(test_data));
}

TEST_F(SqueezeTest, SuccessStart) {
  ExpectCmdWrite(KMAC_CMD_CMD_VALUE_PROCESS);

  kmac_shake256_squeeze_start();
}

TEST_F(SqueezeTest, StartAndEndEmpty) {
  // Start
  ExpectCmdWrite(KMAC_CMD_CMD_VALUE_PROCESS);
  kmac_shake256_squeeze_start();

  // End
  ExpectPollState(KMAC_STATUS_SHA3_SQUEEZE_BIT, /*err=*/false);
  ExpectCmdWrite(KMAC_CMD_CMD_VALUE_DONE);

  EXPECT_EQ(kmac_shake256_squeeze_end(NULL, 0), kErrorOk);
}

TEST_F(SqueezeTest, StartAndEndNonEmpty) {
  std::array<uint32_t, 3> test_data = {0x12345678, 0xabcdef01, 0x02030405};
  std::array<uint32_t, 3> test_mask = {0xabcdef01, 0x02030405, 0x00000000};

  // Test assumption: test data fits in SHAKE-256 rate.
  ASSERT_LE(test_data.size(), shake256_rate_words_);

  // Start
  ExpectCmdWrite(KMAC_CMD_CMD_VALUE_PROCESS);
  kmac_shake256_squeeze_start();

  // Squeeze
  ExpectPollState(KMAC_STATUS_SHA3_SQUEEZE_BIT, /*err=*/false);
  for (size_t i = 0; i < test_data.size(); i++) {
    EXPECT_ABS_READ32(share0_addr_ + (i * sizeof(uint32_t)), test_mask[i]);
    EXPECT_ABS_READ32(share1_addr_ + (i * sizeof(uint32_t)),
                      test_data[i] ^ test_mask[i]);
  }

  // End
  ExpectPollState(KMAC_STATUS_SHA3_SQUEEZE_BIT, /*err=*/false);
  ExpectCmdWrite(KMAC_CMD_CMD_VALUE_DONE);

  uint32_t out[test_data.size()];
  EXPECT_EQ(kmac_shake256_squeeze_end(out, test_data.size()), kErrorOk);
  EXPECT_THAT(out, ElementsAreArray(test_data));
}

TEST_F(SqueezeTest, LongOutput) {
  // Note: for this test, it is important that the Keccak rate for SHAKE-256 is
  // (1600 - (security strength * 2)) = 1088 bits = 34 words.
  std::array<uint32_t, 100> test_data;  // 0, 1, 2... 99
  std::array<uint32_t, 100> test_mask;  // 100, 99, 98,... 1
  for (size_t i = 0; i < test_data.size(); i++) {
    test_data[i] = i;
    test_mask[i] = test_data.size() - i;
  }

  ExpectPollState(KMAC_STATUS_SHA3_SQUEEZE_BIT, /*err=*/false);

  // Read remaining bits of state from offset..rate.
  // After this, we should have squeezed 34 out of 100 words.
  for (size_t i = 0; i < shake256_rate_words_; i++) {
    EXPECT_ABS_READ32(share0_addr_ + i * sizeof(uint32_t), test_mask[i]);
    EXPECT_ABS_READ32(share1_addr_ + i * sizeof(uint32_t),
                      test_data[i] ^ test_mask[i]);
  }

  // Expect a `RUN` command and a repeated polling.
  ExpectCmdWrite(KMAC_CMD_CMD_VALUE_RUN);
  ExpectPollState(KMAC_STATUS_SHA3_SQUEEZE_BIT, /*err=*/false);

  // Read all available state bits.
  // After this, we should have squeezed 68 out of 100 words.
  size_t offset = shake256_rate_words_;
  for (size_t i = 0; i < shake256_rate_words_; i++) {
    EXPECT_ABS_READ32(share0_addr_ + i * sizeof(uint32_t),
                      test_mask[offset + i]);
    EXPECT_ABS_READ32(share1_addr_ + i * sizeof(uint32_t),
                      test_data[offset + i] ^ test_mask[offset + i]);
  }

  // Expect a `RUN` command and a repeated polling.
  ExpectCmdWrite(KMAC_CMD_CMD_VALUE_RUN);
  ExpectPollState(KMAC_STATUS_SHA3_SQUEEZE_BIT, /*err=*/false);

  // Read the last 32 requested words.
  offset += shake256_rate_words_;
  for (size_t i = 0; i < test_data.size() - (2 * shake256_rate_words_); i++) {
    EXPECT_ABS_READ32(share0_addr_ + i * sizeof(uint32_t),
                      test_mask[offset + i]);
    EXPECT_ABS_READ32(share1_addr_ + i * sizeof(uint32_t),
                      test_data[offset + i] ^ test_mask[offset + i]);
  }

  // End
  ExpectPollState(KMAC_STATUS_SHA3_SQUEEZE_BIT, /*err=*/false);
  ExpectCmdWrite(KMAC_CMD_CMD_VALUE_DONE);

  uint32_t out[test_data.size()];
  EXPECT_EQ(kmac_shake256_squeeze_end(out, test_data.size()), kErrorOk);
  EXPECT_THAT(out, ElementsAreArray(test_data));
}

}  // namespace
}  // namespace kmac_unittest
