// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_kmac.h"

#include <array>
#include <string>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "kmac_regs.h"  // Generated

namespace dif_kmac_unittest {

using ::testing::ElementsAre;

TEST(CustomizationStringTest, Encode) {
  dif_kmac_customization_string_t cs;

  EXPECT_DIF_OK(dif_kmac_customization_string_init(nullptr, 0, &cs));
  EXPECT_THAT(std::string(&cs.buffer[0], 2), ElementsAre(1, 0));

  EXPECT_DIF_OK(dif_kmac_customization_string_init("", 0, &cs));
  EXPECT_THAT(std::string(&cs.buffer[0], 2), ElementsAre(1, 0));

  EXPECT_DIF_OK(dif_kmac_customization_string_init("\x00\x00", 2, &cs));
  EXPECT_THAT(std::string(&cs.buffer[0], 2), ElementsAre(1, 16));
  EXPECT_THAT(std::string(&cs.buffer[2], 2), ElementsAre(0, 0));

  EXPECT_DIF_OK(dif_kmac_customization_string_init("SHA-3", 5, &cs));
  EXPECT_THAT(std::string(&cs.buffer[0], 2), ElementsAre(1, 40));
  EXPECT_EQ(std::string(&cs.buffer[2], 5), "SHA-3");

  std::string max(kDifKmacMaxCustomizationStringLen, 0x12);
  EXPECT_DIF_OK(
      dif_kmac_customization_string_init(max.data(), max.size(), &cs));
  static_assert(kDifKmacMaxCustomizationStringLen == 32,
                "encoding needs to be updated");
  EXPECT_THAT(std::string(&cs.buffer[0], 3), ElementsAre(2, 1, 0));
  EXPECT_EQ(std::string(&cs.buffer[3], max.size()), max);
}

TEST(CustomizationStringTest, BadArg) {
  EXPECT_EQ(dif_kmac_customization_string_init("", 0, nullptr), kDifBadArg);

  dif_kmac_customization_string_t cs;
  EXPECT_EQ(dif_kmac_customization_string_init(nullptr, 1, &cs), kDifBadArg);
  EXPECT_EQ(dif_kmac_customization_string_init(
                "", kDifKmacMaxCustomizationStringLen + 1, &cs),
            kDifBadArg);
  EXPECT_EQ(dif_kmac_customization_string_init("", -1, &cs), kDifBadArg);
}

TEST(FunctionNameTest, Encode) {
  dif_kmac_function_name_t fn;

  EXPECT_DIF_OK(dif_kmac_function_name_init(nullptr, 0, &fn));
  EXPECT_THAT(std::string(&fn.buffer[0], 2), ElementsAre(1, 0));

  EXPECT_DIF_OK(dif_kmac_function_name_init("", 0, &fn));
  EXPECT_THAT(std::string(&fn.buffer[0], 2), ElementsAre(1, 0));

  EXPECT_DIF_OK(dif_kmac_function_name_init("\x00\x00", 2, &fn));
  EXPECT_THAT(std::string(&fn.buffer[0], 2), ElementsAre(1, 16));
  EXPECT_THAT(std::string(&fn.buffer[2], 2), ElementsAre(0, 0));

  EXPECT_DIF_OK(dif_kmac_function_name_init("KMAC", 4, &fn));
  EXPECT_THAT(std::string(&fn.buffer[0], 2), ElementsAre(1, 32));
  EXPECT_EQ(std::string(&fn.buffer[2], 4), "KMAC");

  std::string max(kDifKmacMaxFunctionNameLen, 0x34);
  EXPECT_DIF_OK(dif_kmac_function_name_init(max.data(), max.size(), &fn));
  static_assert(kDifKmacMaxFunctionNameLen == 4,
                "encoding needs to be updated");
  EXPECT_THAT(std::string(&fn.buffer[0], 2), ElementsAre(1, 32));
  EXPECT_EQ(std::string(&fn.buffer[2], max.size()), max);
}

TEST(FunctionNameTest, BadArg) {
  EXPECT_EQ(dif_kmac_function_name_init("", 0, nullptr), kDifBadArg);

  dif_kmac_function_name_t fn;
  EXPECT_EQ(dif_kmac_function_name_init(nullptr, 1, &fn), kDifBadArg);
  EXPECT_EQ(
      dif_kmac_function_name_init("", kDifKmacMaxFunctionNameLen + 1, &fn),
      kDifBadArg);
  EXPECT_EQ(dif_kmac_function_name_init("", -1, &fn), kDifBadArg);
}

using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

// Base class for the rest fixtures in this file.
class KmacTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  dif_kmac_t kmac_;
  dif_kmac_operation_state_t op_state_;
  static constexpr std::array<uint8_t, 17> kMsg_ = {
      0xa7, 0x48, 0x47, 0x93, 0x0a, 0x03, 0xab, 0xee, 0xa4,
      0x73, 0xe1, 0xf3, 0xdc, 0x30, 0xb8, 0x88, 0x15};

  KmacTest() { EXPECT_DIF_OK(dif_kmac_init(dev().region(), &kmac_)); }

  /**
   * Set mmio write expectation for 8 bits data size.
   *
   * @param message Buffer with the data.
   * @param size Len of the buffer.
   */
  void setExpectedMessageByte(const uint8_t *message, const size_t size) {
    for (size_t i = 0; i < size; ++i) {
      EXPECT_WRITE8(KMAC_MSG_FIFO_REG_OFFSET, message[i]);
    }
  }

  /**
   * Set mmio write expectation for 32 bits data size considering an alignment
   * of 32 bits.
   *
   * @param message Buffer with the data.
   * @param size Len of the buffer.
   */
  void setExpectedMessageInt32(const uint8_t *message, const size_t size) {
    // Check if the buffer is unaligned.
    size_t remaining = size;
    size_t unalignment = ((uintptr_t)message) % sizeof(uint32_t);
    if (unalignment) {
      // write unaligned data in bytes.
      unalignment = sizeof(uint32_t) - unalignment;
      setExpectedMessageByte(message, unalignment);
      message += unalignment;
      remaining -= unalignment;
    }

    // Write aligned part of the buffer.
    while (remaining >= sizeof(uint32_t)) {
      uint32_t word = 0;
      memcpy(&word, message, sizeof(uint32_t));
      EXPECT_WRITE32(KMAC_MSG_FIFO_REG_OFFSET, word);
      remaining -= sizeof(uint32_t);
      message += sizeof(uint32_t);
    }
    // Check if there still unaligned data in the buffer tail.
    if (remaining) {
      // write unaligned data in bytes.
      setExpectedMessageByte(message, remaining);
    }
  }
};
constexpr std::array<uint8_t, 17> KmacTest::kMsg_;

class AbsorbalignmentMessage : public KmacTest {};

TEST_F(AbsorbalignmentMessage, Success) {
  uint8_t buffer[kMsg_.size() + sizeof(uint32_t)];

  for (size_t i = 0; i < sizeof(uint32_t); i++) {
    uint8_t *pMsg = &buffer[i];
    std::copy(kMsg_.begin(), kMsg_.end(), pMsg);

    EXPECT_READ32(KMAC_STATUS_REG_OFFSET, 3);
    setExpectedMessageInt32(pMsg, kMsg_.size());

    EXPECT_DIF_OK(
        dif_kmac_absorb(&kmac_, &op_state_, pMsg, kMsg_.size(), NULL));
  }
}
}  // namespace dif_kmac_unittest
