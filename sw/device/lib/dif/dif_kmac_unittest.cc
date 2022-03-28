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
  EXPECT_DIF_BADARG(dif_kmac_customization_string_init("", 0, nullptr));

  dif_kmac_customization_string_t cs;
  EXPECT_DIF_BADARG(dif_kmac_customization_string_init(nullptr, 1, &cs));
  EXPECT_DIF_BADARG(dif_kmac_customization_string_init(
      "", kDifKmacMaxCustomizationStringLen + 1, &cs));
  EXPECT_DIF_BADARG(dif_kmac_customization_string_init("", -1, &cs));
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
  EXPECT_DIF_BADARG(dif_kmac_function_name_init("", 0, nullptr));

  dif_kmac_function_name_t fn;
  EXPECT_DIF_BADARG(dif_kmac_function_name_init(nullptr, 1, &fn));
  EXPECT_DIF_BADARG(
      dif_kmac_function_name_init("", kDifKmacMaxFunctionNameLen + 1, &fn));
  EXPECT_DIF_BADARG(dif_kmac_function_name_init("", -1, &fn));
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

  struct ConfigRegister {
    bool enable = false;
    uint8_t key_strength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256;
    uint8_t mode = KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE;
    bool msg_big_endian = false;
    bool state_big_endian = false;
    bool sideload = false;
    uint8_t entropy_mode = KMAC_CFG_SHADOWED_ENTROPY_MODE_VALUE_IDLE_MODE;
    bool entropy_fast_process = false;
    bool msg_mask = false;
    bool entropy_ready = false;
    bool err_processed = false;
    bool enable_unsupported_mode_strength = false;
  } config_reg_;

  KmacTest() { EXPECT_DIF_OK(dif_kmac_init(dev().region(), &kmac_)); }

  /**
   * Set mmio write expectation for 8 bits data size.
   *
   * @param message Buffer with the data.
   * @param size Len of the buffer.
   */
  void ExpectMessageByte(const uint8_t *message, const size_t size) {
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
  void ExpectMessageInt32(const uint8_t *message, const size_t size) {
    // Check if the buffer is unaligned.
    size_t remaining = size;
    size_t unalignment = ((uintptr_t)message) % sizeof(uint32_t);
    if (unalignment) {
      // write unaligned data in bytes.
      unalignment = sizeof(uint32_t) - unalignment;
      ExpectMessageByte(message, unalignment);
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
      ExpectMessageByte(message, remaining);
    }
  }

  void ExpectConfig(void) {
    EXPECT_WRITE32_SHADOWED(
        KMAC_CFG_SHADOWED_REG_OFFSET,
        {{KMAC_CFG_SHADOWED_KMAC_EN_BIT, config_reg_.enable},
         {KMAC_CFG_SHADOWED_KSTRENGTH_OFFSET, config_reg_.key_strength},
         {KMAC_CFG_SHADOWED_MODE_OFFSET, config_reg_.mode},
         {KMAC_CFG_SHADOWED_MSG_ENDIANNESS_BIT, config_reg_.msg_big_endian},
         {KMAC_CFG_SHADOWED_STATE_ENDIANNESS_BIT, config_reg_.state_big_endian},
         {KMAC_CFG_SHADOWED_SIDELOAD_BIT, config_reg_.sideload},
         {KMAC_CFG_SHADOWED_ENTROPY_MODE_OFFSET, config_reg_.entropy_mode},
         {KMAC_CFG_SHADOWED_ENTROPY_FAST_PROCESS_BIT,
          config_reg_.entropy_fast_process},
         {KMAC_CFG_SHADOWED_MSG_MASK_BIT, config_reg_.msg_mask},
         {KMAC_CFG_SHADOWED_ENTROPY_READY_BIT, config_reg_.entropy_ready},
         {KMAC_CFG_SHADOWED_ERR_PROCESSED_BIT, config_reg_.err_processed},
         {KMAC_CFG_SHADOWED_EN_UNSUPPORTED_MODESTRENGTH_BIT,
          config_reg_.enable_unsupported_mode_strength}});
  }

  void ExpectKey(const dif_kmac_key_t &key) {
    std::map<dif_kmac_key_length_t, uint32_t> key_size_map = {
        {kDifKmacKeyLen128, KMAC_KEY_LEN_LEN_VALUE_KEY128},
        {kDifKmacKeyLen192, KMAC_KEY_LEN_LEN_VALUE_KEY192},
        {kDifKmacKeyLen256, KMAC_KEY_LEN_LEN_VALUE_KEY256},
        {kDifKmacKeyLen384, KMAC_KEY_LEN_LEN_VALUE_KEY384},
        {kDifKmacKeyLen512, KMAC_KEY_LEN_LEN_VALUE_KEY512},
    };

    EXPECT_WRITE32(KMAC_KEY_LEN_REG_OFFSET, key_size_map[key.length]);
    for (uint32_t i = 0; i < ARRAYSIZE(key.share0); ++i) {
      ptrdiff_t offset = KMAC_KEY_SHARE0_0_REG_OFFSET + (i * sizeof(uint32_t));
      EXPECT_WRITE32(offset, key.share0[i]);
      offset = KMAC_KEY_SHARE1_0_REG_OFFSET + (i * sizeof(uint32_t));
      EXPECT_WRITE32(offset, key.share1[i]);
    }
  }

  void ExpectPrefix(const uint32_t *prefix_regs, uint32_t size) {
    for (uint32_t i = 0; i < size; ++i) {
      ptrdiff_t offset = KMAC_PREFIX_0_REG_OFFSET + i * sizeof(uint32_t);
      EXPECT_WRITE32(offset, prefix_regs[i]);
    }
  }
};

class Kmac256Test : public KmacTest {
 protected:
  dif_kmac_key_t key_ = {
      .share0 = {0x43424140, 0x47464544, 0x4B4A4948, 0x4F4E4D4C, 0x53525150,
                 0x57565554, 0x5B5A5958, 0x5F5E5D5C},
      .share1 = {0},
      .length = kDifKmacKeyLen256,
  };
  dif_kmac_mode_kmac_t mode_ = kDifKmacModeKmacLen256;
  dif_kmac_customization_string_t custom_string_;

  Kmac256Test() {
    const std::string string = "My Tagged Application";
    EXPECT_DIF_OK(dif_kmac_customization_string_init(
        string.c_str(), string.size(), &custom_string_));
    config_reg_.enable = true;
    config_reg_.mode = KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE;
  }

  void ExpectPrefix(const dif_kmac_customization_string_t &s) {
    // Initialize prefix registers with function name ("KMAC") and empty
    // customization string. The empty customization string will be overwritten
    // if a non-empty string is provided.
    std::string prefix_str("\001 KMAC\001");

    // Encoded customization string (s) must be at least 3 bytes long if it is
    // not the empty string.
    if (s.length >= 3) {
      // First two bytes overwrite the pre-encoded empty customization string.
      prefix_str[prefix_str.size() - 1] |= s.buffer[0] & 0xFF;
      prefix_str.push_back(s.buffer[1] & 0xFF);
      prefix_str.insert(prefix_str.end(), &s.buffer[2], &s.buffer[s.length]);
    }

    std::vector<uint32_t> prefix_regs(11, 0);
    memcpy(prefix_regs.data(), prefix_str.data(), prefix_str.size());
    KmacTest::ExpectPrefix(prefix_regs.data(), prefix_regs.size());
  }
};

TEST_F(Kmac256Test, StartSuccess) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, true}});
  ExpectKey(key_);
  EXPECT_READ32(KMAC_CFG_SHADOWED_REG_OFFSET, 0);
  ExpectConfig();
  ExpectPrefix(custom_string_);
  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_START}});
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_ABSORB_BIT, true}});

  EXPECT_DIF_OK(dif_kmac_mode_kmac_start(&kmac_, &op_state_, mode_, 0, &key_,
                                         &custom_string_));
  EXPECT_EQ(op_state_.squeezing, false);
  EXPECT_EQ(op_state_.append_d, true);
  EXPECT_EQ(op_state_.offset, 0);
  EXPECT_EQ(op_state_.r, (1600 - 2 * 256) / 32);
  EXPECT_EQ(op_state_.d, 0);
}

TEST_F(Kmac256Test, StartBadArg) {
  EXPECT_DIF_BADARG(dif_kmac_mode_kmac_start(NULL, &op_state_, mode_, 0, &key_,
                                             &custom_string_));

  EXPECT_DIF_BADARG(
      dif_kmac_mode_kmac_start(&kmac_, NULL, mode_, 0, &key_, &custom_string_));

  EXPECT_DIF_BADARG(dif_kmac_mode_kmac_start(&kmac_, &op_state_, mode_,
                                             kDifKmacMaxOutputLenWords + 1,
                                             &key_, &custom_string_));

  EXPECT_DIF_BADARG(dif_kmac_mode_kmac_start(&kmac_, &op_state_,
                                             (dif_kmac_mode_kmac_t)0xff, 0,
                                             &key_, &custom_string_));

  EXPECT_DIF_BADARG(dif_kmac_mode_kmac_start(&kmac_, &op_state_, mode_, 0, NULL,
                                             &custom_string_));

  key_.length = static_cast<dif_kmac_key_length_t>(0xFF);
  EXPECT_DIF_BADARG(dif_kmac_mode_kmac_start(&kmac_, &op_state_, mode_, 0,
                                             &key_, &custom_string_));
}

TEST_F(Kmac256Test, StartError) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, false}});
  EXPECT_EQ(dif_kmac_mode_kmac_start(&kmac_, &op_state_, mode_, 0, &key_,
                                     &custom_string_),
            kDifError);
}

class Sha3_224Test : public KmacTest {
 protected:
  dif_kmac_mode_sha3_t mode_ = kDifKmacModeSha3Len224;

  Sha3_224Test() {
    config_reg_.mode = KMAC_CFG_SHADOWED_MODE_VALUE_SHA3;
    config_reg_.key_strength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L224;
  }
};

TEST_F(Sha3_224Test, StartSuccess) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, true}});
  EXPECT_READ32(KMAC_CFG_SHADOWED_REG_OFFSET,
                {{KMAC_CFG_SHADOWED_KMAC_EN_BIT, false}});
  ExpectConfig();
  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_START}});
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_ABSORB_BIT, true}});

  EXPECT_DIF_OK(dif_kmac_mode_sha3_start(&kmac_, &op_state_, mode_));
}

TEST_F(Sha3_224Test, StartBadArg) {
  EXPECT_DIF_BADARG(dif_kmac_mode_sha3_start(NULL, &op_state_, mode_));

  EXPECT_DIF_BADARG(dif_kmac_mode_sha3_start(&kmac_, NULL, mode_));

  EXPECT_DIF_BADARG(
      dif_kmac_mode_sha3_start(&kmac_, &op_state_, (dif_kmac_mode_sha3_t)0xff));
}

TEST_F(Sha3_224Test, StartError) {
  {
    EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, false}});
    EXPECT_EQ(dif_kmac_mode_sha3_start(&kmac_, &op_state_, mode_), kDifError);
  }
}

class Shake128Test : public KmacTest {
 protected:
  dif_kmac_mode_shake_t mode_ = kDifKmacModeShakeLen128;

  Shake128Test() {
    config_reg_.mode = KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE;
    config_reg_.key_strength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L128;
  }
};

TEST_F(Shake128Test, StartSuccess) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, true}});
  EXPECT_READ32(KMAC_CFG_SHADOWED_REG_OFFSET,
                {{KMAC_CFG_SHADOWED_KMAC_EN_BIT, false}});
  ExpectConfig();
  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_START}});
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_ABSORB_BIT, true}});

  EXPECT_DIF_OK(dif_kmac_mode_shake_start(&kmac_, &op_state_, mode_));
}

TEST_F(Shake128Test, StartBadArg) {
  EXPECT_DIF_BADARG(dif_kmac_mode_shake_start(NULL, &op_state_, mode_));

  EXPECT_DIF_BADARG(dif_kmac_mode_shake_start(&kmac_, NULL, mode_));

  EXPECT_DIF_BADARG(dif_kmac_mode_shake_start(&kmac_, &op_state_,
                                              (dif_kmac_mode_shake_t)0xff));
}

TEST_F(Shake128Test, StartError) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, false}});
  EXPECT_EQ(dif_kmac_mode_shake_start(&kmac_, &op_state_, mode_), kDifError);
}

constexpr std::array<uint8_t, 17> KmacTest::kMsg_;

class AbsorbalignmentMessage : public KmacTest {};

TEST_F(AbsorbalignmentMessage, Success) {
  uint8_t buffer[kMsg_.size() + sizeof(uint32_t)];

  for (size_t i = 0; i < sizeof(uint32_t); i++) {
    uint8_t *pMsg = &buffer[i];
    std::copy(kMsg_.begin(), kMsg_.end(), pMsg);

    EXPECT_READ32(KMAC_STATUS_REG_OFFSET, 3);
    ExpectMessageInt32(pMsg, kMsg_.size());

    EXPECT_DIF_OK(
        dif_kmac_absorb(&kmac_, &op_state_, pMsg, kMsg_.size(), NULL));
  }
}

class ConfigLock : public KmacTest {};

TEST_F(ConfigLock, Locked) {
  EXPECT_READ32(KMAC_CFG_REGWEN_REG_OFFSET, true);

  bool lock = false;
  EXPECT_EQ(dif_kmac_config_is_locked(&kmac_, &lock), kDifOk);
  EXPECT_TRUE(lock);
}

TEST_F(ConfigLock, Unlocked) {
  EXPECT_READ32(KMAC_CFG_REGWEN_REG_OFFSET, false);

  bool lock = true;
  EXPECT_EQ(dif_kmac_config_is_locked(&kmac_, &lock), kDifOk);
  EXPECT_FALSE(lock);
}
}  // namespace dif_kmac_unittest
