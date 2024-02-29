// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_kmac.h"

#include <array>
#include <cstring>
#include <limits>
#include <ostream>
#include <string>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "kmac_regs.h"  // Generated

// We define global namespace == and << to make `dif_i2c_timing_params_t` work
// nicely with EXPECT_EQ.
bool operator==(dif_kmac_operation_state_t a, dif_kmac_operation_state_t b) {
  return a.squeezing == b.squeezing && a.append_d == b.append_d &&
         a.offset == b.offset && a.r == b.r && a.d == b.d;
}

std::ostream &operator<<(std::ostream &os,
                         const dif_kmac_operation_state_t &params) {
  return os << "{\n"
            << "  .squeezing = " << params.squeezing << ",\n"
            << "  .append_d = " << params.append_d << ",\n"
            << "  .offset = " << params.offset << ",\n"
            << "  .r = " << params.r << ",\n"
            << "  .d = " << params.d << ",\n"
            << "}";
}

namespace dif_kmac_unittest {

using ::testing::ElementsAre;
using testing::ElementsAreArray;

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
  dif_kmac_operation_state_t op_state_ = {
      .squeezing = false,
      .append_d = false,
      .offset = 0,
      .r = 0,
      .d = 0,
  };

  static constexpr std::array<uint8_t, 17> kMsg = {
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
    uint16_t entropy_hash_threshold = 0;
    uint16_t entropy_wait_timer = 0;
    uint16_t entropy_prescaler = 0;
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

  void ExpectEntropySeed(const uint32_t *seed) {
    for (uint32_t i = 0; i < kDifKmacEntropySeedWords; ++i) {
      ptrdiff_t offset = KMAC_ENTROPY_SEED_0_REG_OFFSET + i * sizeof(uint32_t);
      EXPECT_WRITE32(offset, seed[i]);
    }
  }

  uint32_t GetRateBits(uint32_t security_level) {
    // Formula for the rate in bits is:
    //
    //   r = 1600 - c
    //
    // Where c is the capacity (the security level in bits multiplied by two).
    return 1600 - 2 * security_level;
  }

  uint32_t GetRateWords(uint32_t security_level) {
    return GetRateBits(security_level) / 32;
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
  EXPECT_EQ(op_state_.r, GetRateWords(256));
  EXPECT_EQ(op_state_.d, 0);
}

TEST_F(Kmac256Test, StartBadArg) {
  EXPECT_DIF_BADARG(dif_kmac_mode_kmac_start(nullptr, &op_state_, mode_, 0,
                                             &key_, &custom_string_));

  EXPECT_DIF_BADARG(dif_kmac_mode_kmac_start(&kmac_, nullptr, mode_, 0, &key_,
                                             &custom_string_));

  EXPECT_DIF_BADARG(dif_kmac_mode_kmac_start(&kmac_, &op_state_, mode_,
                                             kDifKmacMaxOutputLenWords + 1,
                                             &key_, &custom_string_));

  EXPECT_DIF_BADARG(dif_kmac_mode_kmac_start(&kmac_, &op_state_,
                                             (dif_kmac_mode_kmac_t)0xff, 0,
                                             &key_, &custom_string_));

  EXPECT_DIF_BADARG(dif_kmac_mode_kmac_start(&kmac_, &op_state_, mode_, 0,
                                             nullptr, &custom_string_));

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
  EXPECT_DIF_BADARG(dif_kmac_mode_sha3_start(nullptr, &op_state_, mode_));

  EXPECT_DIF_BADARG(dif_kmac_mode_sha3_start(&kmac_, nullptr, mode_));

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
  EXPECT_DIF_BADARG(dif_kmac_mode_shake_start(nullptr, &op_state_, mode_));

  EXPECT_DIF_BADARG(dif_kmac_mode_shake_start(&kmac_, nullptr, mode_));

  EXPECT_DIF_BADARG(dif_kmac_mode_shake_start(&kmac_, &op_state_,
                                              (dif_kmac_mode_shake_t)0xff));
}

TEST_F(Shake128Test, StartError) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, false}});
  EXPECT_EQ(dif_kmac_mode_shake_start(&kmac_, &op_state_, mode_), kDifError);
}

class Cshake256Test : public KmacTest {
 protected:
  dif_kmac_mode_cshake_t mode_ = kDifKmacModeCshakeLen256;
  dif_kmac_customization_string_t custom_str_;
  dif_kmac_function_name_t func_name_;

  Cshake256Test() {
    const std::string string = "My Application";
    EXPECT_DIF_OK(dif_kmac_customization_string_init(
        string.c_str(), string.size(), &custom_str_));

    const std::string kFunctionName = "Foo";
    EXPECT_DIF_OK(dif_kmac_function_name_init(
        kFunctionName.c_str(), kFunctionName.size(), &func_name_));

    config_reg_.mode = KMAC_CFG_SHADOWED_MODE_VALUE_CSHAKE;
    config_reg_.key_strength = KMAC_CFG_SHADOWED_KSTRENGTH_VALUE_L256;
  }

  void ExpectPrefix(const dif_kmac_customization_string_t &s) {
    // Calculate PREFIX register values.
    std::vector<uint8_t> prefixData;
    if (func_name_.length == 0) {
      // Append left encoded empty string.
      prefixData.push_back(1);
      prefixData.push_back(0);
    } else {
      prefixData.insert(prefixData.end(), func_name_.buffer,
                        func_name_.buffer + func_name_.length);
    }

    if (s.length == 0) {
      // Append left encoded empty string.
      prefixData.push_back(1);
      prefixData.push_back(0);
    } else {
      prefixData.insert(prefixData.end(), s.buffer, s.buffer + s.length);
    }

    std::vector<uint32_t> prefixRegs(11, 0);
    memcpy(prefixRegs.data(), prefixData.data(), prefixData.size());
    KmacTest::ExpectPrefix(prefixRegs.data(), prefixRegs.size());
  }

  void CheckOperationState(dif_kmac_operation_state_t &operation_state) {
    EXPECT_EQ(op_state_.squeezing, false);
    EXPECT_EQ(op_state_.append_d, false);
    EXPECT_EQ(op_state_.offset, 0);
    EXPECT_EQ(op_state_.d, 0);
    EXPECT_EQ(op_state_.r, GetRateWords(256));
  }
};

TEST_F(Cshake256Test, StartAllArgsSuccess) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, true}});
  EXPECT_READ32(KMAC_CFG_SHADOWED_REG_OFFSET,
                {{KMAC_CFG_SHADOWED_KMAC_EN_BIT, false}});
  ExpectConfig();
  ExpectPrefix(custom_str_);
  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_START}});
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_ABSORB_BIT, true}});

  EXPECT_DIF_OK(dif_kmac_mode_cshake_start(&kmac_, &op_state_, mode_,
                                           &func_name_, &custom_str_));
  CheckOperationState(op_state_);
}

TEST_F(Cshake256Test, StartNoFuncNameSuccess) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, true}});
  EXPECT_READ32(KMAC_CFG_SHADOWED_REG_OFFSET,
                {{KMAC_CFG_SHADOWED_KMAC_EN_BIT, false}});
  ExpectConfig();
  func_name_.length = 0;
  ExpectPrefix(custom_str_);
  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_START}});
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_ABSORB_BIT, true}});

  EXPECT_DIF_OK(dif_kmac_mode_cshake_start(&kmac_, &op_state_, mode_, nullptr,
                                           &custom_str_));
  CheckOperationState(op_state_);
}

TEST_F(Cshake256Test, StartNoCustomStrSuccess) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, true}});
  EXPECT_READ32(KMAC_CFG_SHADOWED_REG_OFFSET,
                {{KMAC_CFG_SHADOWED_KMAC_EN_BIT, false}});
  ExpectConfig();
  custom_str_.length = 0;
  ExpectPrefix(custom_str_);
  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_START}});
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_ABSORB_BIT, true}});

  EXPECT_DIF_OK(dif_kmac_mode_cshake_start(&kmac_, &op_state_, mode_,
                                           &func_name_, nullptr));
  CheckOperationState(op_state_);
}

/**
 * In case the Function name and the Custom string are both empty the
 * `dif_kmac_mode_cshake_start` will fallback to `dif_kmac_mode_shake_start`.
 */
TEST_F(Cshake256Test, StartFallbackToShakeSuccess) {
  config_reg_.mode = KMAC_CFG_SHADOWED_MODE_VALUE_SHAKE;

  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, true}});
  EXPECT_READ32(KMAC_CFG_SHADOWED_REG_OFFSET,
                {{KMAC_CFG_SHADOWED_KMAC_EN_BIT, false}});
  ExpectConfig();
  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_START}});
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_ABSORB_BIT, true}});
  EXPECT_DIF_OK(
      dif_kmac_mode_cshake_start(&kmac_, &op_state_, mode_, nullptr, nullptr));
}

TEST_F(Cshake256Test, StartBadArg) {
  EXPECT_DIF_BADARG(dif_kmac_mode_cshake_start(nullptr, &op_state_, mode_,
                                               &func_name_, &custom_str_));

  EXPECT_DIF_BADARG(dif_kmac_mode_cshake_start(&kmac_, nullptr, mode_,
                                               &func_name_, &custom_str_));

  EXPECT_DIF_BADARG(dif_kmac_mode_cshake_start(&kmac_, &op_state_,
                                               (dif_kmac_mode_cshake_t)0xff,
                                               &func_name_, &custom_str_));

  EXPECT_DIF_BADARG(dif_kmac_mode_cshake_start(
      &kmac_, &op_state_, (dif_kmac_mode_cshake_t)0xff, nullptr, nullptr));
}

TEST_F(Cshake256Test, StartError) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, false}});
  EXPECT_EQ(dif_kmac_mode_cshake_start(&kmac_, &op_state_, mode_, &func_name_,
                                       &custom_str_),
            kDifError);
}

constexpr std::array<uint8_t, 17> KmacTest::kMsg;

class AbsorbalignmentMessage : public KmacTest {
 protected:
  AbsorbalignmentMessage() { op_state_.r = GetRateWords(256); }
};

TEST_F(AbsorbalignmentMessage, Success) {
  // Test assumption: message fits in the FIFO.
  static_assert(kMsg.size() <= KMAC_PARAM_NUM_ENTRIES_MSG_FIFO *
                                   KMAC_PARAM_NUM_BYTES_MSG_FIFO_ENTRY,
                "Message must fit in the KMAC message FIFO.");

  uint8_t buffer[kMsg.size() + sizeof(uint32_t)];

  for (size_t i = 0; i < sizeof(uint32_t); i++) {
    uint8_t *pMsg = &buffer[i];
    std::copy(kMsg.begin(), kMsg.end(), pMsg);

    // First status read: checks for absorb bit.
    EXPECT_READ32(KMAC_STATUS_REG_OFFSET, 1 << KMAC_STATUS_SHA3_ABSORB_BIT);

    // Second status read: checks FIFO depth. Always return 0 (i.e. 0 entries
    // occupied, FIFO is completely free).
    EXPECT_READ32(KMAC_STATUS_REG_OFFSET, 1 << KMAC_STATUS_SHA3_ABSORB_BIT);
    ExpectMessageInt32(pMsg, kMsg.size());

    EXPECT_DIF_OK(
        dif_kmac_absorb(&kmac_, &op_state_, pMsg, kMsg.size(), nullptr));
  }
}

class ConfigLock : public KmacTest {};

TEST_F(ConfigLock, Locked) {
  EXPECT_READ32(KMAC_CFG_REGWEN_REG_OFFSET, 0);

  bool lock = false;
  EXPECT_EQ(dif_kmac_config_is_locked(&kmac_, &lock), kDifOk);
  EXPECT_TRUE(lock);
}

TEST_F(ConfigLock, Unlocked) {
  EXPECT_READ32(KMAC_CFG_REGWEN_REG_OFFSET, 1);

  bool lock = true;
  EXPECT_EQ(dif_kmac_config_is_locked(&kmac_, &lock), kDifOk);
  EXPECT_FALSE(lock);
}

TEST_F(ConfigLock, BadArg) {
  bool locked;
  EXPECT_DIF_BADARG(dif_kmac_config_is_locked(nullptr, &locked));
  EXPECT_DIF_BADARG(dif_kmac_config_is_locked(&kmac_, nullptr));
}

class KmacEndTest : public KmacTest {
 protected:
  KmacEndTest() { op_state_.squeezing = true; }
};

TEST_F(KmacEndTest, Success) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_SQUEEZE_BIT, true}});
  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_DONE}});

  EXPECT_DIF_OK(dif_kmac_end(&kmac_, &op_state_));

  EXPECT_EQ(op_state_.squeezing, false);
  EXPECT_EQ(op_state_.append_d, false);
  EXPECT_EQ(op_state_.offset, 0);
  EXPECT_EQ(op_state_.r, 0);
  EXPECT_EQ(op_state_.d, 0);
}

TEST_F(KmacEndTest, BadArg) {
  EXPECT_DIF_BADARG(dif_kmac_end(nullptr, &op_state_));

  EXPECT_DIF_BADARG(dif_kmac_end(&kmac_, nullptr));
}

TEST_F(KmacEndTest, Error) {
  op_state_.squeezing = false;
  EXPECT_EQ(dif_kmac_end(&kmac_, &op_state_), kDifError);
}

class KmacConfigureTest : public KmacTest {
 protected:
  dif_kmac_config_t kmac_config_ = {
      .entropy_mode = kDifKmacEntropyModeIdle,
      .entropy_fast_process = false,
      .entropy_seed = {0xaa25b4bf, 0x48ce8fff, 0x5a78282a, 0x48465647,
                       0x70410fef},
      .entropy_hash_threshold = 0x03ff,
      .entropy_wait_timer = 0xffff,
      .entropy_prescaler = 0x03ff,
      .message_big_endian = false,
      .output_big_endian = false,
      .sideload = false,
      .msg_mask = true,
  };
  KmacConfigureTest() {
    config_reg_.entropy_hash_threshold = kmac_config_.entropy_hash_threshold,
    config_reg_.entropy_wait_timer = kmac_config_.entropy_wait_timer,
    config_reg_.entropy_prescaler = kmac_config_.entropy_prescaler,
    config_reg_.msg_big_endian = kmac_config_.message_big_endian;
    config_reg_.state_big_endian = kmac_config_.output_big_endian;
    config_reg_.entropy_mode = kmac_config_.entropy_mode;
    config_reg_.entropy_fast_process = kmac_config_.entropy_fast_process;
    config_reg_.sideload = kmac_config_.sideload;
    config_reg_.key_strength = 0;
    config_reg_.mode = 0;
    config_reg_.msg_mask = kmac_config_.msg_mask;
  }
};

TEST_F(KmacConfigureTest, Success) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, true}});
  EXPECT_WRITE32(
      KMAC_ENTROPY_PERIOD_REG_OFFSET,
      {{KMAC_ENTROPY_PERIOD_PRESCALER_OFFSET, kmac_config_.entropy_prescaler},
       {KMAC_ENTROPY_PERIOD_WAIT_TIMER_OFFSET,
        kmac_config_.entropy_wait_timer}});
  EXPECT_WRITE32_SHADOWED(
      KMAC_ENTROPY_REFRESH_THRESHOLD_SHADOWED_REG_OFFSET,
      {{KMAC_ENTROPY_REFRESH_THRESHOLD_SHADOWED_THRESHOLD_OFFSET,
        kmac_config_.entropy_hash_threshold}});
  ExpectConfig();
  ExpectEntropySeed(kmac_config_.entropy_seed);
  EXPECT_DIF_OK(dif_kmac_configure(&kmac_, kmac_config_));
}

TEST_F(KmacConfigureTest, BadArg) {
  EXPECT_DIF_BADARG(dif_kmac_configure(NULL, kmac_config_));
  kmac_config_.entropy_mode = (dif_kmac_entropy_mode_t)0xff;
  EXPECT_DIF_BADARG(dif_kmac_configure(&kmac_, kmac_config_));
}

TEST_F(KmacConfigureTest, Locked) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, false}});
  EXPECT_EQ(dif_kmac_configure(&kmac_, kmac_config_), kDifLocked);
}

class KmacStatusTest : public KmacTest {
 protected:
  dif_kmac_status_t status_;
};

TEST_F(KmacStatusTest, IdleFifoEmptySuccess) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_IDLE_BIT, true},
                                         {KMAC_STATUS_FIFO_EMPTY_BIT, true}});
  EXPECT_DIF_OK(dif_kmac_get_status(&kmac_, &status_));

  EXPECT_EQ(status_.sha3_state, kDifKmacSha3StateIdle);
  EXPECT_EQ(status_.fifo_depth, 0);
  EXPECT_EQ(status_.fifo_state, kDifKmacFifoStateEmpty);
  EXPECT_EQ(status_.faults, kDifKmacAlertNone);
}

TEST_F(KmacStatusTest, AbsorbingFifoPartialSuccess) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_ABSORB_BIT, true},
                                         {KMAC_STATUS_FIFO_DEPTH_OFFSET,
                                          KMAC_PARAM_NUM_ENTRIES_MSG_FIFO}});
  EXPECT_DIF_OK(dif_kmac_get_status(&kmac_, &status_));

  EXPECT_EQ(status_.sha3_state, kDifKmacSha3StateAbsorbing);
  EXPECT_EQ(status_.fifo_depth, KMAC_PARAM_NUM_ENTRIES_MSG_FIFO);
  EXPECT_EQ(status_.fifo_state, kDifKmacFifoStatePartial);
  EXPECT_EQ(status_.faults, kDifKmacAlertNone);
}

TEST_F(KmacStatusTest, SqueezingFifoFullSuccess) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_SQUEEZE_BIT, true},
                                         {KMAC_STATUS_FIFO_DEPTH_OFFSET, 15},
                                         {KMAC_STATUS_FIFO_FULL_BIT, true}});
  EXPECT_DIF_OK(dif_kmac_get_status(&kmac_, &status_));

  EXPECT_EQ(status_.sha3_state, kDifKmacSha3StateSqueezing);
  EXPECT_EQ(status_.fifo_depth, 15);
  EXPECT_EQ(status_.fifo_state, kDifKmacFifoStateFull);
  EXPECT_EQ(status_.faults, kDifKmacAlertNone);
}

TEST_F(KmacStatusTest, AbsorbingFifoFullFatalFault) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET,
                {{KMAC_STATUS_SHA3_ABSORB_BIT, true},
                 {KMAC_STATUS_FIFO_DEPTH_OFFSET, 5},
                 {KMAC_STATUS_FIFO_FULL_BIT, true},
                 {KMAC_STATUS_ALERT_FATAL_FAULT_BIT, true}});
  EXPECT_DIF_OK(dif_kmac_get_status(&kmac_, &status_));

  EXPECT_EQ(status_.sha3_state, kDifKmacSha3StateAbsorbing);
  EXPECT_EQ(status_.fifo_depth, 5);
  EXPECT_EQ(status_.fifo_state, kDifKmacFifoStateFull);
  EXPECT_EQ(status_.faults, kDifKmacAlertFatalFault);
}

TEST_F(KmacStatusTest, AbsorbingFifoFullUpdateError) {
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET,
                {{KMAC_STATUS_SHA3_ABSORB_BIT, true},
                 {KMAC_STATUS_FIFO_DEPTH_OFFSET, 2},
                 {KMAC_STATUS_FIFO_FULL_BIT, true},
                 {KMAC_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT, true}});
  EXPECT_DIF_OK(dif_kmac_get_status(&kmac_, &status_));

  EXPECT_EQ(status_.sha3_state, kDifKmacSha3StateAbsorbing);
  EXPECT_EQ(status_.fifo_depth, 2);
  EXPECT_EQ(status_.fifo_state, kDifKmacFifoStateFull);
  EXPECT_EQ(status_.faults, kDifKmacAlertRecovCtrlUpdate);
}

TEST_F(KmacStatusTest, BadArg) {
  EXPECT_DIF_BADARG(dif_kmac_get_status(nullptr, &status_));
  EXPECT_DIF_BADARG(dif_kmac_get_status(&kmac_, nullptr));
}

class KmacGetErrorTest : public KmacTest {
 protected:
  static constexpr std::array<dif_kmac_error_t, 7> kErrors = {
      kDifErrorNone,
      kDifErrorKeyNotValid,
      kDifErrorSoftwarePushedMessageFifo,
      kDifErrorSoftwarePushedWrongCommand,
      kDifErrorEntropyWaitTimerExpired,
      kDifErrorEntropyModeIncorrect,
      kDifErrorUnknownError};
  dif_kmac_error_t error_;
  KmacGetErrorTest() { op_state_.squeezing = true; }
};
constexpr std::array<dif_kmac_error_t, 7> KmacGetErrorTest::kErrors;

TEST_F(KmacGetErrorTest, Success) {
  for (auto err : kErrors) {
    EXPECT_READ32(KMAC_ERR_CODE_REG_OFFSET, err);
    EXPECT_DIF_OK(dif_kmac_get_error(&kmac_, &error_));
    EXPECT_EQ(error_, err);
  }
}

TEST_F(KmacGetErrorTest, BadArg) {
  EXPECT_DIF_BADARG(dif_kmac_get_error(nullptr, &error_));

  EXPECT_DIF_BADARG(dif_kmac_get_error(&kmac_, nullptr));
}

class KmacGetHashCounterTest : public KmacTest {
 protected:
  uint32_t hash_ctr_;
};

TEST_F(KmacGetHashCounterTest, Success) {
  EXPECT_READ32(KMAC_ENTROPY_REFRESH_HASH_CNT_REG_OFFSET,
                {{KMAC_PARAM_HASH_CNT_W, 0}});
  EXPECT_DIF_OK(dif_kmac_get_hash_counter(&kmac_, &hash_ctr_));
}

TEST_F(KmacGetHashCounterTest, BadArg) {
  EXPECT_DIF_BADARG(dif_kmac_get_hash_counter(nullptr, &hash_ctr_));

  EXPECT_DIF_BADARG(dif_kmac_get_hash_counter(&kmac_, nullptr));
}

class KmacSqueezeTest : public KmacTest {
 protected:
  dif_kmac_operation_state_t expected_op_state_ = {
      .squeezing = true,
      .append_d = false,
      .offset = 30,
      .r = 34,
      .d = 30,
  };

  uint32_t out_buffer_[8];
  size_t processed_;
  static constexpr std::array<std::array<uint32_t, 64>, 2> kOutShares = {
      {{0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0x5AA5A55A, 0x5AA5A55A,
        0x5AA5A55A, 0x5AA5A55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A,
        0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0xA55AA55A, 0xA55AA55A,
        0xA55AA55A, 0xA55AA55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A,
        0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0x5AA5A55A, 0x5AA5A55A,
        0x5AA5A55A, 0x5AA5A55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A,
        0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0xA55AA55A, 0xA55AA55A,
        0xA55AA55A, 0xA55AA55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A,
        0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0x5AA5A55A, 0x5AA5A55A,
        0x5AA5A55A, 0x5AA5A55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A,
        0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A},
       {0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0x5AA5A55A, 0x5AA5A55A,
        0x5AA5A55A, 0x5AA5A55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A,
        0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0xA55AA55A, 0xA55AA55A,
        0xA55AA55A, 0xA55AA55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A,
        0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0x5AA5A55A, 0x5AA5A55A,
        0x5AA5A55A, 0x5AA5A55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A,
        0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0xA55AA55A, 0xA55AA55A,
        0xA55AA55A, 0xA55AA55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A,
        0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0x5AA5A55A, 0x5AA5A55A,
        0x5AA5A55A, 0x5AA5A55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A,
        0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A}}};

  KmacSqueezeTest() {
    op_state_.r = GetRateWords(256);
    op_state_.squeezing = false;
    op_state_.append_d = false;
  }

  void ExpectAppendSize() {
    uint32_t d = op_state_.d * sizeof(uint32_t) * 8;
    uint8_t len = 1 + (d > 0xFF) + (d > 0xFFFF) + (d > 0xFFFFFF);
    uint8_t shift = len * 8;
    do {
      shift -= 8;
      EXPECT_WRITE8(KMAC_MSG_FIFO_REG_OFFSET, (d >> shift) & 0xFF);
    } while (shift);
    EXPECT_WRITE8(KMAC_MSG_FIFO_REG_OFFSET, len & 0xFF);
  }

  void ExpectReadOutput(const uint32_t *share1, const uint32_t *share2,
                        size_t len) {
    uint32_t offset = KMAC_STATE_REG_OFFSET;
    for (size_t i = 0; i < len; ++i) {
      // Read both shares from state register and combine using XOR.
      EXPECT_READ32(offset, share1[i]);
      EXPECT_READ32(offset + 0x100, share2[i]);
      offset += sizeof(uint32_t);
    }
  }
};
constexpr std::array<std::array<uint32_t, 64>, 2> KmacSqueezeTest::kOutShares;

TEST_F(KmacSqueezeTest, GenerateExtraStatesSuccess) {
  uint32_t out_buffer[64];
  op_state_.d = ARRAYSIZE(out_buffer);

  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_PROCESS}});
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_SQUEEZE_BIT, true}});
  ExpectReadOutput(kOutShares[0].data(), kOutShares[1].data(), 34);
  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_RUN}});
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_SQUEEZE_BIT, true}});
  ExpectReadOutput(&kOutShares[0].data()[34], &kOutShares[1].data()[34],
                   kOutShares[0].size() - 34);

  EXPECT_DIF_OK(dif_kmac_squeeze(&kmac_, &op_state_, out_buffer,
                                 ARRAYSIZE(out_buffer), nullptr));

  EXPECT_EQ(op_state_, expected_op_state_);

  std::array<uint32_t, ARRAYSIZE(out_buffer)> out;
  for (size_t i = 0; i < out.size(); i++) {
    out[i] = kOutShares[0][i] ^ kOutShares[1][i];
  }
  EXPECT_THAT(out_buffer, ElementsAreArray(out));
}

TEST_F(KmacSqueezeTest, FillOutBufferSuccess) {
  op_state_.d = ARRAYSIZE(out_buffer_);
  expected_op_state_.d = ARRAYSIZE(out_buffer_);
  expected_op_state_.offset = 8;

  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_PROCESS}});
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET, {{KMAC_STATUS_SHA3_SQUEEZE_BIT, true}});
  ExpectReadOutput(kOutShares[0].data(), kOutShares[1].data(),
                   ARRAYSIZE(out_buffer_));

  EXPECT_DIF_OK(dif_kmac_squeeze(&kmac_, &op_state_, out_buffer_,
                                 ARRAYSIZE(out_buffer_), nullptr));

  EXPECT_EQ(op_state_, expected_op_state_);

  std::array<uint32_t, ARRAYSIZE(out_buffer_)> out;
  for (size_t i = 0; i < out.size(); i++) {
    out[i] = kOutShares[0][i] ^ kOutShares[1][i];
  }
  EXPECT_THAT(out_buffer_, ElementsAreArray(out));
}

TEST_F(KmacSqueezeTest, AppendSizeSuccess) {
  op_state_.append_d = true;
  op_state_.d = ARRAYSIZE(out_buffer_);
  expected_op_state_.append_d = true;
  expected_op_state_.d = ARRAYSIZE(out_buffer_);
  expected_op_state_.r = GetRateWords(256);
  expected_op_state_.offset = 0;

  ExpectAppendSize();
  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_PROCESS}});
  EXPECT_DIF_OK(dif_kmac_squeeze(&kmac_, &op_state_, nullptr, 0, nullptr));

  EXPECT_EQ(op_state_, expected_op_state_);
}

TEST_F(KmacSqueezeTest, JustProcessSuccess) {
  expected_op_state_.d = 0;
  expected_op_state_.r = GetRateWords(256);
  expected_op_state_.offset = 0;
  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_PROCESS}});

  EXPECT_DIF_OK(dif_kmac_squeeze(&kmac_, &op_state_, nullptr, 0, nullptr));
  EXPECT_EQ(op_state_, expected_op_state_);
  EXPECT_EQ(op_state_.d, 0);
}

TEST_F(KmacSqueezeTest, BadArg) {
  EXPECT_DIF_BADARG(dif_kmac_squeeze(NULL, &op_state_, out_buffer_,
                                     ARRAYSIZE(out_buffer_), nullptr));
  EXPECT_DIF_BADARG(dif_kmac_squeeze(&kmac_, nullptr, out_buffer_,
                                     ARRAYSIZE(out_buffer_), nullptr));
  EXPECT_DIF_BADARG(dif_kmac_squeeze(&kmac_, &op_state_, nullptr,
                                     ARRAYSIZE(out_buffer_), nullptr));
}

TEST_F(KmacSqueezeTest, StarteMachineError) {
  op_state_.d = ARRAYSIZE(out_buffer_) / 2;
  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_PROCESS}});

  EXPECT_EQ(dif_kmac_squeeze(&kmac_, &op_state_, out_buffer_,
                             ARRAYSIZE(out_buffer_), nullptr),
            kDifError);
}

TEST_F(KmacSqueezeTest, RequestLessDataThanFixedLenError) {
  op_state_.d = ARRAYSIZE(out_buffer_);

  EXPECT_WRITE32(KMAC_CMD_REG_OFFSET,
                 {{KMAC_CMD_CMD_OFFSET, KMAC_CMD_CMD_VALUE_PROCESS}});
  EXPECT_READ32(KMAC_STATUS_REG_OFFSET,
                {{KMAC_STATUS_SHA3_SQUEEZE_BIT, false}});
  EXPECT_READ32(KMAC_INTR_STATE_REG_OFFSET,
                {{KMAC_INTR_STATE_KMAC_ERR_BIT, true}});

  EXPECT_EQ(dif_kmac_squeeze(&kmac_, &op_state_, out_buffer_,
                             ARRAYSIZE(out_buffer_), nullptr),
            kDifError);
}

class KmacResetTest : public KmacTest {};

TEST_F(KmacResetTest, Success) {
  EXPECT_READ32(KMAC_CFG_SHADOWED_REG_OFFSET, 0);
  EXPECT_WRITE32_SHADOWED(KMAC_CFG_SHADOWED_REG_OFFSET,
                          {{KMAC_CFG_SHADOWED_ERR_PROCESSED_BIT, true}});
  EXPECT_DIF_OK(dif_kmac_reset(&kmac_, &op_state_));
  EXPECT_EQ(op_state_.squeezing, false);
  EXPECT_EQ(op_state_.append_d, false);
  EXPECT_EQ(op_state_.offset, 0);
  EXPECT_EQ(op_state_.r, 0);
  EXPECT_EQ(op_state_.d, 0);
}

TEST_F(KmacResetTest, BadArg) {
  EXPECT_DIF_BADARG(dif_kmac_reset(nullptr, &op_state_));

  EXPECT_DIF_BADARG(dif_kmac_reset(&kmac_, nullptr));
}

}  // namespace dif_kmac_unittest
