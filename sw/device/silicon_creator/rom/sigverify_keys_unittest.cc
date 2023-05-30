// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <array>
#include <cstring>
#include <limits>
#include <numeric>
#include <unordered_set>

#include "gtest/gtest.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/mock_lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/rom/sigverify_keys_rsa.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "otp_ctrl_regs.h"

// Define the symbols that the sigverify library expects for the mock keys
// defined below.
extern "C" {
/**
 * Mock keys used in tests.
 *
 * We only initialize the first word of `n`, which is the key ID, and `key_type`
 * since these are the only fields that are used for determining the validity of
 * a key. The remaining fields are initialized only because non-trivial
 * designated initializers are not supported.
 */
constexpr sigverify_rom_rsa_key_t kSigverifyRsaKeys[]{
    {
        .entry = {.key_type = kSigverifyKeyTypeTest,
                  .key = {.n = {{0xa0}}, .n0_inv = {0}}},
    },
    {
        .entry = {.key_type = kSigverifyKeyTypeProd,
                  .key = {.n = {{0xb0}}, .n0_inv = {0}}},
    },
    {
        .entry = {.key_type = kSigverifyKeyTypeDev,
                  .key = {.n = {{0xc0}}, .n0_inv = {0}}},
    },
    {
        .entry = {.key_type = kSigverifyKeyTypeTest,
                  .key = {.n = {{0xa1}}, .n0_inv = {0}}},
    },
    {
        .entry = {.key_type = kSigverifyKeyTypeProd,
                  .key = {.n = {{0xb1}}, .n0_inv = {0}}},
    },
    {
        .entry = {.key_type = kSigverifyKeyTypeDev,
                  .key = {.n = {{0xc1}}, .n0_inv = {0}}},
    },
    {
        .entry = {.key_type = static_cast<sigverify_key_type_t>(
                      std::numeric_limits<uint32_t>::max()),
                  .key = {.n = {{0xff}}, .n0_inv = {0}}},
    },
};

constexpr size_t kSigverifyRsaKeysCnt =
    std::extent<decltype(kSigverifyRsaKeys)>::value;
static_assert(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN_SIZE >=
                  kSigverifyRsaKeysCnt,
              "CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN OTP item must be at least "
              "`kSigVerifyRsaKeysCnt` bytes.");
// Using 1 as the step size since it is coprime with every integer.
constexpr size_t kSigverifyRsaKeysStep = 1;
}

namespace sigverify_keys_unittest {
namespace {
using ::testing::Return;

/**
 * Returns the indices of mock keys of the given type.
 *
 * @param key_type A key type.
 * @return Indices of mock keys of the given type.
 */
std::vector<size_t> MockKeyIndicesOfType(sigverify_key_type_t key_type) {
  std::vector<size_t> indices;
  for (size_t i = 0; i < kSigverifyRsaKeysCnt; ++i) {
    if (kSigverifyRsaKeys[i].entry.key_type == key_type) {
      indices.push_back(i);
    }
  }
  return indices;
}

/**
 * Life cycle states used in parameterized tests.
 */

constexpr std::array<lifecycle_state_t, 4> kLcStatesNonTestOperational{
    kLcStateDev,
    kLcStateProd,
    kLcStateProdEnd,
    kLcStateRma,
};

constexpr std::array<lifecycle_state_t, 6> kLcStatesAll{
    kLcStateTest,
    kLcStateDev,
    kLcStateProd,
    kLcStateProdEnd,
    kLcStateRma,
    // An invalid state
    static_cast<lifecycle_state_t>(0),
};

class SigverifyKeys : public rom_test::RomTest {
 protected:
  /**
   * Sets expectations for getting the keys stored in the ROM.
   */
  void ExpectKeysGet() {
    EXPECT_CALL(rnd_, Uint32())
        .WillOnce(Return(std::numeric_limits<uint32_t>::max()));
  }

  /**
   * Sets an expectation for an OTP read for the key at the given index.
   *
   * The value that corresponds to `key_index` will be `is_valid` and the
   * values for all other keys in the corresponding OTP word will be the
   * complement of `is_valid`.
   *
   * @param key_index Index of a key.
   * @param is_valid Validitiy of the key.
   */
  void ExpectOtpRead(size_t key_index, hardened_byte_bool_t is_valid) {
    const uint32_t read_addr =
        OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN_OFFSET +
        (key_index / kSigverifyNumEntriesPerOtpWord) * sizeof(uint32_t);
    const size_t entry_index = key_index % kSigverifyNumEntriesPerOtpWord;

    std::array<uint8_t, kSigverifyNumEntriesPerOtpWord> entries;
    hardened_byte_bool_t others_val = is_valid == kHardenedByteBoolTrue
                                          ? kHardenedByteBoolFalse
                                          : kHardenedByteBoolTrue;
    entries.fill(others_val);
    entries[entry_index] = is_valid;

    uint32_t read_val;
    std::memcpy(&read_val, entries.data(), sizeof(read_val));
    EXPECT_CALL(otp_, read32(read_addr)).WillOnce(Return(read_val));
  }

  rom_test::MockOtp otp_;
  rom_test::MockRnd rnd_;
};

class BadKeyIdTypeTest : public SigverifyKeys,
                         public testing::WithParamInterface<lifecycle_state_t> {
};

TEST_P(BadKeyIdTypeTest, BadKeyId) {
  ExpectKeysGet();

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(sigverify_rsa_key_get(0, GetParam(), &key),
            kErrorSigverifyBadRsaKey);
}

INSTANTIATE_TEST_SUITE_P(AllLcStates, BadKeyIdTypeTest,
                         testing::ValuesIn(kLcStatesAll));

class BadKeyIdTypeDeathTest : public BadKeyIdTypeTest {};

TEST_P(BadKeyIdTypeDeathTest, BadKeyType) {
  const sigverify_rsa_key_t *key;

  EXPECT_DEATH(
      {
        ExpectKeysGet();
        OT_DISCARD(sigverify_rsa_key_get(0xff, GetParam(), &key));
      },
      "");
}

INSTANTIATE_TEST_SUITE_P(AllLcStates, BadKeyIdTypeDeathTest,
                         testing::ValuesIn(kLcStatesAll));

/**
 * Base class for paramaterized tests below.
 */
class KeyValidityTest : public SigverifyKeys,
                        public testing::WithParamInterface<
                            std::tuple<size_t, lifecycle_state_t>> {};

class NonOperationalStateDeathTest : public KeyValidityTest {};

TEST_P(NonOperationalStateDeathTest, BadKey) {
  size_t key_index;
  lifecycle_state_t lc_state;
  std::tie(key_index, lc_state) = GetParam();
  const sigverify_rsa_key_t *key;

  EXPECT_DEATH(
      {
        ExpectKeysGet();
        OT_DISCARD(sigverify_rsa_key_get(
            sigverify_rsa_key_id_get(&kSigverifyRsaKeys[key_index].entry.key.n),
            lc_state, &key));
      },
      "");
}

INSTANTIATE_TEST_SUITE_P(
    AllKeysAndNonOperationalStates, NonOperationalStateDeathTest,
    testing::Combine(testing::Range<size_t>(0, kSigverifyRsaKeysCnt - 1),
                     testing::Values(static_cast<lifecycle_state_t>(0))));

class ValidBasedOnOtp : public KeyValidityTest {};

TEST_P(ValidBasedOnOtp, ValidInOtp) {
  size_t key_index;
  lifecycle_state_t lc_state;
  std::tie(key_index, lc_state) = GetParam();

  ExpectKeysGet();
  ExpectOtpRead(key_index, kHardenedByteBoolTrue);
  ExpectOtpRead(key_index, kHardenedByteBoolTrue);

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(
      sigverify_rsa_key_get(
          sigverify_rsa_key_id_get(&kSigverifyRsaKeys[key_index].entry.key.n),
          lc_state, &key),
      kErrorOk);
  EXPECT_EQ(key, &kSigverifyRsaKeys[key_index].entry.key);
}

TEST_P(ValidBasedOnOtp, InvalidInOtp) {
  size_t key_index;
  lifecycle_state_t lc_state;
  std::tie(key_index, lc_state) = GetParam();

  ExpectKeysGet();
  ExpectOtpRead(key_index, kHardenedByteBoolFalse);

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(
      sigverify_rsa_key_get(
          sigverify_rsa_key_id_get(&kSigverifyRsaKeys[key_index].entry.key.n),
          lc_state, &key),
      kErrorSigverifyBadRsaKey);
}

INSTANTIATE_TEST_SUITE_P(
    ProdKeysInNonTestStates, ValidBasedOnOtp,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeProd)),
        testing::ValuesIn(kLcStatesNonTestOperational)));

INSTANTIATE_TEST_SUITE_P(
    TestKeysInRmaState, ValidBasedOnOtp,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeTest)),
        testing::Values(kLcStateRma)));

INSTANTIATE_TEST_SUITE_P(
    DevKeysInDevState, ValidBasedOnOtp,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeDev)),
        testing::Values(kLcStateDev)));

class ValidInState : public KeyValidityTest {};

TEST_P(ValidInState, Get) {
  size_t key_index;
  lifecycle_state_t lc_state;
  std::tie(key_index, lc_state) = GetParam();

  ExpectKeysGet();

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(
      sigverify_rsa_key_get(
          sigverify_rsa_key_id_get(&kSigverifyRsaKeys[key_index].entry.key.n),
          lc_state, &key),
      kErrorOk);
  EXPECT_EQ(key, &kSigverifyRsaKeys[key_index].entry.key);
}

INSTANTIATE_TEST_SUITE_P(
    ProdKeysInTestStates, ValidInState,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeProd)),
        testing::Values(kLcStateTest)));

INSTANTIATE_TEST_SUITE_P(
    TestKeysInTestStates, ValidInState,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeTest)),
        testing::Values(kLcStateTest)));

class InvalidInState : public KeyValidityTest {};

TEST_P(InvalidInState, Get) {
  size_t key_index;
  lifecycle_state_t lc_state;
  std::tie(key_index, lc_state) = GetParam();

  ExpectKeysGet();

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(
      sigverify_rsa_key_get(
          sigverify_rsa_key_id_get(&kSigverifyRsaKeys[key_index].entry.key.n),
          lc_state, &key),
      kErrorSigverifyBadRsaKey);
}

INSTANTIATE_TEST_SUITE_P(
    TestKeysAndProdDevStates, InvalidInState,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeTest)),
        testing::Values(kLcStateProd, kLcStateProdEnd, kLcStateDev)));

INSTANTIATE_TEST_SUITE_P(
    DevKeysAndTestStates, InvalidInState,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeDev)),
        testing::Values(kLcStateTest)));

INSTANTIATE_TEST_SUITE_P(
    DevKeysAndNonDevOperStates, InvalidInState,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeDev)),
        testing::Values(kLcStateProd, kLcStateProdEnd, kLcStateRma)));

}  // namespace
}  // namespace sigverify_keys_unittest
