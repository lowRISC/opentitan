// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/sigverify_keys.h"

#include <array>
#include <cstring>
#include <limits>
#include <numeric>
#include <unordered_set>

#include "gtest/gtest.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

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
constexpr sigverify_rom_ext_key_t kSigverifyRsaKeys[]{
    {
        .key = {.n = {{0xa0}}, .n0_inv = {0}},
        .key_type = kSigverifyKeyTypeFirmwareTest,
    },
    {
        .key = {.n = {{0xb0}}, .n0_inv = {0}},
        .key_type = kSigverifyKeyTypeFirmwareProd,
    },
    {
        .key = {.n = {{0xc0}}, .n0_inv = {0}},
        .key_type = kSigverifyKeyTypeFirmwareDev,
    },
    {
        .key = {.n = {{0xa1}}, .n0_inv = {0}},
        .key_type = kSigverifyKeyTypeFirmwareTest,
    },
    {
        .key = {.n = {{0xb1}}, .n0_inv = {0}},
        .key_type = kSigverifyKeyTypeFirmwareProd,
    },
    {
        .key = {.n = {{0xc1}}, .n0_inv = {0}},
        .key_type = kSigverifyKeyTypeFirmwareDev,
    },
    {
        .key = {.n = {{0xff}}, .n0_inv = {0}},
        .key_type = static_cast<sigverify_key_type_t>(
            std::numeric_limits<uint32_t>::max()),
    },
};

constexpr size_t kSigverifyRsaKeysCnt =
    std::extent<decltype(kSigverifyRsaKeys)>::value;
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
    if (kSigverifyRsaKeys[i].key_type == key_type) {
      indices.push_back(i);
    }
  }
  return indices;
}

class SigverifyKeys : public rom_test::RomTest {
 protected:
  /**
   * Sets expectations for getting the keys stored in the ROM.
   */
  void ExpectKeysGet() {
    EXPECT_CALL(rnd_, Uint32())
        .WillOnce(Return(std::numeric_limits<uint32_t>::max()));
  }

  rom_test::MockRnd rnd_;
};

class BadKeyIdTypeTest : public SigverifyKeys {};

TEST_F(BadKeyIdTypeTest, BadKeyId) {
  ExpectKeysGet();

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(sigverify_rsa_key_get(0, &key), kErrorSigverifyBadKey);
}

class BadKeyIdTypeDeathTest : public BadKeyIdTypeTest {};

TEST_F(BadKeyIdTypeDeathTest, BadKeyType) {
  const sigverify_rsa_key_t *key;

  EXPECT_DEATH(
      {
        ExpectKeysGet();
        sigverify_rsa_key_get(0xff, &key);
      },
      "");
}

/**
 * Base class for paramaterized tests below.
 */
class KeyValidityTest : public SigverifyKeys,
                        public testing::WithParamInterface<size_t> {};

TEST_P(KeyValidityTest, Get) {
  size_t key_index = GetParam();

  ExpectKeysGet();

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(
      sigverify_rsa_key_get(
          sigverify_rsa_key_id_get(&kSigverifyRsaKeys[key_index].key.n), &key),
      kErrorOk);
  EXPECT_EQ(key, &kSigverifyRsaKeys[key_index].key);
}

INSTANTIATE_TEST_SUITE_P(
    FirmwareProdKeys, KeyValidityTest,
    testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeFirmwareProd)));

INSTANTIATE_TEST_SUITE_P(
    FirmwareTestKeys, KeyValidityTest,
    testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeFirmwareTest)));

INSTANTIATE_TEST_SUITE_P(
    FirmwareDevKeys, KeyValidityTest,
    testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeFirmwareDev)));

}  // namespace
}  // namespace sigverify_keys_unittest
