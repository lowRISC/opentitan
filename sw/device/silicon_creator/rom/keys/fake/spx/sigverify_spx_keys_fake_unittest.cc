// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <unordered_set>

#include "sw/device/silicon_creator/rom/sigverify_keys_spx.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace sigverify_spx_keys_fake_unittest {
namespace {
using ::testing::Return;

TEST(Keys, UniqueIds) {
  std::unordered_set<uint32_t> ids;
  for (size_t i = 0; i < kSigverifySpxKeysCnt; ++i) {
    ids.insert(sigverify_spx_key_id_get(&kSigverifySpxKeys[i].entry.key));
  }

  EXPECT_EQ(ids.size(), kSigverifySpxKeysCnt);
}

/**
 * An implementation of the Euclidean algorithm since we can't use c++17's
 * `std::gcd()` yet.
 */
uint32_t Gcd(uint32_t a, uint32_t b) {
  while (b != 0) {
    std::tie(a, b) = std::make_tuple(b, a % b);
  }
  return a;
}

TEST(KeysStep, IsCorrect) {
  if (kSigverifySpxKeysCnt > 1) {
    EXPECT_LT(kSigverifySpxKeysStep, kSigverifySpxKeysCnt);
    EXPECT_EQ(Gcd(kSigverifySpxKeysStep, kSigverifySpxKeysCnt), 1);
  }
}

// TODO: Add a test for each key

}  // namespace
}  // namespace sigverify_spx_keys_fake_unittest
