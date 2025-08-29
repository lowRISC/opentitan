// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "fuzztest/fuzztest.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/lib/crypto/drivers/aes.h"

namespace aes_fuzztest {
namespace {

using ::testing::_;
using ::testing::DoAll;
using ::testing::Each;
using ::testing::Return;
using ::testing::SetArgPointee;

using ::fuzztest::Arbitrary;
using ::fuzztest::ArrayOf;
using ::fuzztest::ElementOf;

using ::rom_test::NiceMockAbsMmio;

/**
 * The `aes_encrypt_begin` method has the following parameters:
 * - `const aes_key_t key`
 * - `const aes_block_t *iv`
 *
 * This test ensures that the method never crashes, regardless of input.
 */
void NeverCrashesEncryptBegin(
    const uint32_t mode, const uint32_t sideload, const uint32_t key_len,
    const std::array<uint32_t, kAesBlockNumWords> &iv_payload,
    const std::array<uint32_t, 4> &share0_payload,
    const std::array<uint32_t, 4> &share1_payload) {
  // Required Data

  uint32_t share0[8];
  memcpy(share0, share0_payload.data(), sizeof(share0));

  uint32_t share1[8];
  memcpy(share1, share1_payload.data(), sizeof(share1));

  aes_key_t key = {
      .mode = (aes_cipher_mode_t)mode,
      .sideload = (hardened_bool_t)sideload,
      .key_len = key_len,
      .key_shares = {share0, share1},
  };

  aes_block_t iv;
  memcpy(iv.data, iv_payload.data(), sizeof(iv.data));

  NiceMockAbsMmio abs_mmio_;

  // Execute Function

  [[maybe_unused]] status_t status = aes_encrypt_begin(key, &iv);
}

/**
 * The `aes_decrypt_begin` method has the following parameters:
 * - `const aes_key_t key`
 * - `const aes_block_t *iv`
 *
 * This test ensures that the method never crashes, regardless of input.
 */
void NeverCrashesDecryptBegin(
    const uint32_t mode, const uint32_t sideload, const uint32_t key_len,
    const std::array<uint32_t, kAesBlockNumWords> &iv_payload,
    const std::array<uint32_t, 4> &share0_payload,
    const std::array<uint32_t, 4> &share1_payload) {
  // Required Data

  uint32_t share0[8];
  memcpy(share0, share0_payload.data(), sizeof(share0));

  uint32_t share1[8];
  memcpy(share1, share1_payload.data(), sizeof(share1));

  aes_key_t key = {
      .mode = (aes_cipher_mode_t)mode,
      .sideload = (hardened_bool_t)sideload,
      .key_len = key_len,
      .key_shares = {share0, share1},
  };

  aes_block_t iv;
  memcpy(iv.data, iv_payload.data(), sizeof(iv.data));

  NiceMockAbsMmio abs_mmio_;

  // Execute Function

  [[maybe_unused]] status_t status = aes_decrypt_begin(key, &iv);
}

FUZZ_TEST(AesDriverFuzzTest, NeverCrashesEncryptBegin)
    .WithDomains(Arbitrary<uint32_t>(), Arbitrary<uint32_t>(),
                 Arbitrary<uint32_t>(),
                 ArrayOf<kAesBlockNumWords>(Arbitrary<uint32_t>()),
                 ArrayOf<4>(Arbitrary<uint32_t>()),
                 ArrayOf<4>(Arbitrary<uint32_t>()));
FUZZ_TEST(AesDriverFuzzTest, NeverCrashesDecryptBegin)
    .WithDomains(Arbitrary<uint32_t>(), Arbitrary<uint32_t>(),
                 Arbitrary<uint32_t>(),
                 ArrayOf<kAesBlockNumWords>(Arbitrary<uint32_t>()),
                 ArrayOf<4>(Arbitrary<uint32_t>()),
                 ArrayOf<4>(Arbitrary<uint32_t>()));
}  // namespace
}  // namespace aes_fuzztest
