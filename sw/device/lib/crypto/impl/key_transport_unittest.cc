// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/key_transport.h"

#include <array>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

namespace key_transport_unittest {
namespace {
using ::testing::ElementsAreArray;

// Key configuration for testing (128-bit AES-CTR hardware-backed key).
constexpr crypto_key_config_t kConfigCtr128 = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeAesCtr,
    .key_length = 128 / 8,
    .hw_backed = kHardenedBoolTrue,
    .security_level = kSecurityLevelLow,
};

// Invalid RSA key configuration for testing (sideloaded RSA-2048 key).
constexpr crypto_key_config_t kConfigRsaInvalid = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeRsaSignPkcs,
    .key_length = 2048 / 8,
    .hw_backed = kHardenedBoolTrue,
    .security_level = kSecurityLevelLow,
};

TEST(Keyblob, HwBackedKeyToDiversificationData) {
  uint32_t test_version = 0xf0f1f2f3;
  std::array<uint32_t, 7> test_salt = {0x01234567, 0x89abcdef, 0x00010203,
                                       0x04050607, 0x08090a0b, 0x0c0d0e0f,
                                       0x10111213};

  // Create a key handle from the test data.
  uint32_t keyblob[32] = {0};
  crypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = 32,
      .keyblob = keyblob,
  };
  EXPECT_EQ(
      status_ok(otcrypto_hw_backed_key(test_version, test_salt.data(), &key)),
      true);

  // Expect that converting to keymgr diversification data generates the same
  // version and salt.
  keymgr_diversification_t diversification;
  EXPECT_EQ(
      status_ok(keyblob_to_keymgr_diversification(&key, &diversification)),
      true);
  EXPECT_EQ(diversification.version, test_version);
  for (size_t i = 0; i < kKeymgrSaltNumWords - 1; i++) {
    EXPECT_EQ(diversification.salt[i], test_salt[i]);
  }
  EXPECT_EQ(diversification.salt[kKeymgrSaltNumWords - 1],
            kConfigCtr128.key_mode);
}

TEST(Keyblob, HwBackedRsaKeyFails) {
  uint32_t test_version = 0xf0f1f2f3;
  std::array<uint32_t, 7> test_salt = {0x01234567, 0x89abcdef, 0x00010203,
                                       0x04050607, 0x08090a0b, 0x0c0d0e0f,
                                       0x10111213};

  // Create a key handle from the test data.
  uint32_t keyblob[32] = {0};
  crypto_blinded_key_t key = {
      .config = kConfigRsaInvalid,
      .keyblob_length = 32,
      .keyblob = keyblob,
  };

  // Expect the hardware-backed RSA key to be rejected.
  EXPECT_EQ(
      status_ok(otcrypto_hw_backed_key(test_version, test_salt.data(), &key)),
      false);
}

}  // namespace
}  // namespace key_transport_unittest
