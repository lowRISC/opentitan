// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/integrity.h"

#include <array>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/crypto/include/datatypes.h"

namespace integrity_unittest {
namespace {

constexpr otcrypto_key_config_t kValidConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = 128 / 8,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolTrue,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

TEST(IntegrityTest, UnblindedKeyValid) {
  std::array<uint32_t, 4> key_data = {0x01020304, 0x05060708, 0x090a0b0c,
                                      0x0d0e0f00};
  otcrypto_unblinded_key_t key = {
      .key_mode = kOtcryptoKeyModeAesCtr,
      .key_length = static_cast<uint32_t>(key_data.size() * sizeof(uint32_t)),
      .key = key_data.data(),
  };
  key.checksum = integrity_unblinded_checksum(&key);

  EXPECT_EQ(integrity_unblinded_key_check(&key), kHardenedBoolTrue);
}

TEST(IntegrityTest, UnblindedKeyCorruptedData) {
  std::array<uint32_t, 4> key_data = {0x01020304, 0x05060708, 0x090a0b0c,
                                      0x0d0e0f00};
  otcrypto_unblinded_key_t key = {
      .key_mode = kOtcryptoKeyModeAesCtr,
      .key_length = static_cast<uint32_t>(key_data.size() * sizeof(uint32_t)),
      .key = key_data.data(),
  };
  key.checksum = integrity_unblinded_checksum(&key);

  key_data[0] ^= 0xFFFFFFFF;
  EXPECT_EQ(integrity_unblinded_key_check(&key), kHardenedBoolFalse);
}

TEST(IntegrityTest, BlindedKeyValid) {
  std::array<uint32_t, 8> keyblob = {0x11111111, 0x22222222, 0x33333333,
                                     0x44444444};
  otcrypto_blinded_key_t key = {
      .config = kValidConfig,
      .keyblob_length =
          static_cast<uint32_t>(keyblob.size() * sizeof(uint32_t)),
      .keyblob = keyblob.data(),
  };

  key.checksum = integrity_blinded_checksum(&key);

  EXPECT_EQ(integrity_blinded_key_check(&key), kHardenedBoolTrue);
}

TEST(IntegrityTest, BlindedKeyCorruptedConfig) {
  std::array<uint32_t, 8> keyblob = {0x11111111, 0x22222222, 0x33333333,
                                     0x44444444};

  otcrypto_blinded_key_t valid_key = {
      .config = kValidConfig,
      .keyblob_length =
          static_cast<uint32_t>(keyblob.size() * sizeof(uint32_t)),
      .keyblob = keyblob.data(),
  };
  uint32_t original_checksum = integrity_blinded_checksum(&valid_key);

  otcrypto_key_config_t bad_config = kValidConfig;
  bad_config.security_level = kOtcryptoKeySecurityLevelHigh;

  otcrypto_blinded_key_t bad_key = {
      .config = bad_config,
      .keyblob_length = valid_key.keyblob_length,
      .keyblob = keyblob.data(),
  };
  bad_key.checksum = original_checksum;

  EXPECT_EQ(integrity_blinded_key_check(&bad_key), kHardenedBoolFalse);
}

TEST(IntegrityTest, BlindedKeyDowngradeProtection) {
  std::array<uint32_t, 8> keyblob = {0x11111111, 0x22222222, 0x33333333,
                                     0x44444444};

  otcrypto_key_config_t downgrade_config = kValidConfig;
  downgrade_config.version = static_cast<otcrypto_lib_version_t>(0);

  otcrypto_blinded_key_t key = {
      .config = downgrade_config,
      .keyblob_length =
          static_cast<uint32_t>(keyblob.size() * sizeof(uint32_t)),
      .keyblob = keyblob.data(),
  };

  key.checksum = integrity_blinded_checksum(&key);

  EXPECT_EQ(integrity_blinded_key_check(&key), kHardenedBoolFalse);
}

TEST(IntegrityTest, BufferCreationAndCheck) {
  std::array<uint8_t, 16> data = {0};

  otcrypto_byte_buf_t buf = otcrypto_make_byte_buf(data.data(), data.size());

  EXPECT_EQ(otcrypto_check_byte_buf(&buf), kHardenedBoolTrue);

  buf.len = data.size() + 1;

  EXPECT_EQ(otcrypto_check_byte_buf(&buf), kHardenedBoolFalse);
}

}  // namespace
}  // namespace integrity_unittest
