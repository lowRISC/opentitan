// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/keyblob.h"

#include <array>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

namespace keyblob_unittest {
namespace {
using ::testing::ElementsAreArray;

#define EXPECT_OK(status_) EXPECT_EQ(status_.value, OTCRYPTO_OK.value)

// Key configuration for testing (128-bit AES-CTR software key).
constexpr crypto_key_config_t kConfigCtr128 = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeAesCtr,
    .key_length = 16,
    .hw_backed = kHardenedBoolFalse,
    .diversification_hw_backed = {.data = NULL, .len = 0},
    .security_level = kSecurityLevelLow,
};

// Key configuration for testing (31-byte key; not valid but helps test for
// issues with keys that don't have an even word size).
constexpr crypto_key_config_t kConfigOddBytes = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeAesCtr,
    .key_length = 31,
    .hw_backed = kHardenedBoolFalse,
    .diversification_hw_backed = {.data = NULL, .len = 0},
    .security_level = kSecurityLevelLow,
};

// Key configuration for testing (key with a huge number of bytes; not valid
// but helps test for overflow).
constexpr crypto_key_config_t kConfigHuge = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeAesCtr,
    .key_length = SIZE_MAX,
    .hw_backed = kHardenedBoolFalse,
    .diversification_hw_backed = {.data = NULL, .len = 0},
    .security_level = kSecurityLevelLow,
};

TEST(Keyblob, ShareNumWordsSimpleTest) {
  size_t share_words = keyblob_share_num_words(kConfigCtr128);
  EXPECT_GE(share_words * sizeof(uint32_t), kConfigCtr128.key_length);
  EXPECT_LT((share_words - 1) * sizeof(uint32_t), kConfigCtr128.key_length);
}

TEST(Keyblob, ShareNumWordsOdd) {
  size_t share_words = keyblob_share_num_words(kConfigOddBytes);
  EXPECT_GE(share_words * sizeof(uint32_t), kConfigOddBytes.key_length);
  EXPECT_LT((share_words - 1) * sizeof(uint32_t), kConfigOddBytes.key_length);
}

TEST(Keyblob, ShareNumWordsHuge) {
  size_t share_words = keyblob_share_num_words(kConfigHuge);
  EXPECT_GE(share_words, kConfigHuge.key_length / sizeof(uint32_t));
  EXPECT_LT((share_words - 1) * sizeof(uint32_t), kConfigHuge.key_length);
}

TEST(Keyblob, KeyblobNumWordsSimpleTest) {
  EXPECT_EQ(keyblob_num_words(kConfigCtr128),
            2 * keyblob_share_num_words(kConfigCtr128));
}

TEST(Keyblob, KeyblobNumWordsOdd) {
  EXPECT_EQ(keyblob_num_words(kConfigOddBytes),
            2 * keyblob_share_num_words(kConfigOddBytes));
}

TEST(Keyblob, KeyblobNumWordsHuge) {
  EXPECT_EQ(keyblob_num_words(kConfigHuge),
            2 * keyblob_share_num_words(kConfigHuge));
}

TEST(Keyblob, FromSharesSimpleTest) {
  std::array<uint32_t, 4> test_share0 = {0x01234567, 0x89abcdef, 0x00010203,
                                         0x04050607};
  std::array<uint32_t, 4> test_share1 = {0x08090a0b, 0x0c0d0e0f, 0x10111213,
                                         0x14151617};

  // Test assumption; shares are the correct size.
  ASSERT_EQ(test_share0.size(), keyblob_share_num_words(kConfigCtr128));
  ASSERT_EQ(test_share1.size(), keyblob_share_num_words(kConfigCtr128));

  // Convert shares to keyblob array.
  size_t keyblob_words = keyblob_num_words(kConfigCtr128);
  EXPECT_THAT(keyblob_share_num_words(kConfigCtr128), 4);
  uint32_t keyblob[keyblob_words] = {0};
  keyblob_from_shares(test_share0.data(), test_share1.data(), kConfigCtr128,
                      keyblob);

  // Check that keyblob is both shares concatenated.
  for (size_t i = 0; i < test_share0.size(); i++) {
    EXPECT_EQ(keyblob[i], test_share0[i]);
  }
  for (size_t i = 0; i < test_share1.size(); i++) {
    EXPECT_EQ(keyblob[test_share0.size() + i], test_share1[i]);
  }
}

TEST(Keyblob, FromToSharesNoop) {
  std::array<uint32_t, 4> test_share0 = {0x01234567, 0x89abcdef, 0x00010203,
                                         0x04050607};
  std::array<uint32_t, 4> test_share1 = {0x08090a0b, 0x0c0d0e0f, 0x10111213,
                                         0x14151617};

  // Test assumption; shares are the correct size.
  ASSERT_EQ(test_share0.size(), keyblob_share_num_words(kConfigCtr128));
  ASSERT_EQ(test_share1.size(), keyblob_share_num_words(kConfigCtr128));

  // Convert shares to keyblob array.
  size_t keyblob_words = keyblob_num_words(kConfigCtr128);
  uint32_t keyblob[keyblob_words] = {0};
  keyblob_from_shares(test_share0.data(), test_share1.data(), kConfigCtr128,
                      keyblob);

  // Construct blinded key.
  crypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Retrieve pointers to each share.
  uint32_t *share0;
  uint32_t *share1;
  EXPECT_OK(keyblob_to_shares(&key, &share0, &share1));

  // Check share values match original data.
  for (size_t i = 0; i < test_share0.size(); i++) {
    EXPECT_EQ(share0[i], test_share0[i]);
  }
  for (size_t i = 0; i < test_share1.size(); i++) {
    EXPECT_EQ(share1[i], test_share1[i]);
  }
}

TEST(Keyblob, FromKeyMaskDoesNotChangeKey) {
  std::array<uint32_t, 4> test_key = {0x01234567, 0x89abcdef, 0x00010203,
                                      0x04050607};
  std::array<uint32_t, 4> test_mask = {0x08090a0b, 0x0c0d0e0f, 0x10111213,
                                       0x14151617};

  // Test assumption; key and mask are the correct size.
  ASSERT_EQ(test_key.size(), keyblob_share_num_words(kConfigCtr128));
  ASSERT_EQ(test_mask.size(), keyblob_share_num_words(kConfigCtr128));

  // Convert key/mask to keyblob array.
  size_t keyblob_words = keyblob_num_words(kConfigCtr128);
  uint32_t keyblob[keyblob_words] = {0};
  EXPECT_OK(keyblob_from_key_and_mask(test_key.data(), test_mask.data(),
                                      kConfigCtr128, keyblob));

  // Construct blinded key.
  crypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Retrieve pointers to each share.
  uint32_t *share0;
  uint32_t *share1;
  EXPECT_OK(keyblob_to_shares(&key, &share0, &share1));

  // Unmask the key and check that it matches the original.
  for (size_t i = 0; i < test_key.size(); i++) {
    uint32_t share0 = keyblob[i];
    uint32_t share1 = keyblob[test_key.size() + i];
    EXPECT_EQ(share1, test_mask[i]);
    EXPECT_EQ(share0 ^ share1, test_key[i]);
  }
}

TEST(Keyblob, RemaskDoesNotChangKey) {
  std::array<uint32_t, 4> test_key = {0x01234567, 0x89abcdef, 0x00010203,
                                      0x04050607};
  std::array<uint32_t, 4> test_mask0 = {0x08090a0b, 0x0c0d0e0f, 0x10111213,
                                        0x14151617};
  std::array<uint32_t, 4> test_mask1 = {0x18191a1b, 0x1c1d1e1f, 0x20212223,
                                        0x24252627};

  // Test assumption; key and masks are the correct size.
  ASSERT_EQ(test_key.size(), keyblob_share_num_words(kConfigCtr128));
  ASSERT_EQ(test_mask0.size(), keyblob_share_num_words(kConfigCtr128));
  ASSERT_EQ(test_mask1.size(), keyblob_share_num_words(kConfigCtr128));

  // Convert key and first mask to keyblob array.
  size_t keyblob_words = keyblob_num_words(kConfigCtr128);
  uint32_t keyblob[keyblob_words] = {0};
  EXPECT_OK(keyblob_from_key_and_mask(test_key.data(), test_mask0.data(),
                                      kConfigCtr128, keyblob));

  // Construct blinded key.
  crypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Remask the key using the second mask.
  EXPECT_OK(keyblob_remask(&key, test_mask1.data()));

  // Retrieve pointers to each share.
  uint32_t *share0;
  uint32_t *share1;
  EXPECT_OK(keyblob_to_shares(&key, &share0, &share1));

  // Unmask the key and check that it matches the original.
  for (size_t i = 0; i < test_key.size(); i++) {
    uint32_t share0 = keyblob[i];
    uint32_t share1 = keyblob[test_key.size() + i];
    EXPECT_EQ(share1, test_mask0[i] ^ test_mask1[i]);
    EXPECT_EQ(share0 ^ share1, test_key[i]);
  }
}

TEST(Keyblob, RemaskWithZero) {
  std::array<uint32_t, 4> test_key = {0x01234567, 0x89abcdef, 0x00010203,
                                      0x04050607};
  std::array<uint32_t, 4> test_mask0 = {0x08090a0b, 0x0c0d0e0f, 0x10111213,
                                        0x14151617};
  std::array<uint32_t, 4> test_mask1 = {0x18191a1b, 0x1c1d1e1f, 0x20212223,
                                        0x24252627};

  // Test assumption; key and masks are the correct size.
  ASSERT_EQ(test_key.size(), keyblob_share_num_words(kConfigCtr128));
  ASSERT_EQ(test_mask0.size(), keyblob_share_num_words(kConfigCtr128));
  ASSERT_EQ(test_mask1.size(), keyblob_share_num_words(kConfigCtr128));

  // Convert key and first mask to keyblob array.
  size_t keyblob_words = keyblob_num_words(kConfigCtr128);
  uint32_t keyblob[keyblob_words] = {0};
  EXPECT_OK(keyblob_from_key_and_mask(test_key.data(), test_mask0.data(),
                                      kConfigCtr128, keyblob));

  // Construct blinded key.
  crypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Remask the key using the second mask.
  EXPECT_OK(keyblob_remask(&key, test_mask1.data()));

  // Retrieve pointers to each share.
  uint32_t *share0;
  uint32_t *share1;
  EXPECT_OK(keyblob_to_shares(&key, &share0, &share1));

  // Unmask the key and check that it matches the original.
  for (size_t i = 0; i < test_key.size(); i++) {
    uint32_t share0 = keyblob[i];
    uint32_t share1 = keyblob[test_key.size() + i];
    EXPECT_EQ(share1, test_mask0[i] ^ test_mask1[i]);
    EXPECT_EQ(share0 ^ share1, test_key[i]);
  }
}

}  // namespace
}  // namespace keyblob_unittest
