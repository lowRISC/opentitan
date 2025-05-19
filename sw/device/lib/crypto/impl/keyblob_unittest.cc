// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/keyblob.h"

#include <array>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

namespace keyblob_unittest {
namespace {
using ::testing::ElementsAreArray;

#define EXPECT_OK(status_) EXPECT_EQ(status_.value, OTCRYPTO_OK.value)
#define EXPECT_NOT_OK(status_) EXPECT_NE(status_.value, OTCRYPTO_OK.value)

// Key configuration for testing (128-bit AES-CTR software key).
constexpr otcrypto_key_config_t kConfigCtr128 = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = 16,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (31-byte key; not valid but helps test for
// issues with keys that don't have an even word size).
constexpr otcrypto_key_config_t kConfigOddBytes = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = 31,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (key with a huge number of bytes; not valid
// but helps test for overflow).
constexpr otcrypto_key_config_t kConfigHuge = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = UINT32_MAX,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (sideloaded AES-CTR key).
constexpr otcrypto_key_config_t kConfigCtrSideloaded = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = 16,
    .hw_backed = kHardenedBoolTrue,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (sideloaded AES-OFB key).
constexpr otcrypto_key_config_t kConfigOfbSideloaded = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesOfb,
    .key_length = 16,
    .hw_backed = kHardenedBoolTrue,
    .security_level = kOtcryptoKeySecurityLevelLow,
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
  status_t err = keyblob_from_shares(test_share0.data(), test_share1.data(),
                                     kConfigCtr128, keyblob);
  EXPECT_EQ(err.value, OTCRYPTO_OK.value);

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
  uint32_t keyblob_words = keyblob_num_words(kConfigCtr128);
  uint32_t keyblob_bytes = keyblob_words * sizeof(uint32_t);
  uint32_t keyblob[keyblob_words] = {0};
  status_t err = keyblob_from_shares(test_share0.data(), test_share1.data(),
                                     kConfigCtr128, keyblob);
  EXPECT_EQ(err.value, OTCRYPTO_OK.value);

  // Construct blinded key.
  otcrypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = keyblob_bytes,
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
  uint32_t keyblob_words = keyblob_num_words(kConfigCtr128);
  uint32_t keyblob_bytes = keyblob_words * sizeof(uint32_t);
  uint32_t keyblob[keyblob_words] = {0};
  EXPECT_OK(keyblob_from_key_and_mask(test_key.data(), test_mask.data(),
                                      kConfigCtr128, keyblob));

  // Construct blinded key.
  otcrypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = keyblob_bytes,
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

TEST(Keyblob, ToKeymgrDiversificationSimple) {
  // Salt and version for the hardware-backed key.
  std::array<uint32_t, 7> test_salt = {0x01234567, 0x89abcdef, 0x00010203,
                                       0x04050607, 0x08090a0b, 0x0c0d0e0f,
                                       0xffffffff};
  uint32_t test_version = 0xdeadbeef;

  // Pack (version, salt) into a keyblob array.
  uint32_t keyblob[test_salt.size() + 1];
  keyblob[0] = test_version;
  for (size_t i = 0; i < test_salt.size(); i++) {
    keyblob[i + 1] = test_salt[i];
  }

  // Construct blinded key.
  otcrypto_blinded_key_t key = {
      .config = kConfigCtrSideloaded,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Extract the keymgr diversification data.
  keymgr_diversification_t diversification;
  EXPECT_OK(keyblob_to_keymgr_diversification(&key, &diversification));

  // Check that the version and salt match expectations.
  EXPECT_EQ(diversification.version, test_version);
  for (size_t i = 0; i < test_salt.size(); i++) {
    EXPECT_EQ(diversification.salt[i], test_salt[i]);
  }
  EXPECT_EQ(diversification.salt[test_salt.size()], key.config.key_mode);
}

TEST(Keyblob, ToKeymgrDiversificationBadlength) {
  // Salt and version for the hardware-backed keys.
  std::array<uint32_t, 6> test_salt = {0x01234567, 0x89abcdef, 0x00010203,
                                       0x04050607, 0x08090a0b, 0x0c0d0e0f};
  uint32_t test_version = 0xdeadbeef;

  // Pack (version, salt) into a keyblob array.
  uint32_t keyblob[test_salt.size() + 1];
  keyblob[0] = test_version;
  for (size_t i = 0; i < test_salt.size(); i++) {
    keyblob[i + 1] = test_salt[i];
  }

  // Construct blinded key.
  otcrypto_blinded_key_t key = {
      .config = kConfigCtrSideloaded,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Try to extract the keymgr diversification data.
  keymgr_diversification_t diversification;
  EXPECT_NOT_OK(keyblob_to_keymgr_diversification(&key, &diversification));
}

TEST(Keyblob, ToKeymgrDiversificationDifferentModes) {
  // Salt for the hardware-backed key (one word too short).
  std::array<uint32_t, 7> test_salt = {0x01234567, 0x89abcdef, 0x00010203,
                                       0x04050607, 0x08090a0b, 0x0c0d0e0f,
                                       0xffffffff};
  uint32_t test_version = 0xdeadbeef;

  // Pack (version, salt) into a keyblob array.
  uint32_t keyblob[test_salt.size() + 1];
  keyblob[0] = test_version;
  for (size_t i = 0; i < test_salt.size(); i++) {
    keyblob[i + 1] = test_salt[i];
  }

  // Construct blinded key for CTR mode.
  otcrypto_blinded_key_t key1 = {
      .config = kConfigCtrSideloaded,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Construct blinded key for OFB mode.
  otcrypto_blinded_key_t key2 = {
      .config = kConfigOfbSideloaded,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Extract the keymgr diversification data for both keys.
  keymgr_diversification_t diversification1;
  EXPECT_OK(keyblob_to_keymgr_diversification(&key1, &diversification1));
  keymgr_diversification_t diversification2;
  EXPECT_OK(keyblob_to_keymgr_diversification(&key2, &diversification2));

  // Expect different salts.
  bool salts_equal = true;
  for (size_t i = 0; i < ARRAYSIZE(diversification1.salt); i++) {
    if (diversification1.salt[i] != diversification2.salt[i]) {
      salts_equal = false;
    }
  }
  EXPECT_EQ(salts_equal, false);
}

TEST(Keyblob, RemaskDoesNotChangeKey) {
  std::array<uint32_t, 4> test_key = {0x01234567, 0x89abcdef, 0x00010203,
                                      0x04050607};
  std::array<uint32_t, 4> test_mask = {0x08090a0b, 0x0c0d0e0f, 0x10111213,
                                       0x14151617};

  // Test assumption; key and mask are the correct size.
  ASSERT_EQ(test_key.size(), keyblob_share_num_words(kConfigCtr128));
  ASSERT_EQ(test_mask.size(), keyblob_share_num_words(kConfigCtr128));

  // Convert key and initial mask to keyblob array.
  uint32_t keyblob_words = keyblob_num_words(kConfigCtr128);
  uint32_t keyblob_bytes = keyblob_words * sizeof(uint32_t);
  uint32_t keyblob[keyblob_words] = {0};
  EXPECT_OK(keyblob_from_key_and_mask(test_key.data(), test_mask.data(),
                                      kConfigCtr128, keyblob));

  // Construct blinded key.
  otcrypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = keyblob_bytes,
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Copy the keyblob for later comparison.
  uint32_t keyblob_copy[ARRAYSIZE(keyblob)];
  memcpy(keyblob_copy, keyblob, sizeof(keyblob));

  // Remask the key.
  EXPECT_OK(keyblob_remask(&key));

  // Check that every word of the keyblob changed.
  for (size_t i = 0; i < ARRAYSIZE(keyblob); i++) {
    EXPECT_NE(keyblob[i], keyblob_copy[i]);
  }

  // Unmask the key and check that it matches the original.
  uint32_t unmasked_key[test_key.size()];
  EXPECT_OK(keyblob_key_unmask(&key, test_key.size(), unmasked_key));
  EXPECT_THAT(unmasked_key, testing::ElementsAreArray(test_key));
}

TEST(Keyblob, RemaskPassesIntegrity) {
  std::array<uint32_t, 4> test_key = {0x01234567, 0x89abcdef, 0x00010203,
                                      0x04050607};
  std::array<uint32_t, 4> test_mask = {0x08090a0b, 0x0c0d0e0f, 0x10111213,
                                       0x14151617};

  // Test assumption; key and mask are the correct size.
  ASSERT_EQ(test_key.size(), keyblob_share_num_words(kConfigCtr128));
  ASSERT_EQ(test_mask.size(), keyblob_share_num_words(kConfigCtr128));

  // Convert key and initial mask to keyblob array.
  uint32_t keyblob_words = keyblob_num_words(kConfigCtr128);
  uint32_t keyblob_bytes = keyblob_words * sizeof(uint32_t);
  uint32_t keyblob[keyblob_words] = {0};
  EXPECT_OK(keyblob_from_key_and_mask(test_key.data(), test_mask.data(),
                                      kConfigCtr128, keyblob));

  // Construct blinded key.
  otcrypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = keyblob_bytes,
      .keyblob = keyblob,
      .checksum = 0,
  };

  // Copy the keyblob for later comparison.
  uint32_t keyblob_copy[ARRAYSIZE(keyblob)];
  memcpy(keyblob_copy, keyblob, sizeof(keyblob));

  // Remask the key.
  EXPECT_OK(keyblob_remask(&key));

  // Check that the integrity checksum was updated.
  EXPECT_EQ(integrity_blinded_key_check(&key), kHardenedBoolTrue);
}

}  // namespace
}  // namespace keyblob_unittest
