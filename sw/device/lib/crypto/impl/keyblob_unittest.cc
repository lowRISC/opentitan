// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/keyblob.h"

#include <array>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"

namespace keyblob_unittest {
namespace {
using ::testing::ElementsAreArray;

#define EXPECT_OK(status_) EXPECT_EQ(status_.value, OTCRYPTO_OK.value)
#define EXPECT_NOT_OK(status_) EXPECT_NE(status_.value, OTCRYPTO_OK.value)

// Define a keymgr_dpe source slot common for all tests
const uint32_t kKeymgrDpeSrcSlot = 3;

// Key configuration for testing (128-bit AES-CTR software key).
const otcrypto_key_config_t kConfigCtr128 = {
    .version = otcrypto_lib_version(),
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = 16,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (RSA 2048).
const otcrypto_key_config_t kConfigRsa2048 = {
    .version = otcrypto_lib_version(),
    .key_mode = kOtcryptoKeyModeRsaSignPkcs,
    .key_length = 256,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (ECC P256).
const otcrypto_key_config_t kConfigEcdsaP256 = {
    .version = otcrypto_lib_version(),
    .key_mode = kOtcryptoKeyModeEcdsaP256,
    .key_length = 32,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (31-byte HMAC key; tests keys that don't have
// an even word size).
const otcrypto_key_config_t kConfigOddBytes = {
    .version = otcrypto_lib_version(),
    .key_mode = kOtcryptoKeyModeHmacSha256,
    .key_length = 31,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (HMAC key with a huge number of bytes; not
// valid but helps test for overflow).
const otcrypto_key_config_t kConfigHuge = {
    .version = otcrypto_lib_version(),
    .key_mode = kOtcryptoKeyModeHmacSha256,
    .key_length = UINT32_MAX,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (sideloaded AES-CTR key).
const otcrypto_key_config_t kConfigCtrSideloaded = {
    .version = otcrypto_lib_version(),
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = 32,
    .hw_backed = kHardenedBoolTrue,
    .keymgr_dpe_slot_idx = kKeymgrDpeSrcSlot,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (sideloaded AES-OFB key).
const otcrypto_key_config_t kConfigOfbSideloaded = {
    .version = otcrypto_lib_version(),
    .key_mode = kOtcryptoKeyModeAesOfb,
    .key_length = 32,
    .hw_backed = kHardenedBoolTrue,
    .keymgr_dpe_slot_idx = kKeymgrDpeSrcSlot,
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

TEST(Keyblob, ShareNumWordsOddNonHmacRejected) {
  otcrypto_key_config_t odd_aes = kConfigCtr128;
  odd_aes.key_length = 31;
  EXPECT_EQ(keyblob_share_num_words(odd_aes), 0);

  // Sideloaded symmetric keys not equal to 256 bits (32 bytes) must return 0.
  otcrypto_key_config_t bad_sideload = kConfigCtrSideloaded;
  bad_sideload.key_length = 16;
  EXPECT_EQ(keyblob_share_num_words(bad_sideload), 0);
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
  std::vector<uint32_t> keyblob(keyblob_words, 0);
  status_t err = keyblob_from_shares(test_share0.data(), test_share1.data(),
                                     kConfigCtr128, keyblob.data());
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
  std::vector<uint32_t> keyblob(keyblob_words, 0);
  status_t err = keyblob_from_shares(test_share0.data(), test_share1.data(),
                                     kConfigCtr128, keyblob.data());
  EXPECT_EQ(err.value, OTCRYPTO_OK.value);

  // Construct blinded key.
  otcrypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = keyblob_bytes,
      .keyblob = keyblob.data(),
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

TEST(Keyblob, ToSharesFailsForHwBackedKey) {
  uint32_t keyblob[8] = {0};
  otcrypto_blinded_key_t key = {
      .config = kConfigCtrSideloaded,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };

  uint32_t *share0;
  uint32_t *share1;
  EXPECT_NOT_OK(keyblob_to_shares(&key, &share0, &share1));
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
  std::vector<uint32_t> keyblob(keyblob_words, 0);
  EXPECT_OK(keyblob_from_key_and_mask(test_key.data(), test_mask.data(),
                                      kConfigCtr128, keyblob.data()));

  // Construct blinded key.
  otcrypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = keyblob_bytes,
      .keyblob = keyblob.data(),
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

TEST(Keyblob, ToKeymgrDpeDiversificationSimple) {
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
  keymgr_dpe_diversification_t diversification;
  EXPECT_OK(keyblob_to_keymgr_dpe_diversification(&key, &diversification));

  // Check that the version and salt match expectations.
  EXPECT_EQ(diversification.version, test_version);
  for (size_t i = 0; i < test_salt.size(); i++) {
    EXPECT_EQ(diversification.salt[i], test_salt[i]);
  }
  EXPECT_EQ(diversification.salt[test_salt.size()], key.config.key_mode);
  EXPECT_EQ(diversification.slot_src_sel, kKeymgrDpeSrcSlot);
}

TEST(Keyblob, ToKeymgrDpeDiversificationBadlength) {
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
  keymgr_dpe_diversification_t diversification;
  EXPECT_NOT_OK(keyblob_to_keymgr_dpe_diversification(&key, &diversification));
}

TEST(Keyblob, ToKeymgrDpeDiversificationDifferentModes) {
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
  keymgr_dpe_diversification_t diversification1;
  EXPECT_OK(keyblob_to_keymgr_dpe_diversification(&key1, &diversification1));
  keymgr_dpe_diversification_t diversification2;
  EXPECT_OK(keyblob_to_keymgr_dpe_diversification(&key2, &diversification2));

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
  std::vector<uint32_t> keyblob(keyblob_words, 0);
  EXPECT_OK(keyblob_from_key_and_mask(test_key.data(), test_mask.data(),
                                      kConfigCtr128, keyblob.data()));

  // Construct blinded key.
  otcrypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = keyblob_bytes,
      .keyblob = keyblob.data(),
      .checksum = 0,
  };

  // Copy the keyblob for later comparison.
  std::vector<uint32_t> keyblob_copy = keyblob;

  // Remask the key.
  EXPECT_OK(keyblob_remask(&key));

  // Check that every word of the keyblob changed.
  for (size_t i = 0; i < keyblob.size(); i++) {
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
  std::vector<uint32_t> keyblob(keyblob_words, 0);
  EXPECT_OK(keyblob_from_key_and_mask(test_key.data(), test_mask.data(),
                                      kConfigCtr128, keyblob.data()));

  // Construct blinded key.
  otcrypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = keyblob_bytes,
      .keyblob = keyblob.data(),
      .checksum = 0,
  };

  // Remask the key.
  EXPECT_OK(keyblob_remask(&key));

  // Check that the integrity checksum was updated.
  EXPECT_EQ(otcrypto_integrity_blinded_key_check(&key), kHardenedBoolTrue);
}

TEST(Keyblob, ShareNumWordsRsa) {
  size_t share_words = keyblob_share_num_words(kConfigRsa2048);
  EXPECT_EQ(share_words, kConfigRsa2048.key_length / sizeof(uint32_t));
}

TEST(Keyblob, KeyblobNumWordsRsa) {
  const otcrypto_key_config_t kConfigRsa3072 = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeRsaSignPss,
      .key_length = 384,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  const otcrypto_key_config_t kConfigRsa4096 = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
      .key_length = 512,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // RSA private keyblobs store d0, d1, n, and a 32-bit checksum.
  EXPECT_EQ(keyblob_num_words(kConfigRsa2048),
            3 * (256 / sizeof(uint32_t)) + 1);
  EXPECT_EQ(keyblob_num_words(kConfigRsa2048) * sizeof(uint32_t), 772);
  EXPECT_EQ(keyblob_num_words(kConfigRsa3072),
            3 * (384 / sizeof(uint32_t)) + 1);
  EXPECT_EQ(keyblob_num_words(kConfigRsa3072) * sizeof(uint32_t), 1156);
  EXPECT_EQ(keyblob_num_words(kConfigRsa4096),
            3 * (512 / sizeof(uint32_t)) + 1);
  EXPECT_EQ(keyblob_num_words(kConfigRsa4096) * sizeof(uint32_t), 1540);
}

TEST(Keyblob, ToSharesRsa) {
  size_t keyblob_words = keyblob_num_words(kConfigRsa2048);
  std::vector<uint32_t> keyblob(keyblob_words, 0);
  otcrypto_blinded_key_t key = {
      .config = kConfigRsa2048,
      .keyblob_length = static_cast<uint32_t>(keyblob_words * sizeof(uint32_t)),
      .keyblob = keyblob.data(),
      .checksum = 0,
  };

  uint32_t *share0 = nullptr;
  uint32_t *share1 = nullptr;
  EXPECT_OK(keyblob_to_shares(&key, &share0, &share1));
  EXPECT_EQ(share0, keyblob.data());
  EXPECT_EQ(share1, keyblob.data() + keyblob_share_num_words(kConfigRsa2048));

  // Old wrong keyblob length (2 * key_length = 512 bytes) must be rejected.
  otcrypto_blinded_key_t bad_key = {
      .config = kConfigRsa2048,
      .keyblob_length = 512,
      .keyblob = keyblob.data(),
      .checksum = 0,
  };
  EXPECT_NOT_OK(keyblob_to_shares(&bad_key, &share0, &share1));
}

TEST(Keyblob, ToKeymgrDpeDiversificationNegative) {
  keymgr_dpe_diversification_t div;
  uint32_t keyblob[8] = {0};

  // hw_backed is false
  otcrypto_blinded_key_t key_not_hw_backed = {
      .config = kConfigCtr128,
      .keyblob_length = 32,  // Assumes kKeyblobHwBackedBytes == 32
      .keyblob = keyblob,
      .checksum = 0,
  };
  EXPECT_NOT_OK(
      keyblob_to_keymgr_dpe_diversification(&key_not_hw_backed, &div));
  EXPECT_NOT_OK(keyblob_to_keymgr_dpe_attestation_diversification(
      &key_not_hw_backed, &div));

  // keyblob is NULL
  otcrypto_blinded_key_t key_null_blob = {
      .config = kConfigCtrSideloaded,
      .keyblob_length = 32,
      .keyblob = nullptr,
      .checksum = 0,
  };
  EXPECT_NOT_OK(keyblob_to_keymgr_dpe_diversification(&key_null_blob, &div));
  EXPECT_NOT_OK(
      keyblob_to_keymgr_dpe_attestation_diversification(&key_null_blob, &div));

  // Bad keyblob_length
  otcrypto_blinded_key_t key_bad_length = {
      .config = kConfigCtrSideloaded,
      .keyblob_length = 99,
      .keyblob = keyblob,
      .checksum = 0,
  };
  EXPECT_NOT_OK(keyblob_to_keymgr_dpe_diversification(&key_bad_length, &div));
  EXPECT_NOT_OK(
      keyblob_to_keymgr_dpe_attestation_diversification(&key_bad_length, &div));
}

TEST(Keyblob, EnsureXorMaskedNegative) {
  uint32_t key_data[64] = {0};
  uint32_t mask_data[64] = {0};
  uint32_t keyblob_buf[128] = {0};

  // ECC key
  EXPECT_NOT_OK(keyblob_from_key_and_mask(key_data, mask_data, kConfigEcdsaP256,
                                          keyblob_buf));

  // RSA key
  EXPECT_NOT_OK(keyblob_from_key_and_mask(key_data, mask_data, kConfigRsa2048,
                                          keyblob_buf));

  // HW backed
  EXPECT_NOT_OK(keyblob_from_key_and_mask(key_data, mask_data,
                                          kConfigCtrSideloaded, keyblob_buf));

  // Invalid / Unrecognized mode
  otcrypto_key_config_t bad_config = kConfigCtr128;
  bad_config.key_mode = static_cast<otcrypto_key_mode_t>(0xFFFFFFFF);
  EXPECT_NOT_OK(
      keyblob_from_key_and_mask(key_data, mask_data, bad_config, keyblob_buf));
}

TEST(Keyblob, KeyUnmaskNegative) {
  uint32_t keyblob_buf[8] = {0};
  otcrypto_blinded_key_t key = {
      .config = kConfigCtr128,
      .keyblob_length = sizeof(keyblob_buf),
      .keyblob = keyblob_buf,
      .checksum = 0,
  };
  uint32_t unmasked_key[4] = {0};

  // NULL key
  EXPECT_NOT_OK(keyblob_key_unmask(nullptr, 4, unmasked_key));

  // NULL unmasked_key destination
  EXPECT_NOT_OK(keyblob_key_unmask(&key, 4, nullptr));

  // Mismatched length
  EXPECT_NOT_OK(keyblob_key_unmask(&key, 99, unmasked_key));

  // Huge key length (> kOtcryptoWrappedKeyMaxWords * sizeof(uint32_t))
  otcrypto_blinded_key_t huge_key = {
      .config = kConfigHuge,
      .keyblob_length = sizeof(keyblob_buf),
      .keyblob = keyblob_buf,
      .checksum = 0,
  };
  uint32_t *share0;
  uint32_t *share1;
  EXPECT_NOT_OK(keyblob_to_shares(&huge_key, &share0, &share1));
}

TEST(Keyblob, WriteSharesChunked) {
  std::array<uint32_t, 8> test_share0 = {0x01234567, 0x89abcdef, 0x00010203,
                                         0x04050607, 0x11223344, 0x55667788,
                                         0x99aabbcc, 0xddeeff00};
  std::array<uint32_t, 8> test_share1 = {0x08090a0b, 0x0c0d0e0f, 0x10111213,
                                         0x14151617, 0xa1b2c3d4, 0xe5f60718,
                                         0x293a4b5c, 0x6d7e8f90};

  ASSERT_EQ(test_share0.size(), keyblob_share_num_words(kConfigOddBytes));
  size_t keyblob_words = keyblob_num_words(kConfigOddBytes);
  std::vector<uint32_t> expected_keyblob(keyblob_words, 0);
  std::vector<uint32_t> chunked_keyblob(keyblob_words, 0);

  EXPECT_OK(keyblob_from_shares(test_share0.data(), test_share1.data(),
                                kConfigOddBytes, expected_keyblob.data()));

  // Write the shares in three chunks: 3 words, 3 words, and 2 words.
  EXPECT_OK(keyblob_write_shares(test_share0.data(), test_share1.data(),
                                 /*word_offset=*/0, /*num_words=*/3,
                                 kConfigOddBytes, chunked_keyblob.data()));
  EXPECT_OK(keyblob_write_shares(test_share0.data() + 3, test_share1.data() + 3,
                                 /*word_offset=*/3, /*num_words=*/3,
                                 kConfigOddBytes, chunked_keyblob.data()));
  EXPECT_OK(keyblob_write_shares(test_share0.data() + 6, test_share1.data() + 6,
                                 /*word_offset=*/6, /*num_words=*/2,
                                 kConfigOddBytes, chunked_keyblob.data()));

  EXPECT_THAT(chunked_keyblob, ElementsAreArray(expected_keyblob));
}

TEST(Keyblob, WriteSharesNegative) {
  std::array<uint32_t, 4> test_share0 = {0};
  std::array<uint32_t, 4> test_share1 = {0};
  std::vector<uint32_t> keyblob(keyblob_num_words(kConfigCtr128), 0);

  // Hardware-backed key configuration is rejected.
  EXPECT_NOT_OK(keyblob_write_shares(
      test_share0.data(), test_share1.data(), /*word_offset=*/0,
      /*num_words=*/4, kConfigCtrSideloaded, keyblob.data()));

  // Zero words is rejected.
  EXPECT_NOT_OK(keyblob_write_shares(
      test_share0.data(), test_share1.data(), /*word_offset=*/0,
      /*num_words=*/0, kConfigCtr128, keyblob.data()));

  // Offset exceeds share_words (4).
  EXPECT_NOT_OK(keyblob_write_shares(
      test_share0.data(), test_share1.data(), /*word_offset=*/5,
      /*num_words=*/1, kConfigCtr128, keyblob.data()));

  // Offset + num_words exceeds share_words (4).
  EXPECT_NOT_OK(keyblob_write_shares(
      test_share0.data(), test_share1.data(), /*word_offset=*/2,
      /*num_words=*/3, kConfigCtr128, keyblob.data()));

  // Overflow check on num_words.
  EXPECT_NOT_OK(keyblob_write_shares(
      test_share0.data(), test_share1.data(), /*word_offset=*/2,
      /*num_words=*/SIZE_MAX, kConfigCtr128, keyblob.data()));
}

TEST(Keyblob, EccMismatchedKeyLengthRejected) {
  uint32_t share0[32] = {0};
  uint32_t share1[32] = {0};
  uint32_t keyblob_buf[64] = {0};
  uint32_t *out0 = nullptr;
  uint32_t *out1 = nullptr;

#ifdef OTCRYPTO_DISABLE_KEYBLOB_MASKING
  constexpr uint32_t kNumShares = 1;
#else
  constexpr uint32_t kNumShares = 2;
#endif

  otcrypto_key_config_t bad_p256 = kConfigEcdsaP256;
  bad_p256.key_length = 64;
  EXPECT_EQ(keyblob_share_num_words(bad_p256), 0);
  EXPECT_NOT_OK(keyblob_from_shares(share0, share1, bad_p256, keyblob_buf));

  // Verify keyblob_to_shares rejects `bad_p256` both with the non-zero keyblob
  // byte length an unvalidated 64-byte ECC config would have used
  // ((64 + 8) * kNumShares), with a valid P-256 keyblob length, and with 0.
  for (uint32_t blob_len : {
           kNumShares * (64u + 8u),
           static_cast<uint32_t>(keyblob_num_words(kConfigEcdsaP256) *
                                 sizeof(uint32_t)),
           0u,
       }) {
    otcrypto_blinded_key_t bad_key = {
        .config = bad_p256,
        .keyblob_length = blob_len,
        .keyblob = keyblob_buf,
        .checksum = 0,
    };
    EXPECT_NOT_OK(keyblob_to_shares(&bad_key, &out0, &out1));
  }

  otcrypto_key_config_t p256_48 = kConfigEcdsaP256;
  p256_48.key_length = 48;
  EXPECT_EQ(keyblob_share_num_words(p256_48), 0);
  EXPECT_NOT_OK(keyblob_from_shares(share0, share1, p256_48, keyblob_buf));
  otcrypto_blinded_key_t p256_48_key = {
      .config = p256_48,
      .keyblob_length = kNumShares * (48u + 8u),
      .keyblob = keyblob_buf,
      .checksum = 0,
  };
  EXPECT_NOT_OK(keyblob_to_shares(&p256_48_key, &out0, &out1));

  otcrypto_key_config_t bad_p384 = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  EXPECT_EQ(keyblob_share_num_words(bad_p384), 0);
  EXPECT_NOT_OK(keyblob_from_shares(share0, share1, bad_p384, keyblob_buf));
  otcrypto_blinded_key_t bad_p384_key = {
      .config = bad_p384,
      .keyblob_length = kNumShares * (32u + 8u),
      .keyblob = keyblob_buf,
      .checksum = 0,
  };
  EXPECT_NOT_OK(keyblob_to_shares(&bad_p384_key, &out0, &out1));
}

}  // namespace
}  // namespace keyblob_unittest
