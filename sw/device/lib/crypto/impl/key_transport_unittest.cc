// Copyright lowRISC contributors (OpenTitan project).
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
constexpr otcrypto_key_config_t kConfigHwBackedAesCtr128 = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = 128 / 8,
    .hw_backed = kHardenedBoolTrue,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Invalid RSA key configuration for testing (sideloaded RSA-2048 key).
constexpr otcrypto_key_config_t kConfigRsaInvalid = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeRsaSignPkcs,
    .key_length = 2048 / 8,
    .hw_backed = kHardenedBoolTrue,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (128-bit AES-CTR exportable key).
constexpr otcrypto_key_config_t kConfigExportableAesCtr128 = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = 128 / 8,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolTrue,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (128-bit AES-CTR non-exportable key).
constexpr otcrypto_key_config_t kConfigNonExportableAesCtr128 = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = 128 / 8,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

TEST(KeyTransport, HwBackedKeyToDiversificationData) {
  uint32_t test_version = 0xf0f1f2f3;
  std::array<uint32_t, 7> test_salt = {0x01234567, 0x89abcdef, 0x00010203,
                                       0x04050607, 0x08090a0b, 0x0c0d0e0f,
                                       0x10111213};

  // Create a key handle from the test data.
  uint32_t keyblob[32] = {0};
  otcrypto_blinded_key_t key = {
      .config = kConfigHwBackedAesCtr128,
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
            kConfigHwBackedAesCtr128.key_mode);
}

TEST(KeyTransport, HwBackedRsaKeyFails) {
  uint32_t test_version = 0xf0f1f2f3;
  std::array<uint32_t, 7> test_salt = {0x01234567, 0x89abcdef, 0x00010203,
                                       0x04050607, 0x08090a0b, 0x0c0d0e0f,
                                       0x10111213};

  // Create a key handle from the test data.
  uint32_t keyblob[32] = {0};
  otcrypto_blinded_key_t key = {
      .config = kConfigRsaInvalid,
      .keyblob_length = 32,
      .keyblob = keyblob,
  };

  // Expect the hardware-backed RSA key to be rejected.
  EXPECT_EQ(
      status_ok(otcrypto_hw_backed_key(test_version, test_salt.data(), &key)),
      false);
}

TEST(KeyTransport, BlindedKeyImportExport) {
  std::array<uint32_t, 4> share0 = {0x00010203, 0x04050607, 0x08090a0b,
                                    0x0c0d0e0f};
  std::array<uint32_t, 4> share1 = {0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb,
                                    0xfcfdfeff};

  // Determine the unmasked value of the key.
  std::array<uint32_t, 4> unmasked_key;
  for (size_t i = 0; i < unmasked_key.size(); i++) {
    unmasked_key[i] = share0[i] ^ share1[i];
  }

  uint32_t keyblob[share0.size() * 2];
  otcrypto_blinded_key_t blinded_key = {
      .config = kConfigExportableAesCtr128,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Import the key into the blinded key struct.
  EXPECT_EQ(status_ok(otcrypto_import_blinded_key(
                (otcrypto_const_word32_buf_t){
                    .data = share0.data(),
                    .len = share0.size(),
                },
                (otcrypto_const_word32_buf_t){
                    .data = share1.data(),
                    .len = share1.size(),
                },
                &blinded_key)),
            true);

  // Zero the original inputs (they should now be safe to free).
  memset(share0.data(), 0, sizeof(share0));
  memset(share1.data(), 0, sizeof(share1));

  // Export the key again.
  otcrypto_word32_buf_t share0_buf = {
      .data = share0.data(),
      .len = share0.size(),
  };
  otcrypto_word32_buf_t share1_buf = {
      .data = share1.data(),
      .len = share1.size(),
  };
  EXPECT_EQ(status_ok(otcrypto_export_blinded_key(&blinded_key, share0_buf,
                                                  share1_buf)),
            true);

  // Unmask the result and compare to the unmasked key.
  for (size_t i = 0; i < unmasked_key.size(); i++) {
    EXPECT_EQ(unmasked_key[i], share0[i] ^ share1[i]);
  }
}

TEST(KeyTransport, BlindedKeyImportBadLengths) {
  std::array<uint32_t, 4> share0 = {0x00010203, 0x04050607, 0x08090a0b,
                                    0x0c0d0e0f};
  std::array<uint32_t, 4> share1 = {0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb,
                                    0xfcfdfeff};

  // Create destination struct.
  uint32_t keyblob[share0.size() * 2];
  otcrypto_blinded_key_t blinded_key = {
      .config = kConfigExportableAesCtr128,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Set a bad length for share 0 and expect the import to fail.
  EXPECT_EQ(status_ok(otcrypto_import_blinded_key(
                (otcrypto_const_word32_buf_t){
                    .data = share0.data(),
                    .len = share0.size() - 1,
                },
                (otcrypto_const_word32_buf_t){
                    .data = share1.data(),
                    .len = share1.size(),
                },
                &blinded_key)),
            false);

  // Set a bad length for share 1 and expect the import to fail.
  EXPECT_EQ(status_ok(otcrypto_import_blinded_key(
                (otcrypto_const_word32_buf_t){
                    .data = share0.data(),
                    .len = share0.size(),
                },
                (otcrypto_const_word32_buf_t){
                    .data = share1.data(),
                    .len = share1.size() - 1,
                },
                &blinded_key)),
            false);

  // Set a bad length for the keyblob and expect the import to fail.
  otcrypto_blinded_key_t bad_blinded_key = {
      .config = kConfigExportableAesCtr128,
      .keyblob_length = sizeof(keyblob) - 1,
      .keyblob = keyblob,
  };
  EXPECT_EQ(status_ok(otcrypto_import_blinded_key(
                (otcrypto_const_word32_buf_t){
                    .data = share0.data(),
                    .len = share0.size(),
                },
                (otcrypto_const_word32_buf_t){
                    .data = share1.data(),
                    .len = share1.size(),
                },
                &bad_blinded_key)),
            false);
}

TEST(KeyTransport, BlindedKeyExportBadLengths) {
  std::array<uint32_t, 4> share0 = {0x00010203, 0x04050607, 0x08090a0b,
                                    0x0c0d0e0f};
  std::array<uint32_t, 4> share1 = {0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb,
                                    0xfcfdfeff};

  // Create destination struct.
  uint32_t keyblob[share0.size() * 2];
  otcrypto_blinded_key_t blinded_key = {
      .config = kConfigExportableAesCtr128,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Import the key.
  EXPECT_EQ(status_ok(otcrypto_import_blinded_key(
                (otcrypto_const_word32_buf_t){
                    .data = share0.data(),
                    .len = share0.size(),
                },
                (otcrypto_const_word32_buf_t){
                    .data = share1.data(),
                    .len = share1.size(),
                },
                &blinded_key)),
            true);

  otcrypto_word32_buf_t share_with_good_length = {
      .data = share0.data(),
      .len = share0.size(),
  };
  otcrypto_word32_buf_t share_with_bad_length = {
      .data = share1.data(),
      .len = share1.size() - 1,
  };

  // Set a bad length for share 0 and expect the import to fail.
  EXPECT_EQ(status_ok(otcrypto_export_blinded_key(
                &blinded_key, share_with_bad_length, share_with_good_length)),
            false);

  // Set a bad length for share 1 and expect the import to fail.
  EXPECT_EQ(status_ok(otcrypto_export_blinded_key(
                &blinded_key, share_with_good_length, share_with_bad_length)),
            false);

  // Set a bad length for the keyblob and expect the export to fail.
  otcrypto_blinded_key_t bad_blinded_key = {
      .config = kConfigExportableAesCtr128,
      .keyblob_length = sizeof(keyblob) - 1,
      .keyblob = keyblob,
  };
  EXPECT_EQ(
      status_ok(otcrypto_export_blinded_key(
          &bad_blinded_key, share_with_good_length, share_with_good_length)),
      false);
}

TEST(KeyTransport, BlindedKeyExportNotExportable) {
  std::array<uint32_t, 4> share0 = {0x00010203, 0x04050607, 0x08090a0b,
                                    0x0c0d0e0f};
  std::array<uint32_t, 4> share1 = {0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb,
                                    0xfcfdfeff};

  // Create destination struct.
  uint32_t keyblob[share0.size() * 2];
  otcrypto_blinded_key_t blinded_key = {
      .config = kConfigNonExportableAesCtr128,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Import the key.
  EXPECT_EQ(status_ok(otcrypto_import_blinded_key(
                (otcrypto_const_word32_buf_t){
                    .data = share0.data(),
                    .len = share0.size(),
                },
                (otcrypto_const_word32_buf_t){
                    .data = share1.data(),
                    .len = share1.size(),
                },
                &blinded_key)),
            true);

  // Expect key export to fail.
  otcrypto_word32_buf_t share0_buf = {
      .data = share0.data(),
      .len = share0.size(),
  };
  otcrypto_word32_buf_t share1_buf = {
      .data = share1.data(),
      .len = share1.size(),
  };
  EXPECT_EQ(status_ok(otcrypto_export_blinded_key(&blinded_key, share0_buf,
                                                  share1_buf)),
            false);
}

}  // namespace
}  // namespace key_transport_unittest
