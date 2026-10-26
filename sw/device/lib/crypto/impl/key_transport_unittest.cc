// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/key_transport.h"

#include <array>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"

#include "aes_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"

namespace key_transport_unittest {
namespace {
using ::testing::ElementsAreArray;

#define EXPECT_OK(status_) EXPECT_EQ(status_.value, OTCRYPTO_OK.value)
#define EXPECT_NOT_OK(status_) EXPECT_NE(status_.value, OTCRYPTO_OK.value)

// Key configuration for testing (128-bit AES-CTR hardware-backed key).
const otcrypto_key_config_t kConfigHwBackedAesCtr128 = {
    .version = otcrypto_lib_version(),
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = 128 / 8,
    .hw_backed = kHardenedBoolTrue,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Invalid RSA key configuration for testing (sideloaded RSA-2048 key).
const otcrypto_key_config_t kConfigRsaInvalid = {
    .version = otcrypto_lib_version(),
    .key_mode = kOtcryptoKeyModeRsaSignPkcs,
    .key_length = 2048 / 8,
    .hw_backed = kHardenedBoolTrue,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (128-bit AES-CTR exportable key).
const otcrypto_key_config_t kConfigExportableAesCtr128 = {
    .version = otcrypto_lib_version(),
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = 128 / 8,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolTrue,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (128-bit AES-CTR non-exportable key).
const otcrypto_key_config_t kConfigNonExportableAesCtr128 = {
    .version = otcrypto_lib_version(),
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = 128 / 8,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Key configuration for testing (256-bit AES-KWP key).
const otcrypto_key_config_t kConfigAesKwp256 = {
    .version = otcrypto_lib_version(),
    .key_mode = kOtcryptoKeyModeAesKwp,
    .key_length = 256 / 8,
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

  std::array<uint32_t, 8> att_salt = {0};
  otcrypto_blinded_key_t att_key = {
      .config = kConfigRsaInvalid,
      .keyblob_length = 36,
      .keyblob = keyblob,
  };
  EXPECT_NOT_OK(otcrypto_hw_backed_attestation_key(test_version,
                                                   att_salt.data(), &att_key));
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
  otcrypto_const_word32_buf_t import_share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share0.data(), share0.size());
  otcrypto_const_word32_buf_t import_share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1.data(), share1.size());
  EXPECT_EQ(status_ok(otcrypto_import_blinded_key(
                &import_share0_buf, &import_share1_buf, &blinded_key)),
            true);

  // Zero the original inputs (they should now be safe to free).
  memset(share0.data(), 0, sizeof(share0));
  memset(share1.data(), 0, sizeof(share1));

  // Export the key again.
  otcrypto_word32_buf_t share0_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, share0.data(), share0.size());
  otcrypto_word32_buf_t share1_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, share1.data(), share1.size());
  EXPECT_EQ(status_ok(otcrypto_export_blinded_key(&blinded_key, &share0_buf,
                                                  &share1_buf)),
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
  otcrypto_const_word32_buf_t bad_length_share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share0.data(), share0.size() - 1);
  otcrypto_const_word32_buf_t share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1.data(), share1.size());
  EXPECT_EQ(status_ok(otcrypto_import_blinded_key(&bad_length_share0_buf,
                                                  &share1_buf, &blinded_key)),
            false);

  // Set a bad length for share 1 and expect the import to fail.
  otcrypto_const_word32_buf_t share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share0.data(), share0.size());
  otcrypto_const_word32_buf_t bad_length_share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1.data(), share1.size() - 1);
  EXPECT_EQ(status_ok(otcrypto_import_blinded_key(
                &share0_buf, &bad_length_share1_buf, &blinded_key)),
            false);

  // Set a bad length for the keyblob and expect the import to fail.
  otcrypto_blinded_key_t bad_blinded_key = {
      .config = kConfigExportableAesCtr128,
      .keyblob_length = sizeof(keyblob) - 1,
      .keyblob = keyblob,
  };
  EXPECT_EQ(status_ok(otcrypto_import_blinded_key(&share0_buf, &share1_buf,
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
  otcrypto_const_word32_buf_t share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share0.data(), share0.size());
  otcrypto_const_word32_buf_t share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1.data(), share1.size());
  EXPECT_EQ(status_ok(otcrypto_import_blinded_key(&share0_buf, &share1_buf,
                                                  &blinded_key)),
            true);

  otcrypto_word32_buf_t share_with_good_length =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, share0.data(), share0.size());
  otcrypto_word32_buf_t share_with_bad_length = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, share1.data(), share1.size() - 1);

  // Set a bad length for share 0 and expect the import to fail.
  EXPECT_EQ(status_ok(otcrypto_export_blinded_key(
                &blinded_key, &share_with_bad_length, &share_with_good_length)),
            false);

  // Set a bad length for share 1 and expect the import to fail.
  EXPECT_EQ(status_ok(otcrypto_export_blinded_key(
                &blinded_key, &share_with_good_length, &share_with_bad_length)),
            false);

  // Set a bad length for the keyblob and expect the export to fail.
  otcrypto_blinded_key_t bad_blinded_key = {
      .config = kConfigExportableAesCtr128,
      .keyblob_length = sizeof(keyblob) - 1,
      .keyblob = keyblob,
  };
  EXPECT_EQ(
      status_ok(otcrypto_export_blinded_key(
          &bad_blinded_key, &share_with_good_length, &share_with_good_length)),
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
  otcrypto_const_word32_buf_t import_share0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share0.data(), share0.size());
  otcrypto_const_word32_buf_t import_share1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1.data(), share1.size());
  EXPECT_EQ(status_ok(otcrypto_import_blinded_key(
                &import_share0_buf, &import_share1_buf, &blinded_key)),
            true);

  // Expect key export to fail.
  otcrypto_word32_buf_t share0_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, share0.data(), share0.size());
  otcrypto_word32_buf_t share1_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, share1.data(), share1.size());
  EXPECT_EQ(status_ok(otcrypto_export_blinded_key(&blinded_key, &share0_buf,
                                                  &share1_buf)),
            false);
}

TEST(KeyTransport, KeyWrapUnwrapNegative) {
  rom_test::NiceMockAbsMmio mmio;
  ON_CALL(mmio, Read32(TOP_EARLGREY_AES_BASE_ADDR + AES_STATUS_REG_OFFSET))
      .WillByDefault(testing::Return(1 << AES_STATUS_IDLE_BIT));
  ON_CALL(mmio, Read32(TOP_EARLGREY_KEYMGR_BASE_ADDR +
                       KEYMGR_SIDELOAD_CLEAR_REG_OFFSET))
      .WillByDefault(testing::Return(KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_AES));
  uint32_t target_keyblob[8] = {0};
  otcrypto_blinded_key_t target_key = {
      .config = kConfigNonExportableAesCtr128,
      .keyblob_length = sizeof(target_keyblob),
      .keyblob = target_keyblob,
      .checksum = 0,
  };
  target_key.checksum = otcrypto_integrity_blinded_checksum(&target_key);

  uint32_t kek_keyblob[16] = {0};
  otcrypto_blinded_key_t kek_key = {
      .config = kConfigAesKwp256,
      .keyblob_length = sizeof(kek_keyblob),
      .keyblob = kek_keyblob,
      .checksum = 0,
  };
  kek_key.checksum = otcrypto_integrity_blinded_checksum(&kek_key);

  uint32_t wrapped_data[64] = {0};
  otcrypto_word32_buf_t wrapped_buf = {
      .data = wrapped_data,
      .len = 64,
  };
  otcrypto_const_word32_buf_t const_wrapped_buf = {
      .data = wrapped_data,
      .len = 64,
  };

  hardened_bool_t success;

  // Wrap negative tests
  EXPECT_NOT_OK(otcrypto_key_wrap(nullptr, &kek_key, &wrapped_buf));
  EXPECT_NOT_OK(otcrypto_key_wrap(&target_key, nullptr, &wrapped_buf));

  otcrypto_word32_buf_t wrapped_buf_null = {.data = nullptr, .len = 64};
  EXPECT_NOT_OK(otcrypto_key_wrap(&target_key, &kek_key, &wrapped_buf_null));

  // Bad KEK mode
  otcrypto_blinded_key_t bad_kek_mode = {
      .config = kConfigNonExportableAesCtr128,
      .keyblob_length = sizeof(kek_keyblob),
      .keyblob = kek_keyblob,
      .checksum = 0,
  };
  bad_kek_mode.checksum = otcrypto_integrity_blinded_checksum(&bad_kek_mode);
  EXPECT_NOT_OK(otcrypto_key_wrap(&target_key, &bad_kek_mode, &wrapped_buf));

  // Target key checksum error
  otcrypto_blinded_key_t bad_target_chk = target_key;
  bad_target_chk.checksum ^= 0xFFFFFFFF;
  EXPECT_NOT_OK(otcrypto_key_wrap(&bad_target_chk, &kek_key, &wrapped_buf));

  // Unwrap negative tests
  EXPECT_NOT_OK(otcrypto_key_unwrap(nullptr, &kek_key, &success, &target_key));
  EXPECT_NOT_OK(
      otcrypto_key_unwrap(&const_wrapped_buf, nullptr, &success, &target_key));
  EXPECT_NOT_OK(
      otcrypto_key_unwrap(&const_wrapped_buf, &kek_key, nullptr, &target_key));
  EXPECT_NOT_OK(
      otcrypto_key_unwrap(&const_wrapped_buf, &kek_key, &success, nullptr));

  // Bad KEK mode
  EXPECT_NOT_OK(otcrypto_key_unwrap(&const_wrapped_buf, &bad_kek_mode, &success,
                                    &target_key));

  // Bad KEK checksum
  otcrypto_blinded_key_t bad_kek_chk = kek_key;
  bad_kek_chk.checksum ^= 0xFFFFFFFF;
  EXPECT_NOT_OK(otcrypto_key_unwrap(&const_wrapped_buf, &bad_kek_chk, &success,
                                    &target_key));

  // Bad KEK hw_backed flag
  otcrypto_key_config_t bad_kek_hw_cfg = kConfigAesKwp256;
  bad_kek_hw_cfg.hw_backed = static_cast<hardened_bool_t>(0x12345678);
  otcrypto_blinded_key_t bad_kek_hw = {
      .config = bad_kek_hw_cfg,
      .keyblob_length = sizeof(kek_keyblob),
      .keyblob = kek_keyblob,
      .checksum = 0,
  };
  bad_kek_hw.checksum = otcrypto_integrity_blinded_checksum(&bad_kek_hw);
  EXPECT_NOT_OK(otcrypto_key_unwrap(&const_wrapped_buf, &bad_kek_hw, &success,
                                    &target_key));

  // Mismatched key_to_wrap->keyblob_length when wrapped_buf.len == exp_len
  size_t exp_wrapped_words = 0;
  EXPECT_OK(otcrypto_wrapped_key_len(target_key.config, &exp_wrapped_words));
  otcrypto_word32_buf_t valid_len_wrapped_buf = {
      .data = wrapped_data,
      .len = exp_wrapped_words,
  };
  otcrypto_blinded_key_t bad_target_len = {
      .config = kConfigNonExportableAesCtr128,
      .keyblob_length = sizeof(target_keyblob) - 4,
      .keyblob = target_keyblob,
      .checksum = 0,
  };
  bad_target_len.checksum =
      otcrypto_integrity_blinded_checksum(&bad_target_len);
  EXPECT_NOT_OK(
      otcrypto_key_wrap(&bad_target_len, &kek_key, &valid_len_wrapped_buf));

  // Unwrap with wrapped_key->len > kOtcryptoWrappedKeyMaxWords
  otcrypto_const_word32_buf_t huge_wrapped_buf = {
      .data = wrapped_data,
      .len = 9999,
  };
  EXPECT_NOT_OK(
      otcrypto_key_unwrap(&huge_wrapped_buf, &kek_key, &success, &target_key));

  // Unwrap with odd number of words (not a multiple of 64-bit semiblock)
  otcrypto_const_word32_buf_t odd_wrapped_buf = {
      .data = wrapped_data,
      .len = 11,
  };
  EXPECT_NOT_OK(
      otcrypto_key_unwrap(&odd_wrapped_buf, &kek_key, &success, &target_key));

  // Unwrap with wrapped_key->len below the minimum wrapped key header size
  for (size_t short_len : {4u, 6u, 8u}) {
    otcrypto_const_word32_buf_t short_wrapped_buf = {
        .data = wrapped_data,
        .len = short_len,
    };
    EXPECT_NOT_OK(otcrypto_key_unwrap(&short_wrapped_buf, &kek_key, &success,
                                      &target_key));
  }
}

TEST(KeyTransport, BlindedKeyMigrate) {
  uint32_t keyblob[8] = {0};
  otcrypto_blinded_key_t old_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = 16,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  otcrypto_blinded_key_t new_key = old_key;

  EXPECT_OK(otcrypto_blinded_key_migrate(&old_key, &new_key));

  // Modify version to something other than Version1.
  otcrypto_blinded_key_t bad_version_key = old_key;
  bad_version_key.config.version = kOtcryptoLibVersion2;
  EXPECT_NOT_OK(otcrypto_blinded_key_migrate(&bad_version_key, &new_key));

  // Hardware-backed keys cannot be migrated.
  otcrypto_blinded_key_t hw_backed_key = old_key;
  hw_backed_key.config.hw_backed = kHardenedBoolTrue;
  EXPECT_NOT_OK(otcrypto_blinded_key_migrate(&hw_backed_key, &new_key));
}

TEST(KeyTransport, WrappedKeyLenRsa) {
  const otcrypto_key_config_t kConfigRsa2048 = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = 256,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  const otcrypto_key_config_t kConfigRsa3072 = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeRsaSignPss,
      .key_length = 384,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  const otcrypto_key_config_t kConfigRsa4096 = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeRsaEncryptOaep,
      .key_length = 512,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  EXPECT_NOT_OK(otcrypto_wrapped_key_len(kConfigRsa2048, nullptr));

  size_t wrapped_words_2048 = 0;
  EXPECT_OK(otcrypto_wrapped_key_len(kConfigRsa2048, &wrapped_words_2048));
  EXPECT_EQ(wrapped_words_2048, 204);
  EXPECT_LE(wrapped_words_2048, kOtcryptoWrappedKeyMaxWords);

  size_t wrapped_words_3072 = 0;
  EXPECT_OK(otcrypto_wrapped_key_len(kConfigRsa3072, &wrapped_words_3072));
  EXPECT_EQ(wrapped_words_3072, 300);
  EXPECT_LE(wrapped_words_3072, kOtcryptoWrappedKeyMaxWords);

  size_t wrapped_words_4096 = 0;
  EXPECT_OK(otcrypto_wrapped_key_len(kConfigRsa4096, &wrapped_words_4096));
  EXPECT_EQ(wrapped_words_4096, 396);
  EXPECT_EQ(wrapped_words_4096, kOtcryptoWrappedKeyMaxWords);

  // Verify otcrypto_key_wrap rejects an RSA-4096 key with the old (2-share)
  // keyblob_length of 1024 bytes instead of 1540 bytes.
  rom_test::NiceMockAbsMmio mmio;
  ON_CALL(mmio, Read32(TOP_EARLGREY_AES_BASE_ADDR + AES_STATUS_REG_OFFSET))
      .WillByDefault(testing::Return(1 << AES_STATUS_IDLE_BIT));
  ON_CALL(mmio, Read32(TOP_EARLGREY_KEYMGR_BASE_ADDR +
                       KEYMGR_SIDELOAD_CLEAR_REG_OFFSET))
      .WillByDefault(testing::Return(KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_AES));

  uint32_t kek_keyblob[16] = {0};
  otcrypto_blinded_key_t kek_key = {
      .config = kConfigAesKwp256,
      .keyblob_length = sizeof(kek_keyblob),
      .keyblob = kek_keyblob,
      .checksum = 0,
  };
  kek_key.checksum = otcrypto_integrity_blinded_checksum(&kek_key);

  uint32_t rsa_keyblob[385] = {0};
  otcrypto_blinded_key_t bad_rsa_key = {
      .config = kConfigRsa4096,
      .keyblob_length = 1024,
      .keyblob = rsa_keyblob,
      .checksum = 0,
  };
  bad_rsa_key.checksum = otcrypto_integrity_blinded_checksum(&bad_rsa_key);

  uint32_t wrapped_data[kOtcryptoWrappedKeyMaxWords] = {0};
  otcrypto_word32_buf_t wrapped_buf = {
      .data = wrapped_data,
      .len = wrapped_words_4096,
  };
  EXPECT_NOT_OK(otcrypto_key_wrap(&bad_rsa_key, &kek_key, &wrapped_buf));
}

TEST(KeyTransport, HwBackedKeygenNegative) {
  const otcrypto_key_config_t kConfigHwBackedAesCtr256 = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeAesCtr,
      .key_length = 256 / 8,
      .hw_backed = kHardenedBoolTrue,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t test_version = 0;
  std::array<uint32_t, 7> test_salt = {0x01234567, 0x89abcdef, 0x00010203,
                                       0x04050607, 0x08090a0b, 0x0c0d0e0f,
                                       0x10111213};
  std::array<uint32_t, 8> att_salt = {0x01234567, 0x89abcdef, 0x00010203,
                                      0x04050607, 0x08090a0b, 0x0c0d0e0f,
                                      0x10111213, 0x14151617};

  // A 32-byte (8-word) sideload keyblob is too small for SW keygen (needs 64B).
  uint32_t small_sealing_keyblob[8] = {0};
  otcrypto_blinded_key_t small_sealing_key = {
      .config = kConfigHwBackedAesCtr256,
      .keyblob_length = sizeof(small_sealing_keyblob),
      .keyblob = small_sealing_keyblob,
  };
  EXPECT_OK(otcrypto_hw_backed_key(test_version, test_salt.data(),
                                   &small_sealing_key));
  EXPECT_NOT_OK(
      ot_crypto_hw_backed_keygen(kHardenedBoolFalse, &small_sealing_key));

  // A 36-byte (9-word) attestation keyblob is too small for SW keygen (needs
  // 64B).
  uint32_t small_att_keyblob[9] = {0};
  otcrypto_blinded_key_t small_att_key = {
      .config = kConfigHwBackedAesCtr256,
      .keyblob_length = sizeof(small_att_keyblob),
      .keyblob = small_att_keyblob,
  };
  EXPECT_OK(otcrypto_hw_backed_attestation_key(test_version, att_salt.data(),
                                               &small_att_key));
  EXPECT_NOT_OK(ot_crypto_hw_backed_keygen(kHardenedBoolTrue, &small_att_key));

  // A 128-bit key config does not match the 256-bit keymgr output share size.
  uint32_t keyblob_64b[16] = {0};
  otcrypto_blinded_key_t wrong_key_len = {
      .config = kConfigHwBackedAesCtr128,
      .keyblob_length = sizeof(keyblob_64b),
      .keyblob = keyblob_64b,
  };
  EXPECT_OK(
      otcrypto_hw_backed_key(test_version, test_salt.data(), &wrong_key_len));
  EXPECT_NOT_OK(ot_crypto_hw_backed_keygen(kHardenedBoolFalse, &wrong_key_len));

  // Corrupted checksum should be rejected before keygen.
  otcrypto_blinded_key_t bad_checksum_key = {
      .config = kConfigHwBackedAesCtr256,
      .keyblob_length = sizeof(keyblob_64b),
      .keyblob = keyblob_64b,
  };
  EXPECT_OK(otcrypto_hw_backed_key(test_version, test_salt.data(),
                                   &bad_checksum_key));
  bad_checksum_key.checksum ^= 0xffffffff;
  EXPECT_NOT_OK(
      ot_crypto_hw_backed_keygen(kHardenedBoolFalse, &bad_checksum_key));
}

}  // namespace
}  // namespace key_transport_unittest
