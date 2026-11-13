// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"

#include <cstring>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/nonce.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/ownership/mock_owner_verify.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "flash_ctrl_regs.h"

namespace {
using ::rom_test::FlashCfg;
using ::rom_test::FlashPerms;
using ::testing::_;
using ::testing::DoAll;
using ::testing::Field;
using ::testing::Invoke;
using ::testing::NotNull;
using ::testing::Return;
using ::testing::SetArgPointee;

constexpr uint32_t kTestCommand = 0x524e574f;  // 'OWNR'
constexpr nonce_t kTestNonce = {.value = {0x11223344, 0x55667788}};
constexpr size_t kPageSize = FLASH_CTRL_PARAM_BYTES_PER_PAGE;
constexpr size_t kScanRegion = 1;
constexpr uint32_t kTotalFlashPages =
    FLASH_CTRL_PARAM_REG_NUM_BANKS * FLASH_CTRL_PARAM_REG_PAGES_PER_BANK;
constexpr flash_ctrl_data_region_state_t kSavedRegionState = {
    .mp_region = 0x00020020,
    .mp_region_cfg = 0x09669966,
};

class OwnershipKeyTest : public rom_test::RomTest {
 protected:
  static constexpr size_t kBufferPages = 16;

  void SetUp() override {
    std::memset(flash_buf_.data(), 0xff, flash_buf_.size());
    std::memset(&owner_page[0], 0, sizeof(owner_page[0]));
    owner_page[0].ownership_key_alg = kOwnershipKeyAlgHybridSpxPure;
  }

  uintptr_t BufferStart() const {
    return reinterpret_cast<uintptr_t>(flash_buf_.data());
  }

  uint8_t *PagePtr(size_t page_index) {
    return flash_buf_.data() + page_index * kPageSize;
  }

  static owner_detached_signature_t MakeDetachedSig(uint32_t command,
                                                    nonce_t nonce,
                                                    uint32_t sig_marker = 1) {
    owner_detached_signature_t sig{};
    sig.header.tag = kTlvTagDetachedSignature;
    sig.header.length = sizeof(owner_detached_signature_t);
    sig.header.version = {.major = 0, .minor = 0};
    sig.command = command;
    sig.nonce = nonce;
    sig.signature.hybrid.ecdsa.r[0] = sig_marker;
    sig.signature.hybrid.spx.data[0] = sig_marker;
    return sig;
  }

  void WriteDetachedSigAtPage(size_t page_index,
                              const owner_detached_signature_t &sig) {
    std::memcpy(PagePtr(page_index), &sig, sizeof(sig));
  }

  void ExpectWindowSave() {
    EXPECT_CALL(flash_ctrl_, DataRegionSave(kScanRegion, _))
        .WillOnce(SetArgPointee<1>(kSavedRegionState));
  }

  void ExpectWindowConfig(multi_bit_bool_t scrambling) {
    EXPECT_CALL(
        flash_ctrl_,
        DataRegionProtect(
            kScanRegion, /*page_offset=*/0, kTotalFlashPages,
            FlashPerms(kMultiBitBool4True, kMultiBitBool4False,
                       kMultiBitBool4False),
            FlashCfg(scrambling, kMultiBitBool4False, kMultiBitBool4False),
            kHardenedBoolFalse));
  }

  void ExpectWindowRestore() {
    EXPECT_CALL(flash_ctrl_,
                DataRegionRestore(
                    kScanRegion,
                    AllOf(Field(&flash_ctrl_data_region_state_t::mp_region,
                                kSavedRegionState.mp_region),
                          Field(&flash_ctrl_data_region_state_t::mp_region_cfg,
                                kSavedRegionState.mp_region_cfg))));
    EXPECT_CALL(flash_ctrl_, DataRegionSave(kScanRegion, _))
        .WillOnce(SetArgPointee<1>(kSavedRegionState));
  }

  std::vector<uint8_t> flash_buf_ =
      std::vector<uint8_t>(kBufferPages * kPageSize, 0xff);
  uint32_t message_[4] = {0xa1, 0xb2, 0xc3, 0xd4};
  uint32_t flash_exec_ = 0;

  rom_test::MockFlashCtrl flash_ctrl_;
  rom_test::MockHmac hmac_;
  rom_test::MockOwnerVerify owner_verify_;
};

TEST_F(OwnershipKeyTest, FoundInFirstPass) {
  WriteDetachedSigAtPage(2, MakeDetachedSig(kTestCommand, kTestNonce));

  ExpectWindowSave();
  ExpectWindowConfig(kMultiBitBool4True);
  EXPECT_CALL(hmac_, sha256(message_, sizeof(message_), _));
  EXPECT_CALL(owner_verify_,
              verify(kOwnershipKeyAlgHybridSpxPure, &owner_page[0].owner_key,
                     NotNull(), NotNull(), nullptr, 0, nullptr, 0, message_,
                     sizeof(message_), _, &flash_exec_))
      .WillOnce(Return(kErrorOk));
  ExpectWindowRestore();

  EXPECT_EQ(
      ownership_detached_signature_validate(
          BufferStart(), flash_buf_.size(), /*page=*/0, kOwnershipKeyOwner,
          kTestCommand, &kTestNonce, message_, sizeof(message_), &flash_exec_),
      kErrorOk);
}

TEST_F(OwnershipKeyTest, FoundOnlyInSecondPass) {
  const owner_detached_signature_t valid_sig =
      MakeDetachedSig(kTestCommand, kTestNonce);

  ExpectWindowSave();
  ExpectWindowConfig(kMultiBitBool4True);
  EXPECT_CALL(
      flash_ctrl_,
      DataRegionProtect(kScanRegion, /*page_offset=*/0, kTotalFlashPages,
                        FlashPerms(kMultiBitBool4True, kMultiBitBool4False,
                                   kMultiBitBool4False),
                        FlashCfg(kMultiBitBool4False, kMultiBitBool4False,
                                 kMultiBitBool4False),
                        kHardenedBoolFalse))
      .WillOnce(
          Invoke([&](flash_ctrl_region_index_t, uint32_t, uint32_t,
                     flash_ctrl_perms_t, flash_ctrl_cfg_t, hardened_bool_t) {
            WriteDetachedSigAtPage(5, valid_sig);
          }));
  EXPECT_CALL(hmac_, sha256(message_, sizeof(message_), _));
  EXPECT_CALL(owner_verify_,
              verify(kOwnershipKeyAlgHybridSpxPure, &owner_page[0].owner_key,
                     NotNull(), NotNull(), nullptr, 0, nullptr, 0, message_,
                     sizeof(message_), _, &flash_exec_))
      .WillOnce(Return(kErrorOk));
  ExpectWindowRestore();

  EXPECT_EQ(
      ownership_detached_signature_validate(
          BufferStart(), flash_buf_.size(), /*page=*/0, kOwnershipKeyOwner,
          kTestCommand, &kTestNonce, message_, sizeof(message_), &flash_exec_),
      kErrorOk);
}

TEST_F(OwnershipKeyTest, NotFoundRestoresRegion) {
  ExpectWindowSave();
  ExpectWindowConfig(kMultiBitBool4True);
  ExpectWindowConfig(kMultiBitBool4False);
  ExpectWindowRestore();

  EXPECT_EQ(
      ownership_detached_signature_validate(
          BufferStart(), flash_buf_.size(), /*page=*/0, kOwnershipKeyOwner,
          kTestCommand, &kTestNonce, message_, sizeof(message_), &flash_exec_),
      kErrorOwnershipSignatureNotFound);
}

TEST_F(OwnershipKeyTest, FoundInLastValidPosition) {
  // A detached signature occupies 4 pages (8192 bytes). Place it in the last 4
  // pages of the buffer (pages kBufferPages - 4 .. kBufferPages - 1).
  constexpr size_t kLastStartPage =
      kBufferPages - sizeof(owner_detached_signature_t) / kPageSize;
  WriteDetachedSigAtPage(kLastStartPage,
                         MakeDetachedSig(kTestCommand, kTestNonce));

  ExpectWindowSave();
  ExpectWindowConfig(kMultiBitBool4True);
  EXPECT_CALL(hmac_, sha256(message_, sizeof(message_), _));
  EXPECT_CALL(owner_verify_,
              verify(kOwnershipKeyAlgHybridSpxPure, &owner_page[0].owner_key,
                     NotNull(), NotNull(), nullptr, 0, nullptr, 0, message_,
                     sizeof(message_), _, &flash_exec_))
      .WillOnce(Return(kErrorOk));
  ExpectWindowRestore();

  EXPECT_EQ(
      ownership_detached_signature_validate(
          BufferStart(), flash_buf_.size(), /*page=*/0, kOwnershipKeyOwner,
          kTestCommand, &kTestNonce, message_, sizeof(message_), &flash_exec_),
      kErrorOk);
}

TEST_F(OwnershipKeyTest, SkipsWrongCommandAndWrongNonceMatchesZeroNonce) {
  // Page 0: wrong command.
  WriteDetachedSigAtPage(0, MakeDetachedSig(0xdeadbeef, kTestNonce, 0x10));
  // Page 4: wrong nonce.
  const nonce_t kWrongNonce = {.value = {1, 2}};
  WriteDetachedSigAtPage(4, MakeDetachedSig(kTestCommand, kWrongNonce, 0x20));
  // Page 8: zero nonce wildcard, which must match any nonce.
  const nonce_t kZeroNonce = {.value = {0, 0}};
  WriteDetachedSigAtPage(8, MakeDetachedSig(kTestCommand, kZeroNonce, 0x30));

  const auto *expected_sig =
      reinterpret_cast<const owner_detached_signature_t *>(PagePtr(8));

  ExpectWindowSave();
  ExpectWindowConfig(kMultiBitBool4True);
  EXPECT_CALL(hmac_, sha256(message_, sizeof(message_), _));
  EXPECT_CALL(owner_verify_,
              verify(kOwnershipKeyAlgHybridSpxPure, &owner_page[0].owner_key,
                     &expected_sig->signature.hybrid.ecdsa,
                     &expected_sig->signature.hybrid.spx, nullptr, 0, nullptr,
                     0, message_, sizeof(message_), _, &flash_exec_))
      .WillOnce(Return(kErrorOk));
  ExpectWindowRestore();

  EXPECT_EQ(
      ownership_detached_signature_validate(
          BufferStart(), flash_buf_.size(), /*page=*/0, kOwnershipKeyOwner,
          kTestCommand, &kTestNonce, message_, sizeof(message_), &flash_exec_),
      kErrorOk);
}

TEST_F(OwnershipKeyTest, VerificationFailureStillRestoresRegion) {
  WriteDetachedSigAtPage(0, MakeDetachedSig(kTestCommand, kTestNonce));

  ExpectWindowSave();
  ExpectWindowConfig(kMultiBitBool4True);
  EXPECT_CALL(hmac_, sha256(message_, sizeof(message_), _));
  EXPECT_CALL(owner_verify_,
              verify(kOwnershipKeyAlgHybridSpxPure, &owner_page[0].unlock_key,
                     NotNull(), NotNull(), nullptr, 0, nullptr, 0, message_,
                     sizeof(message_), _, &flash_exec_))
      .WillOnce(Return(kErrorOwnershipInvalidSignature));
  EXPECT_CALL(owner_verify_,
              verify(kOwnershipKeyAlgHybridSpxPure, &owner_page[0].owner_key,
                     NotNull(), NotNull(), nullptr, 0, nullptr, 0, message_,
                     sizeof(message_), _, &flash_exec_))
      .WillOnce(Return(kErrorOwnershipInvalidSignature));
  ExpectWindowRestore();

  EXPECT_EQ(
      ownership_detached_signature_validate(
          BufferStart(), flash_buf_.size(), /*page=*/0, kOwnershipKeyUnlock,
          kTestCommand, &kTestNonce, message_, sizeof(message_), &flash_exec_),
      kErrorOwnershipInvalidSignature);
}

TEST_F(OwnershipKeyTest, InvalidAlgorithmStillRestoresRegion) {
  owner_page[0].ownership_key_alg = 0;
  WriteDetachedSigAtPage(0, MakeDetachedSig(kTestCommand, kTestNonce));

  ExpectWindowSave();
  ExpectWindowConfig(kMultiBitBool4True);
  ExpectWindowRestore();

  EXPECT_EQ(
      ownership_detached_signature_validate(
          BufferStart(), flash_buf_.size(), /*page=*/0, kOwnershipKeyOwner,
          kTestCommand, &kTestNonce, message_, sizeof(message_), &flash_exec_),
      kErrorOwnershipInvalidAlgorithm);
}

}  // namespace
