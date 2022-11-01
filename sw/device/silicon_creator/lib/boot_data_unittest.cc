// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_data.h"

#include <array>
#include <cstring>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

bool operator==(flash_ctrl_perms_t lhs, flash_ctrl_perms_t rhs) {
  return std::memcmp(&lhs, &rhs, sizeof(flash_ctrl_perms_t)) == 0;
}

bool operator==(boot_data_t lhs, boot_data_t rhs) {
  return std::memcmp(&lhs, &rhs, sizeof(boot_data_t)) == 0;
}

/**
 * Example boot data entry with the first `.counter` value.
 */
constexpr boot_data_t kValidEntry0 = {
    .digest = {kBootDataIdentifier, kBootDataIdentifier, kBootDataIdentifier,
               0x00000000, 0x11111111, 0x22222222, 0x33333333, 0x44444444},
    .is_valid = kBootDataValidEntry,
    .identifier = kBootDataIdentifier,
    .counter = kBootDataDefaultCounterVal,
    .min_security_version_rom_ext = 0,
    .min_security_version_bl0 = 0,
};

/**
 * Example boot data entry with a _higher_ `.counter` value.
 */
constexpr boot_data_t kValidEntry1 = {
    .digest = {kBootDataIdentifier, kBootDataIdentifier, kBootDataIdentifier,
               0x44444444, 0x33333333, 0x22222222, 0x11111111, 0x00000000},
    .is_valid = kBootDataValidEntry,
    .identifier = kBootDataIdentifier,
    .counter = kBootDataDefaultCounterVal + 1,
    .min_security_version_rom_ext = 0,
    .min_security_version_bl0 = 0,
};

/**
 * Default boot data entry loaded by `boot_data_default_get`.
 */
constexpr boot_data_t kDefaultEntry = {
    .digest = {kBootDataIdentifier, kBootDataIdentifier, kBootDataIdentifier,
               0xcc761df1, 0xff42f0f2, 0x3f1955ee, 0x9465b3e7, 0x81ce0fdb},
    .is_valid = kBootDataValidEntry,
    .identifier = kBootDataIdentifier,
    .counter = kBootDataDefaultCounterVal,
    .min_security_version_rom_ext = 0x01234567,
    .min_security_version_bl0 = 0x89abcdef,
};

namespace boot_data_unittest {
namespace {
using ::testing::_;
using ::testing::DoAll;
using ::testing::Return;
using ::testing::SetArgPointee;

class BootDataTest : public rom_test::RomTest {
 protected:
  rom_test::MockFlashCtrl flash_ctrl_;
  rom_test::MockHmac hmac_;
  rom_test::MockOtp otp_;

  // Data for an entry which is fully erased.
  std::array<uint32_t, kBootDataNumWords> erased_entry_ = {};
  // Data for a non-erased but non-bootable entry.
  std::array<uint32_t, kBootDataNumWords> non_erased_entry_ = {};
  // Data for a `boot_data_t` entry with only the first three words erased.
  std::array<uint32_t, kBootDataNumWords> part_erased_entry_ = {};

  BootDataTest() {
    std::fill_n(erased_entry_.begin(), kBootDataNumWords, kFlashCtrlErasedWord);
    std::fill_n(non_erased_entry_.begin(), kBootDataNumWords, 0x01234567);
    std::fill_n(part_erased_entry_.begin(), kBootDataNumWords, 0x01234567);
    std::fill_n(part_erased_entry_.begin(), 3, kFlashCtrlErasedWord);
  }

  /**
   * Sets an expectation that a given boot data entry in the given info page
   * is read. The data and return value given by the read can be specified.
   *
   * @param page   The info page containing the boot data entry.
   * @param index  The index of the boot data entry in the page.
   * @param offset Offset into the boot data entry expected to be read from.
   * @param data   Mock data to be read at this entry. The number of words is
   *               unchecked and can be less than (or greater) than the boot
   *               data entry size.
   * @param error  Value to be returned by the read.
   * @param count  Optionally the number of values expected to be read from the
   *               start of the entry. Useful for expecting sniffs.
   */
  void ExpectRead(flash_ctrl_info_page_t page, size_t index,
                  std::array<uint32_t, kBootDataNumWords> data,
                  rom_error_t error) {
    size_t offset = index * sizeof(boot_data_t);

    // Mock out flash_ctrl_page_info_read to pass the given `data` and return
    // the given `error`.
    //
    // Using a lambda rather than `.SetArrayArgument(...).Return(error)`
    // because we have to cast the `void*` argument to a real pointer type
    // before we can write to it.
    EXPECT_CALL(flash_ctrl_, InfoRead(page, offset, kBootDataNumWords, _))
        .WillOnce([data, error](auto, auto, auto, void *out) {
          uint32_t *out_words = static_cast<uint32_t *>(out);
          std::copy_n(data.begin(), kBootDataNumWords, out_words);
          return error;
        });
  }

  /**
   * Sets an expectation that a given boot data entry in an info page was
   * sniffed (i.e. with `boot_data_sniff`).
   *
   * @param page  The info page containing the boot entry.
   * @param index The index of the boot info entry in the page.
   * @param data  Data of the boot data entry (only first three words read).
   * @param error Value to be returned by the read.
   */
  template <size_t N>
  void ExpectSniff(flash_ctrl_info_page_t page, size_t index,
                   std::array<uint32_t, N> data, rom_error_t error) {
    static_assert(N > 3, "Data must be at least three words for a sniff");

    constexpr uint32_t kIsValidOffset = offsetof(boot_data_t, is_valid);
    size_t offset = index * sizeof(boot_data_t) + kIsValidOffset;

    // As with `ExpectRead`, provide the given `data` and `error` using a lambda
    // to support casting the `void*` parameter before writing.
    EXPECT_CALL(flash_ctrl_, InfoRead(page, offset, 3, _))
        .WillOnce([data, error](auto, auto, auto, void *out) {
          uint32_t *out_words = static_cast<uint32_t *>(out);
          std::copy_n(data.begin(), 3, out_words);
          return error;
        });
  }

  /**
   * Sets an expectation that a digest for the given `boot` data is computed.
   *
   * @param boot_data The boot data expected to be used in computation.
   * @param valid     Whether the mocked digest computed should match.
   */
  void ExpectDigestCompute(boot_data_t boot_data, bool valid) {
    constexpr size_t kDigestRegionOffset = sizeof(boot_data.digest);
    constexpr size_t kDigestRegionSize =
        sizeof(boot_data_t) - kDigestRegionOffset;

    EXPECT_CALL(hmac_, sha256_init());

    // Check the post-digest data we're computing with matches what's given.
    EXPECT_CALL(hmac_, sha256_update(_, kDigestRegionSize))
        .WillOnce(DoAll([boot_data](const void *digest_region, size_t size) {
          int digest_region_cmp = std::memcmp(
              digest_region,
              reinterpret_cast<const char *>(&boot_data) + kDigestRegionOffset,
              kDigestRegionSize);
          EXPECT_EQ(digest_region_cmp, 0);
          return kErrorOk;
        }));

    // If mocking as invalid, break the digest.
    hmac_digest_t digest = boot_data.digest;
    if (!valid) {
      digest.digest[0] += 1;
    }

    EXPECT_CALL(hmac_, sha256_final(_))
        .WillOnce(DoAll(SetArgPointee<0>(digest), Return(kErrorOk)));
  }

  /**
   * Sets an expectation that the given page's permissions are set to the given
   * values for `read`, `write`, and `erase`.
   *
   * @param page  The page whose permissions are expected to be set.
   * @param read  Expected setting for the `.read` permission.
   * @param write Expected setting for the `.write` permission.
   * @param erase Expected setting for the `.erase` permission.
   */
  void ExpectPermsSet(flash_ctrl_info_page_t page, bool read, bool write,
                      bool erase) {
    flash_ctrl_perms_t perms = {
        .read = read ? kMultiBitBool4True : kMultiBitBool4False,
        .write = write ? kMultiBitBool4True : kMultiBitBool4False,
        .erase = erase ? kMultiBitBool4True : kMultiBitBool4False,
    };
    EXPECT_CALL(flash_ctrl_, InfoPermsSet(page, perms));
  }

  /**
   * Sets an expectation that the given page is searched for its last valid boot
   * data entry.
   *
   * This acts as a wrapper around the provided function which should contain
   * the expectations of sniffs and reads that happen within the given page.
   *
   * @param page  The page expected to be searched for boot data entries.
   * @param reads Function given the `page` containing expectations of the reads
   *              happening there.
   */
  void ExpectPageScan(flash_ctrl_info_page_t page,
                      std::function<void(flash_ctrl_info_page_t)> reads) {
    ExpectPermsSet(page, true, false, false);
    reads(page);
    ExpectPermsSet(page, false, false, false);
  }

  /**
   * Provides a lambda function mocking a page containing various boot
   * data entries (all non-bootable or invalid) plus the given `boot_data` which
   * is expected to be bootable.
   *
   * @param boot_data    Bootable boot data entry to be inserted into the page.
   * @param valid_digest Whether to mock that `boot_data`'s digest is valid.
   * @return Lambda function for use with `ExpectPageScan`.
   */
  auto EntryPage(boot_data_t boot_data, bool valid_digest = true) {
    // Ensures the following memcpy is safe
    static_assert(sizeof(uint32_t) * kBootDataNumWords == sizeof(boot_data_t),
                  "`kBootDataNumWords` must match size of `boot_data_t`");

    // Convert the given boot data into an array of words.
    std::array<uint32_t, kBootDataNumWords> boot_data_raw = {};
    std::memcpy(boot_data_raw.data(), &boot_data, sizeof(boot_data_t));

    // Mock the page to have the following layout:
    // #0. Non-erased but non-bootable.
    // #1. Non-erased and bootable provided boot_data.
    // #2. Non-erased and bootable but invalid digest.
    // #3. Entry with sniffed area erased but the rest not.
    // #4. Fully erased entry.
    return [=](flash_ctrl_info_page_t page) {
      // Expect to sniff each entry, fully reading if it could be erased.
      ExpectSniff(page, 0, non_erased_entry_, kErrorOk);
      ExpectSniff(page, 1, boot_data_raw, kErrorOk);
      ExpectSniff(page, 2, boot_data_raw, kErrorOk);
      ExpectSniff(page, 3, part_erased_entry_, kErrorOk);
      ExpectRead(page, 3, part_erased_entry_, kErrorOk);
      ExpectSniff(page, 4, erased_entry_, kErrorOk);
      ExpectRead(page, 4, erased_entry_, kErrorOk);

      // Check the last seen bootable entry's digest (mocked as invalid).
      ExpectRead(page, 2, boot_data_raw, kErrorOk);
      ExpectDigestCompute(boot_data, false);

      // Step back to the previously seen bootable entry (provided `boot_data`).
      ExpectRead(page, 1, boot_data_raw, kErrorOk);
      ExpectDigestCompute(boot_data, valid_digest);
    };
  }

  /**
   * Provides a lambda function mocking a page with only an erased entry.
   *
   * @return Lambda function for use with `ExpectPageScan`.
   */
  auto ErasedPage() {
    return [this](auto page) {
      ExpectSniff(page, 0, erased_entry_, kErrorOk);
      ExpectRead(page, 0, erased_entry_, kErrorOk);
    };
  }

  /**
   * Sets an expectation that the device queries for whether the default boot
   * data entry should be loaded when in the `prod` lifecycle state.
   *
   * @param allowed_in_prod Whether loading the default entry should be allowed.
   */
  void ExpectAllowedInProdCheck(bool allowed_in_prod) {
    EXPECT_CALL(
        otp_,
        read32(
            OTP_CTRL_PARAM_CREATOR_SW_CFG_DEFAULT_BOOT_DATA_IN_PROD_EN_OFFSET))
        .WillOnce(
            Return(allowed_in_prod ? kHardenedBoolTrue : kHardenedBoolFalse));
  }

  /**
   * Sets an expectation that the default boot data entry is loaded and its
   * digest is checked.
   */
  void ExpectDefaultEntryRead() {
    EXPECT_CALL(
        otp_, read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_MIN_SEC_VER_ROM_EXT_OFFSET))
        .WillOnce(Return(kDefaultEntry.min_security_version_rom_ext));
    EXPECT_CALL(otp_,
                read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_MIN_SEC_VER_BL0_OFFSET))
        .WillOnce(Return(kDefaultEntry.min_security_version_bl0));

    ExpectDigestCompute(kDefaultEntry, true);
  }
};

class BootDataReadTest : public BootDataTest {};

TEST_F(BootDataReadTest, ReadBothValidTest1) {
  // Expect both pages to be checked, with both giving valid entries.
  ExpectPageScan(kFlashCtrlInfoPageBootData0, EntryPage(kValidEntry0));
  ExpectPageScan(kFlashCtrlInfoPageBootData1, EntryPage(kValidEntry1));

  boot_data_t boot_data = {{0}};
  EXPECT_EQ(boot_data_read(kLcStateTest, &boot_data), kErrorOk);
  // Expect the entry with the higher `.counter` to have been selected.
  EXPECT_EQ(boot_data, kValidEntry1);
}

TEST_F(BootDataReadTest, ReadBothValidTest2) {
  // Same as above, but swap which page contains `test_entry_1`.
  ExpectPageScan(kFlashCtrlInfoPageBootData0, EntryPage(kValidEntry1));
  ExpectPageScan(kFlashCtrlInfoPageBootData1, EntryPage(kValidEntry0));

  boot_data_t boot_data = {{0}};
  EXPECT_EQ(boot_data_read(kLcStateTest, &boot_data), kErrorOk);
  // Expect the entry with the higher `.counter` to have been selected.
  EXPECT_EQ(boot_data, kValidEntry1);
}

TEST_F(BootDataReadTest, ReadOneEntryTest) {
  // Expect both pages to be searched, but give only a valid entry for one.
  ExpectPageScan(kFlashCtrlInfoPageBootData0, EntryPage(kValidEntry0));
  ExpectPageScan(kFlashCtrlInfoPageBootData1, ErasedPage());

  boot_data_t boot_data = {{0}};
  EXPECT_EQ(boot_data_read(kLcStateTest, &boot_data), kErrorOk);
  EXPECT_EQ(boot_data, kValidEntry0);
}

TEST_F(BootDataReadTest, ReadOneValidTest) {
  // Expect both pages to be searched, but give only a valid entry for one.
  ExpectPageScan(kFlashCtrlInfoPageBootData0, EntryPage(kValidEntry0));
  ExpectPageScan(kFlashCtrlInfoPageBootData1, EntryPage(kValidEntry1, false));

  boot_data_t boot_data = {{0}};
  EXPECT_EQ(boot_data_read(kLcStateTest, &boot_data), kErrorOk);
  // `...BootData1` had an entry with a higher `.counter`, but it has an
  // invalid digest and should not be chosen.
  EXPECT_EQ(boot_data, kValidEntry0);
}

TEST_F(BootDataReadTest, ReadErasedDefaultTest) {
  // Expect both pages to be searched, but give no entry for either.
  ExpectPageScan(kFlashCtrlInfoPageBootData0, ErasedPage());
  ExpectPageScan(kFlashCtrlInfoPageBootData1, ErasedPage());

  // Expect to fall back to loading the default entry.
  ExpectAllowedInProdCheck(false);
  ExpectDefaultEntryRead();

  boot_data_t boot_data = {{0}};
  EXPECT_EQ(boot_data_read(kLcStateTest, &boot_data), kErrorOk);
  EXPECT_EQ(boot_data, kDefaultEntry);
}

TEST_F(BootDataReadTest, ReadInvalidDefaultTest) {
  // Expect both pages to be searched, but give invalid entries for both.
  ExpectPageScan(kFlashCtrlInfoPageBootData0, EntryPage(kValidEntry0, false));
  ExpectPageScan(kFlashCtrlInfoPageBootData1, EntryPage(kValidEntry1, false));

  // Expect to fall back to loading the default entry.
  ExpectAllowedInProdCheck(false);
  ExpectDefaultEntryRead();

  boot_data_t boot_data = {{0}};
  EXPECT_EQ(boot_data_read(kLcStateTest, &boot_data), kErrorOk);
  EXPECT_EQ(boot_data, kDefaultEntry);
}

TEST_F(BootDataReadTest, ReadDefaultAllowedInProdTest) {
  // Expect both pages to be searched, but give no entry for either.
  ExpectPageScan(kFlashCtrlInfoPageBootData0, ErasedPage());
  ExpectPageScan(kFlashCtrlInfoPageBootData1, ErasedPage());

  // Expect to fall back to loading the default entry (allowed in prod).
  ExpectAllowedInProdCheck(true);
  ExpectDefaultEntryRead();

  boot_data_t boot_data = {{0}};
  EXPECT_EQ(boot_data_read(kLcStateProd, &boot_data), kErrorOk);
  EXPECT_EQ(boot_data, kDefaultEntry);
}

TEST_F(BootDataReadTest, ReadDefaultNotAllowedInProdTest) {
  // Expect both pages to be searched, but give no entry for either.
  ExpectPageScan(kFlashCtrlInfoPageBootData0, ErasedPage());
  ExpectPageScan(kFlashCtrlInfoPageBootData1, ErasedPage());

  // Expect to fall back to loading the default entry (now allowed in prod).
  ExpectAllowedInProdCheck(false);
  // Do not expect the default entry to be read.

  boot_data_t boot_data = {{0}};
  EXPECT_EQ(boot_data_read(kLcStateProd, &boot_data), kErrorBootDataNotFound);
}

}  // namespace
}  // namespace boot_data_unittest
