// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/romextimage.h"

#include "gtest/gtest.h"
#include "sw/device/lib/testing/mask_rom_test.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/mask_rom/mock_romextimage_ptrs.h"

namespace manifest_unittest {
namespace {
using ::testing::Return;

class RomExtImage : public mask_rom_test::MaskRomTest {
 protected:
  mask_rom_test::MockRomextimagePtrs romextimage_ptrs_;
  manifest_t manifest_;
};

TEST_F(RomExtImage, ManifestGet) {
  const manifest_t *act_manifest;
  manifest_.identifier = kRomextimageManifestIdentifier;

  EXPECT_CALL(romextimage_ptrs_, slot_a_manifest_ptr_get)
      .WillOnce(Return(&manifest_));
  EXPECT_EQ(romextimage_manifest_get(kFlashSlotA, &act_manifest), kErrorOk);
  EXPECT_EQ(act_manifest, &manifest_);

  act_manifest = nullptr;
  EXPECT_CALL(romextimage_ptrs_, slot_b_manifest_ptr_get)
      .WillOnce(Return(&manifest_));
  EXPECT_EQ(romextimage_manifest_get(kFlashSlotB, &act_manifest), kErrorOk);
  EXPECT_EQ(act_manifest, &manifest_);
}

TEST_F(RomExtImage, ManifestGetBadIdentifier) {
  const manifest_t *act_manifest;

  EXPECT_CALL(romextimage_ptrs_, slot_a_manifest_ptr_get)
      .WillOnce(Return(&manifest_));
  EXPECT_EQ(romextimage_manifest_get(kFlashSlotA, &act_manifest),
            kErrorRomextimageInternal);

  EXPECT_CALL(romextimage_ptrs_, slot_b_manifest_ptr_get)
      .WillOnce(Return(&manifest_));
  EXPECT_EQ(romextimage_manifest_get(kFlashSlotB, &act_manifest),
            kErrorRomextimageInternal);
}

TEST_F(RomExtImage, ManifestGetBadSlot) {
  const manifest_t *act_manifest;

  EXPECT_EQ(romextimage_manifest_get(static_cast<flash_slot_t>(kFlashSlotB + 1),
                                     &act_manifest),
            kErrorRomextimageInvalidArgument);
}

}  // namespace
}  // namespace manifest_unittest
