// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/manifest.h"

#include "gtest/gtest.h"
#include "sw/device/lib/testing/mask_rom_test.h"

namespace manifest_unittest {
namespace {

class ManifestTest : public mask_rom_test::MaskRomTest {
 protected:
  ManifestTest() {
    manifest_.length = 0x1000;
    manifest_.code_start = 0x400;
    manifest_.code_end = 0x800;
    manifest_.entry_point = 0x500;
  }

  manifest_t manifest_{};
};

TEST_F(ManifestTest, SignedRegionGet) {
  manifest_signed_region_t signed_region =
      manifest_signed_region_get(&manifest_);

  // Signed region starts after `signature` and ends at the end of the image.
  EXPECT_EQ(signed_region.start, reinterpret_cast<const char *>(&manifest_) +
                                     sizeof(manifest_t::signature));
  EXPECT_EQ(signed_region.length,
            manifest_.length - sizeof(manifest_t::signature));
}

TEST_F(ManifestTest, CodeRegionGet) {
  epmp_region_t code_region = manifest_code_region_get(&manifest_);

  EXPECT_EQ(code_region.start,
            reinterpret_cast<uintptr_t>(&manifest_) + manifest_.code_start);
  EXPECT_EQ(code_region.end,
            reinterpret_cast<uintptr_t>(&manifest_) + manifest_.code_end);
}

TEST_F(ManifestTest, EntryPointGet) {
  uintptr_t entry_point = manifest_entry_point_get(&manifest_);

  EXPECT_EQ(entry_point,
            reinterpret_cast<uintptr_t>(&manifest_) + manifest_.entry_point);
}

TEST_F(ManifestTest, BadLength) {
  manifest_.length = MANIFEST_LENGTH_FIELD_MAX + 1;
  EXPECT_EQ(manifest_check(&manifest_), kErrorManifestBadLength);

  manifest_.length = MANIFEST_LENGTH_FIELD_MIN - 1;
  EXPECT_EQ(manifest_check(&manifest_), kErrorManifestBadLength);
}

TEST_F(ManifestTest, CodeRegionEmpty) {
  manifest_.code_start = manifest_.code_end;
  EXPECT_EQ(manifest_check(&manifest_), kErrorManifestBadCodeRegion);
}

TEST_F(ManifestTest, CodeRegionInsideManifest) {
  manifest_.code_start = sizeof(manifest_) - 1;
  EXPECT_EQ(manifest_check(&manifest_), kErrorManifestBadCodeRegion);
}

TEST_F(ManifestTest, CodeRegionOutsideImage) {
  manifest_.code_end = manifest_.length + 1;
  EXPECT_EQ(manifest_check(&manifest_), kErrorManifestBadCodeRegion);
}

TEST_F(ManifestTest, CodeRegionUnalignedStart) {
  ++manifest_.code_start;
  EXPECT_EQ(manifest_check(&manifest_), kErrorManifestBadCodeRegion);
}

TEST_F(ManifestTest, CodeRegionUnalignedEnd) {
  ++manifest_.code_end;
  EXPECT_EQ(manifest_check(&manifest_), kErrorManifestBadCodeRegion);
}

TEST_F(ManifestTest, EntryPointBeforeCodeStart) {
  manifest_.entry_point = manifest_.code_start - 1;
  EXPECT_EQ(manifest_check(&manifest_), kErrorManifestBadEntryPoint);
}

TEST_F(ManifestTest, EntryPointAfterCodeEnd) {
  manifest_.entry_point = manifest_.code_end;
  EXPECT_EQ(manifest_check(&manifest_), kErrorManifestBadEntryPoint);
}

TEST_F(ManifestTest, EntryPointOutsideImage) {
  manifest_.entry_point = manifest_.length;
  EXPECT_EQ(manifest_check(&manifest_), kErrorManifestBadEntryPoint);
}

TEST_F(ManifestTest, EntryPointUnaligned) {
  ++manifest_.entry_point;
  EXPECT_EQ(manifest_check(&manifest_), kErrorManifestBadEntryPoint);
}

}  // namespace
}  // namespace manifest_unittest
