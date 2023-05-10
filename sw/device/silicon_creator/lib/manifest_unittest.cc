// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/manifest.h"

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace manifest_unittest {
namespace {

class ManifestTest : public rom_test::RomTest {
 protected:
  ManifestTest() {
    manifest_.length = sizeof(manifest_t) + 0x1000;
    manifest_.signed_region_end = sizeof(manifest_t) + 0x900;
    manifest_.code_start = sizeof(manifest_t);
    manifest_.code_end = sizeof(manifest_t) + 0x800;
    manifest_.entry_point = 0x500;
  }

  manifest_t manifest_{};
};

TEST_F(ManifestTest, DigestRegionGet) {
  manifest_digest_region_t digest_region =
      manifest_digest_region_get(&manifest_);

  // Digest region starts immediately after `usage_constraints` and ends at
  // `signed_region_end`.
  size_t digest_region_offset = offsetof(manifest_t, usage_constraints) +
                                sizeof(manifest_t::usage_constraints);
  EXPECT_EQ(digest_region.start,
            reinterpret_cast<const char *>(&manifest_) + digest_region_offset);
  EXPECT_EQ(digest_region.length,
            manifest_.signed_region_end - digest_region_offset);
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
