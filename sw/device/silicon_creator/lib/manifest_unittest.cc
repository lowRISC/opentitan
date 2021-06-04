// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/manifest.h"

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/epmp.h"

namespace manifest_unittest {
namespace {

TEST(Manifest, SignedRegionGet) {
  manifest_t manifest{};
  manifest.image_length = 4096;
  manifest_signed_region_t signed_region;

  EXPECT_EQ(manifest_signed_region_get(&manifest, &signed_region), kErrorOk);
  // Signed region starts at `image_length` and ends at the end of the image.
  EXPECT_EQ(&manifest.image_length, signed_region.start);
  EXPECT_EQ(manifest.image_length - offsetof(manifest_t, image_length),
            signed_region.length);
}

TEST(Manifest, SignedRegionGetBadLength) {
  manifest_t manifest{};
  manifest_signed_region_t signed_region;

  manifest.image_length = kManifestImageLengthMax + 1;
  EXPECT_EQ(manifest_signed_region_get(&manifest, &signed_region),
            kErrorManifestBadLength);

  manifest.image_length = kManifestImageLengthMin - 1;
  EXPECT_EQ(manifest_signed_region_get(&manifest, &signed_region),
            kErrorManifestBadLength);
}

TEST(Manifest, CodeRegionGet) {
  manifest_t manifest{};
  manifest.image_length = 0x1000;
  manifest.code_start = 0x400;
  manifest.code_end = 0x800;
  epmp_region_t code_region;

  EXPECT_EQ(manifest_code_region_get(&manifest, &code_region), kErrorOk);
  EXPECT_EQ(code_region.start,
            reinterpret_cast<uintptr_t>(&manifest) + manifest.code_start);
  EXPECT_EQ(code_region.end,
            reinterpret_cast<uintptr_t>(&manifest) + manifest.code_end);
  // Code region cannot be empty.
  manifest.code_start = manifest.code_end;
  EXPECT_EQ(manifest_code_region_get(&manifest, &code_region),
            kErrorManifestBadCodeRegion);
  // Code region must be after the manifest.
  manifest.code_start = sizeof(manifest_t) - 1;
  EXPECT_EQ(manifest_code_region_get(&manifest, &code_region),
            kErrorManifestBadCodeRegion);
  // Code region must be inside the image.
  manifest.code_start = 0x400;
  manifest.code_end = manifest.image_length + 1;
  EXPECT_EQ(manifest_code_region_get(&manifest, &code_region),
            kErrorManifestBadCodeRegion);
  // Start and end offsets must be word aligned.
  manifest.code_start = 0x401;
  manifest.code_end = 0x800;
  EXPECT_EQ(manifest_code_region_get(&manifest, &code_region),
            kErrorManifestBadCodeRegion);
  manifest.code_start = 0x400;
  manifest.code_end = 0x801;
  EXPECT_EQ(manifest_code_region_get(&manifest, &code_region),
            kErrorManifestBadCodeRegion);
}

TEST(Manifest, EntryPointGet) {
  manifest_t manifest{};
  manifest.image_length = 0x1000;
  manifest.code_start = 0x400;
  manifest.entry_point = 0x500;
  manifest.code_end = 0x800;
  uintptr_t entry_point;

  EXPECT_EQ(manifest_entry_point_get(&manifest, &entry_point), kErrorOk);
  EXPECT_EQ(entry_point,
            reinterpret_cast<uintptr_t>(&manifest) + manifest.entry_point);
  // entry_point must be at or after code_start.
  manifest.entry_point = manifest.code_start - 1;
  EXPECT_EQ(manifest_entry_point_get(&manifest, &entry_point),
            kErrorManifestBadEntryPoint);
  // entry_point must be before code_end.
  manifest.entry_point = manifest.code_end;
  EXPECT_EQ(manifest_entry_point_get(&manifest, &entry_point),
            kErrorManifestBadEntryPoint);
  // entry_point must be before the end of the image.
  manifest.entry_point = manifest.image_length;
  EXPECT_EQ(manifest_entry_point_get(&manifest, &entry_point),
            kErrorManifestBadEntryPoint);
  // entry_point must be word aligned.
  manifest.entry_point = 0x501;
  EXPECT_EQ(manifest_entry_point_get(&manifest, &entry_point),
            kErrorManifestBadEntryPoint);
}

}  // namespace
}  // namespace manifest_unittest
