// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/manifest.h"

#include "gtest/gtest.h"

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
            kErrorManifestInternal);

  manifest.image_length = kManifestImageLengthMin - 1;
  EXPECT_EQ(manifest_signed_region_get(&manifest, &signed_region),
            kErrorManifestInternal);
}

TEST(Manifest, EntryPointGet) {
  manifest_t manifest{};

  // FIXME: Update after `entry_point` field is added.
  EXPECT_EQ(manifest_entry_point_address_get(&manifest),
            reinterpret_cast<uintptr_t>(&manifest) + 1152);
}

}  // namespace
}  // namespace manifest_unittest
