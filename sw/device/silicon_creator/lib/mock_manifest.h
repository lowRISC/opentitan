// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_MANIFEST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_MANIFEST_H_

#include "sw/device/lib/base/testing/global_mock.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for manifest.h.
 */
class MockManifest : public global_mock::GlobalMock<MockManifest> {
 public:
  MOCK_METHOD(rom_error_t, Check, (const manifest_t *));
  MOCK_METHOD(manifest_digest_region_t, DigestRegion, (const manifest_t *));
  MOCK_METHOD(epmp_region_t, CodeRegion, (const manifest_t *));
  MOCK_METHOD(uintptr_t, EntryPoint, (const manifest_t *));
};

}  // namespace internal

using MockManifest = testing::StrictMock<internal::MockManifest>;

extern "C" {

rom_error_t manifest_check(const manifest_t *manifest) {
  return MockManifest::Instance().Check(manifest);
}

manifest_digest_region_t manifest_digest_region_get(
    const manifest_t *manifest) {
  return MockManifest::Instance().DigestRegion(manifest);
}

epmp_region_t manifest_code_region_get(const manifest_t *manifest) {
  return MockManifest::Instance().CodeRegion(manifest);
}

uintptr_t manifest_entry_point_get(const manifest_t *manifest) {
  return MockManifest::Instance().EntryPoint(manifest);
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_MANIFEST_H_
