// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/mock_manifest.h"

namespace rom_test {
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
}  // namespace rom_test
