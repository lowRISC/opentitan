// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/cheriot_manifest.h"

#include <stddef.h>

#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/manifest.h"

// CHERIoT assembly images emit their `.manifest` section from the constants
// in `cheriot_manifest.h`, because `manifest.h` does not yet compile for
// CHERIoT. Check the two agree here, where both are available.
static_assert(offsetof(manifest_t, address_translation) ==
                  MANIFEST_ADDRESS_TRANSLATION_OFFSET,
              "address_translation offset moved");
static_assert(offsetof(manifest_t, manifest_version) +
                      offsetof(manifest_version_t, minor) ==
                  MANIFEST_VERSION_MINOR_OFFSET,
              "manifest_version.minor offset moved");
static_assert(offsetof(manifest_t, manifest_version) +
                      offsetof(manifest_version_t, major) ==
                  MANIFEST_VERSION_MAJOR_OFFSET,
              "manifest_version.major offset moved");
static_assert(offsetof(manifest_t, code_start) == MANIFEST_CODE_START_OFFSET,
              "code_start offset moved");
static_assert(offsetof(manifest_t, code_end) == MANIFEST_CODE_END_OFFSET,
              "code_end offset moved");
static_assert(offsetof(manifest_t, entry_point) == MANIFEST_ENTRY_POINT_OFFSET,
              "entry_point offset moved");

static_assert(sizeof(manifest_t) == MANIFEST_SIZE, "manifest size changed");
static_assert(kManifestVersionMinor1 == MANIFEST_VERSION_MINOR_1,
              "manifest minor version changed");
static_assert(kManifestVersionMajor2 == MANIFEST_VERSION_MAJOR_2,
              "manifest major version changed");
