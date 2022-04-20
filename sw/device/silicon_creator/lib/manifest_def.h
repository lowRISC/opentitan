// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_DEF_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_DEF_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/manifest.h"

/**
 * Manifest definition.
 *
 * Declaration of the manifest that resides in the .manifest section. This
 * should be defined with known values, such as `code_start`, `code_end`, and
 * `entry_point`, populated. The remaining fields will be updated in the binary
 * by the signer tool.
 */
extern const volatile manifest_t kManifest OT_SECTION(".manifest");

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_DEF_H_
