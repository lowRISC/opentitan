// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_DEF_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_DEF_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/manifest.h"

/**
 * Gets the manifest of the current boot stage.
 */
const manifest_t *manifest_def_get(void);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_DEF_H_
