// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/manifest_def.h"

#include <stdint.h>

/*
 * Declarations for the manifest fields populdated by the linker script.
 */
extern char _manifest_code_start[];
extern char _manifest_code_end[];
extern char _manifest_entry_point[];

/**
 * Manifest definition.
 *
 * Definition of the manifest that resides in the `.manifest` section. The
 * initializer should explicitly specify the initial values of the members whose
 * values are known a compilation time, such as `code_start`, `code_end`, and
 * `entry_point`. The remaining fields will be updated in the binary by
 * `opentitantool` (overriding the implicitly specified initial value of zero).
 */
OT_SECTION(".manifest")
static manifest_t kManifest_ = {
    .code_start = (uint32_t)_manifest_code_start,
    .code_end = (uint32_t)_manifest_code_end,
    .entry_point = (uint32_t)_manifest_entry_point,
};

const manifest_t *manifest_def_get(void) { return &kManifest_; }
