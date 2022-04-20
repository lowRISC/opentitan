// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/manifest_def.h"

#include <stdint.h>

/*
 * Declarations for the manifest fields populdated by the linker script.
 */
extern const uint32_t _manifest_code_start[];
extern const uint32_t _manifest_code_end[];
extern const uint32_t _manifest_entry_point[];

static_assert(sizeof(uint32_t) == sizeof(uintptr_t), "Pointer is not 32-bits.");

const volatile manifest_t kManifest = {
    .code_start = (uintptr_t)&_manifest_code_start,
    .code_end = (uintptr_t)&_manifest_code_end,
    .entry_point = (uintptr_t)&_manifest_entry_point,
};
