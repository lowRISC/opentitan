// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/silicon_creator/lib/manifest_def.h"

/*
 * Declarations for the manifest fields populdated by the linker script.
 */
extern const uint32_t _manifest_code_start;
extern const uint32_t _manifest_code_end;
extern const uint32_t _manifest_entry_point;

const volatile manifest_t kManifest = {
    .code_start = (uintptr_t)&_manifest_code_start,
    .code_end = (uintptr_t)(&_manifest_code_end),
    .entry_point = (uintptr_t)(&_manifest_entry_point),
};
