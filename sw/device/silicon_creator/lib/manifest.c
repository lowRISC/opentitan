// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/manifest.h"

// Extern declarations for the inline functions in the manifest header.
extern rom_error_t manifest_signed_region_get(
    const manifest_t *manifest, manifest_signed_region_t *signed_region);
extern uintptr_t manifest_entry_point_address_get(const manifest_t *manifest);
