// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/manifest.h"

#include "sw/device/silicon_creator/lib/base/chip.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static_assert(MANIFEST_LENGTH_FIELD_ROM_EXT_MIN >= MANIFEST_SIZE,
              "`MANIFEST_LENGTH_FIELD_ROM_EXT_MIN` is too small");
static_assert(MANIFEST_LENGTH_FIELD_ROM_EXT_MAX >=
                  MANIFEST_LENGTH_FIELD_ROM_EXT_MIN,
              "`MANIFEST_LENGTH_FIELD_ROM_EXT_MAX` is too small");
static_assert(MANIFEST_LENGTH_FIELD_OWNER_STAGE_MIN >= MANIFEST_SIZE,
              "`MANIFEST_LENGTH_FIELD_OWNER_STAGE_MIN` is too small");
static_assert(MANIFEST_LENGTH_FIELD_OWNER_STAGE_MAX >=
                  MANIFEST_LENGTH_FIELD_OWNER_STAGE_MIN,
              "`MANIFEST_LENGTH_FIELD_OWNER_STAGE_MAX` is too small");
static_assert(MANIFEST_LENGTH_FIELD_OWNER_STAGE_MAX <=
                  ((TOP_EARLGREY_EFLASH_SIZE_BYTES / 2) -
                   MANIFEST_LENGTH_FIELD_ROM_EXT_MAX),
              "`MANIFEST_LENGTH_FIELD_OWNER_STAGE_MAX` is too large");

// Extern declarations for the inline functions in the manifest header.
extern rom_error_t manifest_check(const manifest_t *manifest);
extern manifest_digest_region_t manifest_digest_region_get(
    const manifest_t *manifest);
extern epmp_region_t manifest_code_region_get(const manifest_t *manifest);
extern uintptr_t manifest_entry_point_get(const manifest_t *manifest);
