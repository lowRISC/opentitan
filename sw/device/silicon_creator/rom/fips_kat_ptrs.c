// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdalign.h>
#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/rom/fips_kat_table.h"

/**
 * Empty initial FIPS KAT descriptor table pinned at `0x60000` in `.fips_kat`.
 * Subsequent commits populate individual algorithm entries and payloads inside
 * this combined ROM blob struct.
 */
typedef struct fips_kat_rom_blob {
  uint32_t magic;
  uint32_t version;
  uint32_t entry_count;
  uint32_t total_size;
} fips_kat_rom_blob_t;

OT_ASSERT_SIZE(fips_kat_rom_blob_t, 16);
static_assert(sizeof(fips_kat_rom_blob_t) <= kFipsKatRegionSize,
              "fips_kat_rom_blob_t exceeds 32 KiB NAPOT ROM window");

#ifdef OT_PLATFORM_RV32
OT_SECTION(".fips_kat")
#endif
OT_USED
alignas(uint32_t) static const fips_kat_rom_blob_t kFipsKatRomBlob = {
    .magic = kFipsKatDescriptorMagic,
    .version = kFipsKatDescriptorVersion1,
    .entry_count = 0,
    .total_size = sizeof(fips_kat_rom_blob_t),
};

#ifndef OT_PLATFORM_RV32
const fips_kat_descriptor_table_t *fips_kat_get_rom_table_for_host_test(void) {
  return (const fips_kat_descriptor_table_t *)&kFipsKatRomBlob;
}
#endif
