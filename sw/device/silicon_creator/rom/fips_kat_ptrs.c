// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdalign.h>
#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/rom/fips_kat_table.h"

#define FIPS_KAT_NUM_ENTRIES 0

/**
 * Concrete descriptor table in ROM holding 0 entries initially.
 */
typedef struct fips_kat_rom_table {
  uint32_t magic;
  uint32_t version;
  uint32_t entry_count;
  uint32_t total_size;
  fips_kat_entry_t entries[FIPS_KAT_NUM_ENTRIES];
} fips_kat_rom_table_t;

OT_SECTION(".fips_kat.table")
OT_USED
alignas(uint32_t) static const fips_kat_rom_table_t kFipsKatDescriptorTable = {
    .magic = kFipsKatDescriptorMagic,
    .version = kFipsKatDescriptorVersion1,
    .entry_count = FIPS_KAT_NUM_ENTRIES,
    .total_size = sizeof(fips_kat_rom_table_t),
    .entries = {},
};

/**
 * Fixed pointer to the FIPS KAT descriptor table placed at
 * `_rom_chip_info_start - 4`.
 */
OT_SECTION(".fips_kat_descriptor_ptr")
OT_USED
const fips_kat_descriptor_table_t *const kFipsKatDescriptorPtr =
    (const fips_kat_descriptor_table_t *)&kFipsKatDescriptorTable;
