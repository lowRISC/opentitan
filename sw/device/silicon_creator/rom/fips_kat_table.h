// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_FIPS_KAT_TABLE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_FIPS_KAT_TABLE_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /**
   * Magic number identifying the FIPS KAT descriptor table ("FKAT" in ASCII).
   */
  kFipsKatDescriptorMagic = 0x464B4154,
  /**
   * Supported version for the FIPS KAT descriptor table structure.
   */
  kFipsKatDescriptorVersion1 = 1,
};

/**
 * Unique identifiers for cryptographic algorithms with KAT vectors.
 *
 * NOTE: Values are permanent tokens on taped-out silicon. Never renumber or
 * reorder existing values.
 */
typedef enum fips_kat_alg_id {
  kFipsKatAlgNone = 0,
} fips_kat_alg_id_t;

/**
 * Entry describing the location of a single algorithm test vector payload.
 */
typedef struct fips_kat_entry {
  uint32_t algorithm_id;  // fips_kat_alg_id_t
  uint32_t offset;        // Offset in bytes from start of descriptor table
  uint32_t size;          // Size of serialized data block in bytes
} fips_kat_entry_t;

/**
 * Root table located in ROM describing all embedded KAT vectors.
 */
typedef struct fips_kat_descriptor_table {
  uint32_t magic;        // Must be kFipsKatDescriptorMagic (0x464B4154)
  uint32_t version;      // Must be kFipsKatDescriptorVersion1 (1)
  uint32_t entry_count;  // Number of entries in entries[]
  uint32_t total_size;   // Total size of .fips_kat section in bytes
  fips_kat_entry_t entries[];
} fips_kat_descriptor_table_t;

/**
 * Fixed address slot storing the pointer to the FIPS KAT descriptor table.
 * Placed at _rom_chip_info_start - 4 (132 bytes from the end of ROM).
 */
#ifndef FIPS_KAT_DESCRIPTOR_PTR_ADDR
#define FIPS_KAT_DESCRIPTOR_PTR_ADDR     \
  (TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR + \
   TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES - 132)
#endif

/**
 * Validates a FIPS KAT descriptor table structure in memory.
 *
 * @param table Pointer to descriptor table.
 * @return True if table passes alignment, magic, version, and entry bounds.
 */
static inline bool validate_fips_descriptor_table(
    const fips_kat_descriptor_table_t *table) {
  if (table == NULL || ((uintptr_t)table & 0x3) != 0) {
    return false;
  }
  if (table->magic != kFipsKatDescriptorMagic ||
      table->version != kFipsKatDescriptorVersion1 ||
      table->total_size < sizeof(fips_kat_descriptor_table_t)) {
    return false;
  }
  uint32_t max_entries =
      (table->total_size - sizeof(fips_kat_descriptor_table_t)) /
      sizeof(fips_kat_entry_t);
  return table->entry_count <= max_entries;
}

/**
 * Returns a pointer to the FIPS KAT descriptor table referenced at `ptr_addr`,
 * after validating alignment, magic number, version, and total size.
 *
 * @param ptr_addr Address of the 4-byte pointer slot.
 * @return Pointer to table if valid, NULL otherwise.
 */
static inline const fips_kat_descriptor_table_t *
get_fips_descriptor_table_from_address(uintptr_t ptr_addr) {
  if (ptr_addr == 0 || (ptr_addr & 0x3) != 0) {
    return NULL;
  }
  const fips_kat_descriptor_table_t *const *table_ptr =
      (const fips_kat_descriptor_table_t *const *)ptr_addr;
  const fips_kat_descriptor_table_t *table = *table_ptr;
  if (!validate_fips_descriptor_table(table)) {
    return NULL;
  }
  return table;
}

/**
 * Returns a pointer to the FIPS KAT descriptor table from the fixed ROM pointer
 * slot FIPS_KAT_DESCRIPTOR_PTR_ADDR, validating table != NULL, table->magic ==
 * kFipsKatDescriptorMagic, table->version == 1, and table->total_size > 0.
 *
 * @return Pointer to table if valid, NULL otherwise.
 */
static inline const fips_kat_descriptor_table_t *get_fips_descriptor_table(
    void) {
  return get_fips_descriptor_table_from_address(FIPS_KAT_DESCRIPTOR_PTR_ADDR);
}

/**
 * Searches the descriptor table for an entry matching `alg_id`.
 *
 * @param table Pointer to descriptor table.
 * @param alg_id Algorithm identifier to search for.
 * @return Pointer to entry if found, NULL otherwise.
 */
static inline const fips_kat_entry_t *find_fips_entry(
    const fips_kat_descriptor_table_t *table, fips_kat_alg_id_t alg_id) {
  if (!validate_fips_descriptor_table(table)) {
    return NULL;
  }
  for (size_t i = 0; i < table->entry_count; ++i) {
    if (table->entries[i].algorithm_id == (uint32_t)alg_id) {
      return &table->entries[i];
    }
  }
  return NULL;
}

/**
 * Resolves a pointer to the serialized data payload for `entry`, enforcing
 * 4-byte natural alignment and bounds checks against `table->total_size`.
 *
 * @param table Pointer to descriptor table.
 * @param entry Pointer to entry within the table.
 * @return Pointer to data payload if valid, NULL if unaligned or out of bounds.
 */
static inline const void *get_fips_data(
    const fips_kat_descriptor_table_t *table, const fips_kat_entry_t *entry) {
  if (table == NULL || entry == NULL) {
    return NULL;
  }
  if (((uintptr_t)table & 0x3) != 0 || ((uintptr_t)entry & 0x3) != 0 ||
      (entry->offset & 0x3) != 0) {
    return NULL;
  }
  if (entry->offset > table->total_size ||
      entry->size > table->total_size - entry->offset) {
    return NULL;
  }
  return (const void *)((uintptr_t)table + entry->offset);
}

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_FIPS_KAT_TABLE_H_
