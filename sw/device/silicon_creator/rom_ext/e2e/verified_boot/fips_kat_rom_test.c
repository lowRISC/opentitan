// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/rom/fips_kat_table.h"

OTTF_DEFINE_TEST_CONFIG(.ignore_alerts = true);

bool test_main(void) {
  LOG_INFO("Running FIPS KAT Table E2E Discovery Test...");

  const fips_kat_descriptor_table_t *table = get_fips_descriptor_table();
  CHECK(table != NULL, "FIPS KAT descriptor table pointer is NULL!");
  CHECK(table->magic == kFipsKatDescriptorMagic,
        "Invalid table magic: expected 0x%08x, got 0x%08x",
        kFipsKatDescriptorMagic, table->magic);
  CHECK(table->version == kFipsKatDescriptorVersion1,
        "Invalid table version: expected %u, got %u",
        kFipsKatDescriptorVersion1, table->version);

  LOG_INFO(
      "Found valid FIPS KAT descriptor table at %p (entries: %u, size: %u "
      "bytes)",
      table, table->entry_count, table->total_size);

  return true;
}
