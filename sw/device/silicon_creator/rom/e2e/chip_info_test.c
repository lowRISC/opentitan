// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/chip_info.h"

#include <stdbool.h>

#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  chip_info_t *chip_info = (chip_info_t *)&_chip_info_start;
  LOG_INFO("Chip Info");
  LOG_INFO("  Version: %x", chip_info->version);
  LOG_INFO("   SCM lo: %x", chip_info->scm_revision.scm_revision_low);
  LOG_INFO("   SCM hi: %x", chip_info->scm_revision.scm_revision_high);

  return chip_info->version == kChipInfoVersion1;
}
