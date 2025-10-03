// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/testing/ret_sram_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/build_info.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

OTTF_DEFINE_TEST_CONFIG();

extern const char _chip_info_start[];

bool test_main(void) {
  build_info_t *build_info = (build_info_t *)&_chip_info_start;
  LOG_INFO("ROM Build Info");
  LOG_INFO("  Version: %x", build_info->version);
  LOG_INFO("   SCM lo: %x", build_info->scm_revision.scm_revision_low);
  LOG_INFO("   SCM hi: %x", build_info->scm_revision.scm_revision_high);

  // Make sure that the version is valid.
  CHECK(build_info->version == kBuildInfoVersion1);

  bool is_testrom = false;
  CHECK_STATUS_OK(ret_sram_testutils_is_testrom(&is_testrom));
  if (!is_testrom) {
    boot_log_t *boot_log = &retention_sram_get()->creator.boot_log;
    LOG_INFO("Boot Log Info");
    LOG_INFO("   SCM lo: %x", boot_log->chip_version.scm_revision_low);
    LOG_INFO("   SCM hi: %x", boot_log->chip_version.scm_revision_high);

    // Make sure that the boot log correctly reflects the ROM build info.
    CHECK(build_info->scm_revision.scm_revision_low ==
          boot_log->chip_version.scm_revision_low);
    CHECK(build_info->scm_revision.scm_revision_high ==
          boot_log->chip_version.scm_revision_high);
  } else {
    LOG_INFO("Boot log info check skipped (test_rom detected).");
  }

  return true;
}
