// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "hw/top/dt/rom_ctrl.h"
#include "sw/device/lib/testing/ret_sram_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/build_info.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

OTTF_DEFINE_TEST_CONFIG();

// The following is defined in the linker script. This is really a
// size but the way the accept the linker script variables makes it odd.
extern const char _chip_info_size[];

bool test_main(void) {
  // Assume that the the chip info is at the very end of the first ROM.
  dt_rom_ctrl_t rom = kDtRomCtrlFirst;
  uint32_t rom_base = dt_rom_ctrl_memory_base(rom, kDtRomCtrlMemoryRom);
  uint32_t rom_size = dt_rom_ctrl_memory_size(rom, kDtRomCtrlMemoryRom);
  // Note that the chip info data is at fixed location from the end of the ROM
  // which does *NOT* match the size of the build_info_t structure.
  uint32_t chip_info_start = rom_base + rom_size - (uint32_t)&_chip_info_size;

  build_info_t *build_info = (build_info_t *)chip_info_start;
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
