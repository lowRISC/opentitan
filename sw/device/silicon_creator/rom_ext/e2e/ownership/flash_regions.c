// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

dif_flash_ctrl_state_t flash_state;

status_t flash_regions_print(boot_log_t *boot_log, dif_flash_ctrl_state_t *f) {
  TRY(boot_log_check(boot_log));
  LOG_INFO("boot_log rom_ext_slot = %C", boot_log->rom_ext_slot);
  LOG_INFO("boot_log bl0_slot = %C", boot_log->bl0_slot);
  for (uint32_t i = 0; i < 8; ++i) {
    dif_flash_ctrl_data_region_properties_t p;
    bool locked;
    TRY(dif_flash_ctrl_get_data_region_properties(f, i, &p));
    TRY(dif_flash_ctrl_data_region_is_locked(f, i, &locked));
    flash_ctrl_testutils_data_region_print(i, &p, locked);
  }
  for (uint32_t bank = 0; bank < 2; ++bank) {
    for (uint32_t page = 0; page < 10; ++page) {
      dif_flash_ctrl_info_region_t region = {
          .bank = bank,
          .partition_id = 0,
          .page = page,
      };
      bool locked;
      dif_flash_ctrl_region_properties_t p;
      TRY(dif_flash_ctrl_get_info_region_properties(f, region, &p));
      TRY(dif_flash_ctrl_info_region_is_locked(f, region, &locked));
      flash_ctrl_testutils_info_region_print(region, &p, locked);
    }
  }
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  status_t sts = flash_regions_print(&retention_sram_get()->creator.boot_log,
                                     &flash_state);

  if (status_err(sts)) {
    LOG_ERROR("flash_regions_print: %r", sts);
  }
  return status_ok(sts);
}
