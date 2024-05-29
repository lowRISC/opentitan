// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

OTTF_DEFINE_TEST_CONFIG();

status_t boot_log_print(boot_log_t *boot_log) {
  TRY(boot_log_check(boot_log));
  LOG_INFO("boot_log identifier = %C", boot_log->identifier);
  LOG_INFO("boot_log chip_version = %08x%08x",
           boot_log->chip_version.scm_revision_high,
           boot_log->chip_version.scm_revision_low);

  LOG_INFO("boot_log rom_ext_slot = %C", boot_log->rom_ext_slot);
  LOG_INFO("boot_log rom_ext_version = %d.%d", boot_log->rom_ext_major,
           boot_log->rom_ext_minor);
  LOG_INFO("boot_log rom_ext_size = 0x%08x", boot_log->rom_ext_size);
  LOG_INFO("boot_log rom_ext_nonce = %08x%08x",
           boot_log->rom_ext_nonce.value[1], boot_log->rom_ext_nonce.value[0]);
  LOG_INFO("boot_log bl0_slot = %C", boot_log->bl0_slot);
  LOG_INFO("boot_log ownership_state = %C", boot_log->ownership_state);
  LOG_INFO("boot_log ownership_transfers = %u", boot_log->ownership_transfers);
  LOG_INFO("boot_log rom_ext_min_sec_ver = %u", boot_log->rom_ext_min_sec_ver);
  LOG_INFO("boot_log bl0_min_sec_ver = %u", boot_log->bl0_min_sec_ver);
  LOG_INFO("boot_log primary_bl0_slot = %C", boot_log->primary_bl0_slot);
  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = boot_log_print(&retention_sram_get()->creator.boot_log);
  if (status_err(sts)) {
    LOG_ERROR("boot_log_print: %r", sts);
  }
  return status_ok(sts);
}
