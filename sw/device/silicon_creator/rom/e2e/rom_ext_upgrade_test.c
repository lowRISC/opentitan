// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "otp_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(lifecycle_state_get(), &boot_data));
  LOG_INFO("ROM_EXT booted min_security_version_rom_ext:%d",
           boot_data.min_security_version_rom_ext);
  ++boot_data.min_security_version_rom_ext;
  RETURN_IF_ERROR(boot_data_write(&boot_data));
  RETURN_IF_ERROR(boot_data_read(kLcStateProd, &boot_data));
  LOG_INFO("Upgraded min_security_version_rom_ext:%d",
           boot_data.min_security_version_rom_ext);
  LOG_INFO("Resetting...");
  rstmgr_reset();
  OT_UNREACHABLE();
  return true;
}
