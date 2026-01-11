// Copyright lowRISC contributors (OpenTitan project).
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

#include "hw/top/otp_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(lifecycle_state_get(), &boot_data));
  ++boot_data.min_security_version_rom_ext;
  RETURN_IF_ERROR(boot_data_write(&boot_data));
  LOG_INFO("Boot data written, rom_ext version %u\n",
           boot_data.min_security_version_rom_ext);
  return true;
}
