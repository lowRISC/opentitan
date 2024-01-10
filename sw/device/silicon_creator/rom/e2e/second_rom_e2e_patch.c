// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "otp_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kRomPatchMaxAddr =
      OTP_CTRL_PARAM_ROM_PATCH_OFFSET + OTP_CTRL_PARAM_ROM_PATCH_SIZE,
};

bool test_main(void) {
  uint32_t rom_patch = otp_read32(kRomPatchMaxAddr - sizeof(uint32_t));

  /* This will fail unless patched */
  if (rom_patch == 0)
    return false;

  rom_patch = otp_read32(kRomPatchMaxAddr - 2 * sizeof(uint32_t));

  /* This will fail unless patched */
  if (rom_patch == 0)
    return false;

  rom_patch = otp_read32(kRomPatchMaxAddr - 3 * sizeof(uint32_t));

  /* This will fail unless patched */
  if (rom_patch == 0)
    return false;

  rom_patch = otp_read32(kRomPatchMaxAddr - 4 * sizeof(uint32_t));

  if (rom_patch != 0)
    return false;

  return true;
}
