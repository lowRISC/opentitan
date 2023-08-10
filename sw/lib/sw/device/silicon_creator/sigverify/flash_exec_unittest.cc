// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/lib/sw/device/silicon_creator/sigverify/flash_exec.h"

#include "sw/lib/sw/device/silicon_creator/sigverify/rsa_verify.h"
#include "sw/lib/sw/device/silicon_creator/sigverify/spx_verify.h"
#include "sw/lib/sw/device/silicon_creator/testing/rom_test.h"

#include "flash_ctrl_regs.h"

namespace flash_exec_unittest {
namespace {

TEST(FlashExec, MagicValues) {
  EXPECT_EQ(kSigverifyFlashExec, FLASH_CTRL_PARAM_EXEC_EN);
  EXPECT_EQ(kSigverifyRsaSuccess ^ kSigverifySpxSuccess,
            FLASH_CTRL_PARAM_EXEC_EN);
  EXPECT_EQ(kSigverifySpxDisabledOtp, kSigverifySpxSuccess);
}

}  // namespace
}  // namespace flash_exec_unittest
