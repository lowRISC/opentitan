// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/flash_exec.h"

#include "sw/device/lib/base/macros.h"

#include "flash_ctrl_regs.h"

OT_ASSERT_ENUM_VALUE(kSigverifyFlashExec, FLASH_CTRL_PARAM_EXEC_EN);
