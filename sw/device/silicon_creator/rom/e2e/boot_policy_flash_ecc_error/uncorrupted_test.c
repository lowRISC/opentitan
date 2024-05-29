// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  char *cause = (char *)retention_sram_get()->owner.reserved;
  LOG_INFO("Booted slot=%p; Cause=%s", manifest_def_get(), cause);
  return true;
}
