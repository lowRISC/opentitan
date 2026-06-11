// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  retention_sram_t *retram = retention_sram_get();

  bool isfb_error = bitfield_bit32_read(retram->creator.boot_log.events,
                                        BOOT_LOG_EVENT_ISFB_ERROR);
  LOG_INFO("ISFB error event raised: %d", isfb_error);

  CHECK(isfb_error,
        "ISFB error event should be raised when linked to isfb_null on an "
        "ISFB-enabled chip");
  return true;
}
