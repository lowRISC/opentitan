// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/e2e/boot_svc/boot_svc_test_lib.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

status_t boot_svc_test_init(retention_sram_t *retram, boot_svc_test_t test) {
  boot_log_t *boot_log = &retram->creator.boot_log;
  TRY(boot_log_check(boot_log));

  boot_svc_retram_t *state = (boot_svc_retram_t *)&retram->owner;

  if (bitfield_bit32_read(retram->creator.reset_reasons,
                          kRstmgrReasonPowerOn)) {
    memset(&retram->owner, 0, sizeof(retram->owner));
  }

  if (state->test != 0 && state->test != test) {
    return INTERNAL();
  }

  if (state->test == 0) {
    state->test = test;
    state->state = kBootSvcTestStateInit;
  }
  state->partition[state->boots] = (boot_log->bl0_slot == kBl0BootSlotA) ? 'A'
                                   : (boot_log->bl0_slot == kBl0BootSlotB)
                                       ? 'B'
                                       : 'x';
  state->boots += 1;
  return OK_STATUS();
}
