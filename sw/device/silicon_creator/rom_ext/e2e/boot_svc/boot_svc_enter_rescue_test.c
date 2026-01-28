// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_empty.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/rom_ext/e2e/boot_svc/boot_svc_test_lib.h"

OTTF_DEFINE_TEST_CONFIG();

static status_t initialize(retention_sram_t *retram, boot_svc_retram_t *state) {
  boot_svc_msg_t msg = {0};
  boot_svc_enter_rescue_req_init(/*skip_once=*/kHardenedBoolFalse,
                                 &msg.enter_rescue_req);
  retram->creator.boot_svc_msg = msg;
  state->state = kBootSvcTestStateEnterRescue;
  rstmgr_reset();
  return INTERNAL();
}

static status_t enter_rescue_message_test(void) {
  retention_sram_t *retram = retention_sram_get();
  TRY(boot_svc_test_init(retram, kBootSvcTestEmpty));
  boot_svc_retram_t *state = (boot_svc_retram_t *)&retram->owner;

  for (;;) {
    LOG_INFO("Test state = %d", state->state);
    switch (state->state) {
      case kBootSvcTestStateInit:
        TRY(initialize(retram, state));
        break;
      default:
        // We never expect to come back because the test's exit_success is to
        // observe the rescue entry message.
        LOG_INFO("Unexpected State: %d", state->state);
        return UNKNOWN();
    }
  }
}

bool test_main(void) {
  status_t sts = enter_rescue_message_test();
  if (status_err(sts)) {
    LOG_ERROR("enter_rescue_message_test: %r", sts);
  }
  return status_ok(sts);
}
