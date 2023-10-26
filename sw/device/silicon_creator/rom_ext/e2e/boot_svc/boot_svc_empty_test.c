// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_empty.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/rom_ext/e2e/boot_svc/boot_svc_test_lib.h"

OTTF_DEFINE_TEST_CONFIG();

static status_t initialize(retention_sram_t *retram, boot_svc_retram_t *state) {
  boot_svc_msg_t msg = {0};
  boot_svc_empty_init(&msg.empty);
  retram->creator.boot_svc_msg = msg;
  state->state = kBootSvcTestStateCheckEmpty;
  rstmgr_reset();
  return INTERNAL();
}

static status_t check_empty(retention_sram_t *retram,
                            boot_svc_retram_t *state) {
  boot_svc_msg_t msg = retram->creator.boot_svc_msg;
  TRY(boot_svc_header_check(&msg.header));
  TRY_CHECK(msg.header.type == kBootSvcEmptyType);
  state->state = kBootSvcTestStateFinal;
  return OK_STATUS();
}

static status_t empty_message_test(void) {
  retention_sram_t *retram = retention_sram_get();
  TRY(boot_svc_test_init(retram, kBootSvcTestEmpty));
  boot_svc_retram_t *state = (boot_svc_retram_t *)&retram->owner;

  for (;;) {
    LOG_INFO("Test state = %d", state->state);
    switch (state->state) {
      case kBootSvcTestStateInit:
        TRY(initialize(retram, state));
        break;
      case kBootSvcTestStateCheckEmpty:
        TRY(check_empty(retram, state));
        break;
      case kBootSvcTestStateFinal:
        LOG_INFO("FinalBootLog: %d:%s", state->boots, state->partition);
        return OK_STATUS();
      default:
        return UNKNOWN();
    }
  }
}

bool test_main(void) {
  status_t sts = empty_message_test();
  if (status_err(sts)) {
    LOG_ERROR("empty_message_test: %r", sts);
  }
  return status_ok(sts);
}
