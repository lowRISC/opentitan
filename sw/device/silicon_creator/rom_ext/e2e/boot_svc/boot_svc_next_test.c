// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_next_boot_bl0_slot.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/rom_ext/e2e/boot_svc/boot_svc_test_lib.h"

OTTF_DEFINE_TEST_CONFIG();

static status_t initialize(retention_sram_t *retram, boot_svc_retram_t *state) {
  boot_svc_msg_t msg = {0};
  boot_svc_next_boot_bl0_slot_req_init(kBootSvcNextBootBl0SlotB,
                                       &msg.next_boot_bl0_slot_req);
  retram->creator.boot_svc_msg = msg;
  state->state = kBootSvcTestStateNextSideB;
  rstmgr_reset();
  return INTERNAL();
}

static status_t check_side_b(retention_sram_t *retram,
                             boot_svc_retram_t *state) {
  boot_svc_msg_t msg = retram->creator.boot_svc_msg;
  TRY(boot_svc_header_check(&msg.header));
  TRY_CHECK(msg.header.type == kBootSvcNextBl0SlotResType);
  TRY_CHECK(msg.next_boot_bl0_slot_res.status == kErrorOk);
  TRY_CHECK(state->current_side == 'B');
  state->state = kBootSvcTestStateReturnSideA;
  rstmgr_reset();
  return INTERNAL();
}

static status_t check_return_side_a(retention_sram_t *retram,
                                    boot_svc_retram_t *state) {
  TRY_CHECK(state->current_side == 'A');
  state->state = kBootSvcTestStateFinal;
  return OK_STATUS();
}

static status_t next_bl0_slot_test(void) {
  retention_sram_t *retram = retention_sram_get();
  TRY(boot_svc_test_init(retram, kBootSvcTestEmpty));
  boot_svc_retram_t *state = (boot_svc_retram_t *)&retram->owner;

  for (;;) {
    LOG_INFO("Test state = %d", state->state);
    switch (state->state) {
      case kBootSvcTestStateInit:
        TRY(initialize(retram, state));
        break;
      case kBootSvcTestStateNextSideB:
        TRY(check_side_b(retram, state));
        break;
      case kBootSvcTestStateReturnSideA:
        TRY(check_return_side_a(retram, state));
        break;
      case kBootSvcTestStateFinal:
        LOG_INFO("FinalBootLog: %d:%s", state->boots, state->partition);
        return OK_STATUS();
      default:
        LOG_ERROR("Unknown state: %d", state->state);
        return UNKNOWN();
    }
  }
}

bool test_main(void) {
  status_t sts = next_bl0_slot_test();
  if (status_err(sts)) {
    LOG_ERROR("next_bl0_slot_test: %r", sts);
  }
  return status_ok(sts);
}
