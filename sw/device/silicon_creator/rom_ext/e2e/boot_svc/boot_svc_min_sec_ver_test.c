// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_min_bl0_sec_ver.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/rom_ext/e2e/boot_svc/boot_svc_test_lib.h"

OTTF_DEFINE_TEST_CONFIG();

#define MANIFEST_SEC_VER 4

static status_t initialize(retention_sram_t *retram, boot_svc_retram_t *state) {
  boot_svc_msg_t msg = {0};
  boot_svc_empty_init(&msg.empty);
  boot_svc_min_bl0_sec_ver_req_init(2, &msg.min_bl0_sec_ver_req);
  retram->creator.boot_svc_msg = msg;
  state->state = kBootSvcTestStateMinSecAdvance;
  rstmgr_reset();
  return INTERNAL();
}

static status_t advance(retention_sram_t *retram, boot_svc_retram_t *state) {
  boot_svc_msg_t msg = retram->creator.boot_svc_msg;
  TRY(boot_svc_header_check(&msg.header));
  TRY_CHECK(msg.header.type == kBootSvcMinBl0SecVerResType);
  LOG_INFO("Response: status=%08x min_bl0_sec_ver=%d",
           msg.min_bl0_sec_ver_res.status,
           msg.min_bl0_sec_ver_res.min_bl0_sec_ver);

  TRY_CHECK(msg.min_bl0_sec_ver_res.status == kErrorOk);

  if (msg.min_bl0_sec_ver_res.min_bl0_sec_ver < MANIFEST_SEC_VER) {
    // Advance by one and check again for success
    boot_svc_min_bl0_sec_ver_req_init(
        msg.min_bl0_sec_ver_res.min_bl0_sec_ver + 1, &msg.min_bl0_sec_ver_req);
    retram->creator.boot_svc_msg = msg;
    rstmgr_reset();
  }

  if (msg.min_bl0_sec_ver_res.min_bl0_sec_ver == MANIFEST_SEC_VER) {
    // Advance by one and check for failure
    state->state = kBootSvcTestStateMinSecTooFar;
    boot_svc_min_bl0_sec_ver_req_init(
        msg.min_bl0_sec_ver_res.min_bl0_sec_ver + 1, &msg.min_bl0_sec_ver_req);
    retram->creator.boot_svc_msg = msg;
    rstmgr_reset();
  }
  return INTERNAL();
}

static status_t too_far(retention_sram_t *retram, boot_svc_retram_t *state) {
  boot_svc_msg_t msg = retram->creator.boot_svc_msg;
  TRY(boot_svc_header_check(&msg.header));
  TRY_CHECK(msg.header.type == kBootSvcMinBl0SecVerResType);
  LOG_INFO("Response: status=%08x min_bl0_sec_ver=%d",
           msg.min_bl0_sec_ver_res.status,
           msg.min_bl0_sec_ver_res.min_bl0_sec_ver);
  TRY_CHECK(msg.min_bl0_sec_ver_res.status == kErrorBootSvcBadSecVer);
  TRY_CHECK(msg.min_bl0_sec_ver_res.min_bl0_sec_ver == MANIFEST_SEC_VER);

  // Try to go back
  state->state = kBootSvcTestStateMinSecGoBack;
  boot_svc_min_bl0_sec_ver_req_init(msg.min_bl0_sec_ver_res.min_bl0_sec_ver - 1,
                                    &msg.min_bl0_sec_ver_req);
  retram->creator.boot_svc_msg = msg;
  rstmgr_reset();
  return INTERNAL();
}

static status_t go_back(retention_sram_t *retram, boot_svc_retram_t *state) {
  boot_svc_msg_t msg = retram->creator.boot_svc_msg;
  TRY(boot_svc_header_check(&msg.header));
  TRY_CHECK(msg.header.type == kBootSvcMinBl0SecVerResType);
  LOG_INFO("Response: status=%08x min_bl0_sec_ver=%d",
           msg.min_bl0_sec_ver_res.status,
           msg.min_bl0_sec_ver_res.min_bl0_sec_ver);
  TRY_CHECK(msg.min_bl0_sec_ver_res.status == kErrorBootSvcBadSecVer);
  TRY_CHECK(msg.min_bl0_sec_ver_res.min_bl0_sec_ver == MANIFEST_SEC_VER);

  // End of test sequence.
  state->state = kBootSvcTestStateFinal;
  return OK_STATUS();
}

static status_t min_sec_ver_test(void) {
  retention_sram_t *retram = retention_sram_get();
  TRY(boot_svc_test_init(retram, kBootSvcTestBl0MinSecVer));
  boot_svc_retram_t *state = (boot_svc_retram_t *)&retram->owner;

  for (;;) {
    LOG_INFO("Test state = %d", state->state);
    switch (state->state) {
      case kBootSvcTestStateInit:
        TRY(initialize(retram, state));
        break;
      case kBootSvcTestStateMinSecAdvance:
        TRY(advance(retram, state));
        break;
      case kBootSvcTestStateMinSecTooFar:
        TRY(too_far(retram, state));
        break;
      case kBootSvcTestStateMinSecGoBack:
        TRY(go_back(retram, state));
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
  status_t sts = min_sec_ver_test();
  if (status_err(sts)) {
    LOG_ERROR("min_sec_ver_test: %r", sts);
  }
  return status_ok(sts);
}
