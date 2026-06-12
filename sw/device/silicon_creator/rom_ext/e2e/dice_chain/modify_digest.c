// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top/dt/flash_ctrl.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kNumWords = NVM_BYTES_PER_PAGE / sizeof(uint32_t),
};

static status_t clear_digest_page(nvm_info_page_t info_page) {
  uint32_t data[kNumWords];

  TRY(nvm_ctrl_info_read_zeros_on_read_error(info_page, 0, kNumWords, data));

  // Invalidate the digest
  uint32_t prev = data[kNumWords - 1];
  data[kNumWords - 1] ^= 1;
  LOG_INFO("Modify digest %x -> %x", prev, data[kNumWords - 1]);

  TRY(nvm_ctrl_info_erase(info_page));
  TRY(nvm_ctrl_info_write(info_page, 0, kNumWords, data));

  return OK_STATUS();
}

static status_t modify_digest_test(void) {
  nvm_ctrl_cert_info_page_creator_cfg(kNvmInfoPageFactoryCerts);
  nvm_ctrl_cert_info_page_creator_cfg(kNvmInfoPageDiceCerts);
  TRY(clear_digest_page(kNvmInfoPageFactoryCerts));
  TRY(clear_digest_page(kNvmInfoPageDiceCerts));
  return OK_STATUS();
}

bool test_main(void) {
  // This test intentionally creates an invalid digest triggering recoverable
  // errors. Ignore the alert in OTTF.
  CHECK_STATUS_OK(
      ottf_alerts_expect_alert_start(dt_flash_ctrl_alert_to_alert_id(
          kDtFlashCtrlFirst, kDtFlashCtrlAlertRecovErr)));

  status_t sts = modify_digest_test();
  if (status_err(sts)) {
    LOG_ERROR("modify_digest_test: %r", sts);
  }
  return status_ok(sts);
}
