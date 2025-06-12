// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"

#include "hw/top/flash_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kNumWords = FLASH_CTRL_PARAM_BYTES_PER_PAGE / sizeof(uint32_t),
};

static status_t clear_digest_page(const flash_ctrl_info_page_t *info_page) {
  uint32_t data[kNumWords];

  TRY(flash_ctrl_info_read_zeros_on_read_error(info_page, 0, kNumWords, data));

  // Invalidate the digest
  uint32_t prev = data[kNumWords - 1];
  data[kNumWords - 1] ^= 1;
  LOG_INFO("Modify digest %x -> %x", prev, data[kNumWords - 1]);

  TRY(flash_ctrl_info_erase(info_page, kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_write(info_page, 0, kNumWords, data));

  return OK_STATUS();
}

static status_t modify_digest_test(void) {
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageFactoryCerts);
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageDiceCerts);
  TRY(clear_digest_page(&kFlashCtrlInfoPageFactoryCerts));
  TRY(clear_digest_page(&kFlashCtrlInfoPageDiceCerts));
  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = modify_digest_test();
  if (status_err(sts)) {
    LOG_ERROR("modify_digest_test: %r", sts);
  }
  return status_ok(sts);
}
