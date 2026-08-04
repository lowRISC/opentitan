// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/nvm_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

OTTF_DEFINE_TEST_CONFIG();

// The ISFB info page is logical info page 5 (bank 0, info partition 0, page
// 5 in flash terms).
//
// TODO(#30890): on RRAM, there is no hardware-enforced distinction between
// "can write" and "can erase" (no `erase_en`), so any image with plain write
// access to this page can flip a struck bit back to `1` without needing the
// `isfb_erase` manifest extension this test exercises. The one-way
// strike/un-strike ratchet the extension is meant to enforce is not
// currently guaranteed on RRAM.
static const nvm_info_page_t kIsfbPage = kNvmInfoPageOwnerReserved0;

status_t isfb_page_properties(void) {
  TRY(nvm_testutils_info_page_print(kIsfbPage));
  return OK_STATUS();
}

status_t isfb_page_erase(void) {
  uint32_t strike_mask[] = {0};
  // The strike_mask starts at 0 bytes into the ISFB info page.  This write
  // erases the page first.
  TRY(nvm_testutils_write_info_page(kIsfbPage, /*byte_offset=*/0, strike_mask,
                                    ARRAYSIZE(strike_mask),
                                    /*erase_before_write=*/true,
                                    /*readback=*/false));

  uint32_t product_words[] = {
      // ascii: `ABCD`
      0x44434241,
      // ascii: `WXYZ`
      0x5a595857,
  };
  // The product_words start at 1024 bytes into the ISFB info page, matching
  // isfb.c's real read offset (512 bytes of strike region followed by up to
  // 1024 bytes of product expressions). The page was already erased above,
  // so no need to erase it again here.
  TRY(nvm_testutils_write_info_page(kIsfbPage, /*byte_offset=*/1024,
                                    product_words, ARRAYSIZE(product_words),
                                    /*erase_before_write=*/false,
                                    /*readback=*/false));

  return OK_STATUS();
}

status_t isfb_page_test(void) {
  TRY(isfb_page_properties());
  const manifest_t *manifest = manifest_def_get();
  const manifest_ext_isfb_erase_t *erase;
  if (manifest_ext_get_isfb_erase(manifest, &erase) == kErrorOk) {
    LOG_INFO("isfb_erase present with value %x", erase->erase_allowed);
    if (erase->erase_allowed == kHardenedBoolTrue) {
      TRY(isfb_page_erase());
    }
  }
  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = isfb_page_test();
  if (status_err(sts)) {
    LOG_ERROR("isfb_page_test: %r", sts);
  }
  return status_ok(sts);
}
