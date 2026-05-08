// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "hw/top/flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

dif_flash_ctrl_state_t flash_state;

status_t isfb_page_properties(dif_flash_ctrl_state_t *f) {
  dif_flash_ctrl_info_region_t region = {
      .bank = 0,
      .partition_id = 0,
      .page = 5,
  };
  bool locked;
  dif_flash_ctrl_region_properties_t p;
  TRY(dif_flash_ctrl_get_info_region_properties(f, region, &p));
  TRY(dif_flash_ctrl_info_region_is_locked(f, region, &locked));
  flash_ctrl_testutils_info_region_print(region, &p, locked);
  return OK_STATUS();
}

status_t isfb_page_erase(dif_flash_ctrl_state_t *f) {
  uint32_t info0_page5 = 5 * FLASH_CTRL_PARAM_BYTES_PER_PAGE;
  TRY(flash_ctrl_testutils_erase_page(f, info0_page5,
                                      /*partition_id=*/0,
                                      kDifFlashCtrlPartitionTypeInfo));

  uint32_t strike_mask[] = {0};
  // The strike_mask starts at 0 bytes into the ISFB info page.
  TRY(flash_ctrl_testutils_write(f, info0_page5 + 0,
                                 /*partition_id=*/0, strike_mask,
                                 kDifFlashCtrlPartitionTypeInfo,
                                 sizeof(strike_mask) / sizeof(uint32_t)));

  uint32_t product_words[] = {
      // ascii: `ABCD`
      0x44434241,
      // ascii: `WXYZ`
      0x5a595857,
  };
  // The product_words start at 1024 bytes into the ISFB info page.
  TRY(flash_ctrl_testutils_write(f, info0_page5 + 1024,
                                 /*partition_id=*/0, product_words,
                                 kDifFlashCtrlPartitionTypeInfo,
                                 sizeof(product_words) / sizeof(uint32_t)));

  return OK_STATUS();
}

status_t isfb_page_test(dif_flash_ctrl_state_t *f) {
  TRY(isfb_page_properties(f));
  const manifest_t *manifest = manifest_def_get();
  const manifest_ext_isfb_erase_t *erase;
  if (manifest_ext_get_isfb_erase(manifest, &erase) == kErrorOk) {
    LOG_INFO("isfb_erase present with value %x", erase->erase_allowed);
    if (erase->erase_allowed == kHardenedBoolTrue) {
      TRY(isfb_page_erase(f));
    }
  }
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  status_t sts = isfb_page_test(&flash_state);
  if (status_err(sts)) {
    LOG_ERROR("isfb_page_test: %r", sts);
  }
  return status_ok(sts);
}
