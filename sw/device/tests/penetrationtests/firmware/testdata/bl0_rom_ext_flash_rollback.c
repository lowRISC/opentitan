// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_min_bl0_sec_ver.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_next_boot_bl0_slot.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  // Byte offset of Slot B (owner_slot_b) relative to
  // TOP_EARLGREY_EFLASH_BASE_ADDR.
  kSlotBFlashOffset = 0x90000,
  // Byte offset of a 2-KB scratch page in Bank 1 relative to
  // TOP_EARLGREY_EFLASH_BASE_ADDR.
  kScratchFlashOffset = 0xF0000,
  // Number of 32-bit words in one 2048-byte flash page.
  kFlashPageWords = 512,
};

bool test_main(void) {
  retention_sram_t *retram = retention_sram_get();
  uint32_t bl0_slot = retram->creator.boot_log.bl0_slot;
  uint32_t min_sec_ver_bl0 = retram->creator.boot_log.bl0_min_sec_ver;
  uint32_t primary_slot = retram->creator.boot_log.primary_bl0_slot;

  // Check if we booted from Slot B (security_version = 0).
  if (bl0_slot == kBootSlotB) {
    LOG_INFO("BL0 Slot B (sec_ver=0) booted! min_sec_ver_bl0=%d",
             min_sec_ver_bl0);
    while (1) {
    }
  }

  LOG_INFO("BL0 Slot A (sec_ver=2) booted: min_sec_ver_bl0=%d primary_slot=%x",
           min_sec_ver_bl0, primary_slot);

  flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4True,
      .erase = kMultiBitBool4True,
  });

  uint32_t page_buf[kFlashPageWords];

  // Step 1: Upgrade min_security_version_bl0 in BootData0/BootData1 to 2.
  // Because boot_svc_min_sec_ver_handler() checks MIN(slot_a_sec_ver,
  // slot_b_sec_ver), we save page 0 of Slot B (sec_ver=0) to a scratch page and
  // erase page 0 of Slot B before requesting min_bl0_sec_ver = 2.
  if (min_sec_ver_bl0 < 2) {
    LOG_INFO(
        "Backing up Slot B page 0 and upgrading min_security_version_bl0 to "
        "2...");
    CHECK(flash_ctrl_data_read(kSlotBFlashOffset, kFlashPageWords, page_buf) ==
          kErrorOk);
    if (page_buf[0] != UINT32_MAX) {
      CHECK(flash_ctrl_data_erase(kScratchFlashOffset,
                                  kFlashCtrlEraseTypePage) == kErrorOk);
      CHECK(flash_ctrl_data_write(kScratchFlashOffset, kFlashPageWords,
                                  page_buf) == kErrorOk);
      CHECK(flash_ctrl_data_erase(kSlotBFlashOffset, kFlashCtrlEraseTypePage) ==
            kErrorOk);
    }

    boot_svc_min_bl0_sec_ver_req_init(
        /*min_bl0_sec_ver=*/2,
        &retram->creator.boot_svc_msg.min_bl0_sec_ver_req);
    rstmgr_reset();
    while (1) {
    }
  }

  // Step 2: Once min_security_version_bl0 == 2, restore Slot B (sec_ver=0) from
  // the scratch page and set primary_bl0_slot to kBootSlotB via Boot Services.
  CHECK(flash_ctrl_data_read(kSlotBFlashOffset, kFlashPageWords, page_buf) ==
        kErrorOk);
  if (primary_slot != kBootSlotB || page_buf[0] == UINT32_MAX) {
    LOG_INFO(
        "Restoring Slot B page 0 and setting primary_bl0_slot to "
        "kBootSlotB...");
    CHECK(flash_ctrl_data_read(kScratchFlashOffset, kFlashPageWords,
                               page_buf) == kErrorOk);
    CHECK(flash_ctrl_data_erase(kSlotBFlashOffset, kFlashCtrlEraseTypePage) ==
          kErrorOk);
    CHECK(flash_ctrl_data_write(kSlotBFlashOffset, kFlashPageWords, page_buf) ==
          kErrorOk);

    boot_svc_next_boot_bl0_slot_req_init(
        /*primary_slot=*/kBootSlotB,
        /*next_slot=*/kBootSlotB,
        &retram->creator.boot_svc_msg.next_boot_bl0_slot_req);
    rstmgr_reset();
    while (1) {
    }
  }

  // Re-stage NextBootBl0Slot(kBootSlotB, kBootSlotB) in Retention SRAM so that
  // on the next reset under fault injection, ROM_EXT will execute
  // boot_svc_next_boot_bl0_slot_handler().
  boot_svc_next_boot_bl0_slot_req_init(
      /*primary_slot=*/kBootSlotB,
      /*next_slot=*/kBootSlotB,
      &retram->creator.boot_svc_msg.next_boot_bl0_slot_req);

  LOG_INFO("boot_data min_sec_ver_bl0 upgraded to 2");
  while (1) {
  }
  return true;
}
