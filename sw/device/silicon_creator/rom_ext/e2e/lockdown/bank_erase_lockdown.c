// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  retention_sram_t *retram = retention_sram_get();

  if (bitfield_bit32_read(retram->creator.reset_reasons,
                          kRstmgrReasonPowerOn)) {
    LOG_INFO("Primary boot: attempting bank erase");

    dif_flash_ctrl_state_t flash_ctrl;
    CHECK_DIF_OK(dif_flash_ctrl_init_state(
        &flash_ctrl,
        mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

    dif_flash_ctrl_transaction_t transaction = {
        .byte_address = 0,  // Bank 0
        .op = kDifFlashCtrlOpBankErase,
        .partition_type = kDifFlashCtrlPartitionTypeData,
    };

    // Ignore Alert 35 (flash_ctrl_recov_err) which is expected in lockdown
    // case.
    CHECK_STATUS_OK(
        ottf_alerts_ignore_alert(kTopEarlgreyAlertIdFlashCtrlRecovErr));

    // Attempt to enable bank erase for Bank 0.
    OT_DISCARD(dif_flash_ctrl_set_bank_erase_enablement(&flash_ctrl, 0,
                                                        kDifToggleEnabled));

    // Attempt to start bank erase.
    CHECK_DIF_OK(dif_flash_ctrl_start(&flash_ctrl, transaction));
    LOG_INFO("dif_flash_ctrl_start succeeded, waiting for operation status.");

    dif_flash_ctrl_output_t out;
    dif_result_t end_result;
    do {
      end_result = dif_flash_ctrl_end(&flash_ctrl, &out);
    } while (end_result == kDifUnavailable);

    if (end_result == kDifOk) {
      LOG_INFO("Operation completed. Error status: %d.", out.operation_error);
      CHECK(out.operation_error, "Expected operation error but it succeeded!");
    } else {
      LOG_INFO("dif_flash_ctrl_end failed: %d", end_result);
      return false;
    }

    LOG_INFO("Rebooting");
    rstmgr_reset();
    return false;
  }

  LOG_INFO("Rebooted successfully.");
  return true;
}
