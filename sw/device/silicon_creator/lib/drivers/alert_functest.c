// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/alert.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/test_main.h"

#include "alert_handler_regs.h"
#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "rstmgr_regs.h"

// The reset reason value is really a bitfield. The power-on-reset indicator
// is defined by rstmgr_regs.h.
#define RESET_REASON_POR (1 << RSTMGR_RESET_INFO_POR_BIT)
// FIXME: I don't know where the HW_REQ field of the reset reason register
// is defined.  I observe a value of 4 for alerts.
#define RESET_REASON_ALERT \
  ((4 << RSTMGR_RESET_INFO_HW_REQ_OFFSET) | RESET_REASON_POR)

enum {
  kAlertBase = TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR,
  kOtpBase = TOP_EARLGREY_OTP_CTRL_BASE_ADDR,
  kFlashBase = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR,
};

rom_error_t alert_no_escalate_test(void) {
  // Configure class B alerts for phase 0 only and disable NMI signalling.
  alert_class_config_t config = {
      .enabled = kAlertEnableEnabled,
      .escalation = kAlertEscalatePhase0,
      .accum_threshold = 0,
      .timeout_cycles = 0,
      .phase_cycles = {1, 10, 100, 1000},
  };
  LOG_INFO("Configure OtpCtrlFatalMacroError as class B");
  RETURN_IF_ERROR(alert_configure(kTopEarlgreyAlertIdOtpCtrlFatalMacroError,
                                  kAlertClassB, kAlertEnableLocked));
  LOG_INFO("Configure class B alerts");
  RETURN_IF_ERROR(alert_class_configure(kAlertClassB, &config));
  LOG_INFO("Generate alert via test regs");
  abs_mmio_write32(kOtpBase + OTP_CTRL_ALERT_TEST_REG_OFFSET, 1);
  uint32_t count =
      abs_mmio_read32(kAlertBase + ALERT_HANDLER_CLASSB_ACCUM_CNT_REG_OFFSET);
  return count == 1 ? kErrorOk : kErrorUnknown;
}

rom_error_t alert_escalate_test(void) {
  // Configure class A alerts for full escalation.
  alert_class_config_t config = {
      .enabled = kAlertEnableEnabled,
      .escalation = kAlertEscalatePhase3,
      .accum_threshold = 0,
      .timeout_cycles = 0,
      .phase_cycles = {1, 10, 100, 1000},
  };

  LOG_INFO("Configure FlashCtrlFatalIntgErr as class A");
  RETURN_IF_ERROR(alert_configure(kTopEarlgreyAlertIdFlashCtrlFatalIntgErr,
                                  kAlertClassA, kAlertEnableEnabled));
  LOG_INFO("Configure class A alerts");
  RETURN_IF_ERROR(alert_class_configure(kAlertClassA, &config));
  LOG_INFO("Generate alert via test regs");
  abs_mmio_write32(kFlashBase + FLASH_CTRL_ALERT_TEST_REG_OFFSET, 8);
  return kErrorUnknown;
}

const test_config_t kTestConfig;

bool test_main(void) {
  rom_error_t result = kErrorOk;
  uint32_t reason = rstmgr_reason_get();
  rstmgr_alert_info_enable();

  LOG_INFO("reset_info = %08x", reason);
  if (reason == RESET_REASON_POR) {
    EXECUTE_TEST(result, alert_no_escalate_test);
    EXECUTE_TEST(result, alert_escalate_test);
    // We should never get here - the escalate test should cause a reset
    // and we should see a reset reason of 0x21.
    LOG_ERROR("Test failure: should have reset before this line.");
    result = kErrorUnknown;
  } else if (reason == RESET_REASON_ALERT) {
    LOG_INFO("Detected reset after escalation test");
  } else {
    LOG_ERROR("Unknown reset reason");
    result = kErrorUnknown;
  }
  return result == kErrorOk;
}
