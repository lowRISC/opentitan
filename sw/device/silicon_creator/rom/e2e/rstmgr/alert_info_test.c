// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top/dt/uart.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top/uart_regs.h"

// Test handles alerts directly, disable OTTF catcher.
OTTF_DEFINE_TEST_CONFIG(.ignore_alerts = true);

static const dt_uart_t kUartDt = kDtUart0;

/**
 * Base address of the uart registers.
 */
static inline uint32_t uart_reg_base(void) {
  return dt_uart_reg_block(kUartDt, kDtUartRegBlockCore);
}

static void uart_alert_trigger(void) {
  abs_mmio_write32(
      uart_reg_base() + UART_ALERT_TEST_REG_OFFSET,
      bitfield_bit32_write(0, UART_ALERT_TEST_FATAL_FAULT_BIT, true));
}

static void check_alert_info_dump(void) {
  rstmgr_info_t info;

  rstmgr_alert_info_collect(&info);
  uint32_t all_values = 0;
  for (int i = 0; i < info.length; i++) {
    LOG_INFO("DUMP[%d]: 0x%x", i, info.info[i]);
    all_values |= info.info[i];
  }

#if defined(TEST_ALERT_INFO_ENABLED)
  CHECK(all_values != 0, "All crashdump values are zero.");
#elif defined(TEST_ALERT_INFO_DISABLED)
  CHECK(all_values == 0, "All crashdump values should be zero.");
#else
#error "no alert info test variant is defined"
#endif
}

bool test_main(void) {
  uint32_t reset_reasons = retention_sram_get()->creator.reset_reasons;
  if (bitfield_bit32_read(reset_reasons, kRstmgrReasonPowerOn)) {
    LOG_INFO("No alert escalation, going to trigger alert...");
    uart_alert_trigger();
    LOG_INFO("UART alert routine returned!");
    return false;
  } else if (rstmgr_is_hw_reset_reason(kDtRstmgrAon, reset_reasons,
                                       kDtInstanceIdAlertHandler, 0)) {
    LOG_INFO("Escalation detected!");
    check_alert_info_dump();
    return true;
  } else {
    LOG_INFO("Unhandled reset reason: %d", reset_reasons);
    return false;
  }
}
