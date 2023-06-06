// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "uart_regs.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  /**
   * Base address of uart.
   */
  kBaseUart = TOP_EARLGREY_UART0_BASE_ADDR,
};

static void uart_alert_trigger(void) {
  abs_mmio_write32(
      kBaseUart + UART_ALERT_TEST_REG_OFFSET,
      bitfield_bit32_write(0, UART_ALERT_TEST_FATAL_FAULT_BIT, true));
}

bool test_main(void) {
  LOG_INFO("Starting test...");
  uint32_t reset_reasons = retention_sram_get()->creator.reset_reasons;
  switch (reset_reasons) {
    case 1 << kRstmgrReasonPowerOn:
      LOG_INFO("No alert escalation, going to trigger alert...");
      uart_alert_trigger();
      LOG_INFO("UART alert routine returned!");
      return false;
    case 1 << kRstmgrReasonEscalation:
      LOG_INFO("Escalation detected!");
      return true;
    default:
      LOG_INFO("Unhandled reset reason: %d", reset_reasons);
      return false;
  }
}
