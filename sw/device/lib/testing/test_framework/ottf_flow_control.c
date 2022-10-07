// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_flow_control.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define FLOW_CONTROL_LOW_WATERMARK 4
#define FLOW_CONTROL_HIGH_WATERMARK 16
const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

// The flow_control_state and ottf_flow_control_intr varibles are shared between
// the interrupt service handler and user code.
static volatile flow_control_t flow_control_state;
volatile uint32_t ottf_flow_control_intr;

void ottf_flow_control_enable(void) {
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &ottf_plic));

  dif_uart_t *uart = ottf_console();
  CHECK_DIF_OK(dif_uart_watermark_rx_set(uart, kDifUartWatermarkByte16));
  CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                        kDifToggleEnabled));

  // Set IRQ priorities to MAX
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      &ottf_plic, kTopEarlgreyPlicIrqIdUart0RxWatermark,
      kDifRvPlicMaxPriority));
  // Set Ibex IRQ priority threshold level
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&ottf_plic, kPlicTarget,
                                                kDifRvPlicMinPriority));
  // Enable IRQs in PLIC
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      &ottf_plic, kTopEarlgreyPlicIrqIdUart0RxWatermark, kPlicTarget,
      kDifToggleEnabled));

  flow_control_state = kFlowControlAuto;
  irq_global_ctrl(true);
  irq_external_ctrl(true);
  // Make sure we're in the Resume state and we emit a Resume to the UART.
  ottf_flow_control(ottf_console(), kFlowControlResume);
}

// This version of the function is safe to call from within the ISR.
static status_t manage_flow_control(const dif_uart_t *uart,
                                    flow_control_t ctrl) {
  if (flow_control_state == kFlowControlNone) {
    return OK_STATUS(flow_control_state);
  }
  if (ctrl == kFlowControlAuto) {
    uint32_t avail;
    TRY(dif_uart_rx_bytes_available(uart, &avail));
    if (avail < FLOW_CONTROL_LOW_WATERMARK &&
        flow_control_state != kFlowControlResume) {
      ctrl = kFlowControlResume;
    } else if (avail >= FLOW_CONTROL_HIGH_WATERMARK &&
               flow_control_state != kFlowControlPause) {
      ctrl = kFlowControlPause;
    } else {
      return OK_STATUS(flow_control_state);
    }
  }
  uint8_t byte = (uint8_t)ctrl;
  CHECK_DIF_OK(dif_uart_bytes_send(uart, &byte, 1, NULL));
  flow_control_state = ctrl;
  return OK_STATUS(flow_control_state);
}

bool ottf_flow_control_isr(void) {
  dif_uart_t *uart = ottf_console();
  ottf_flow_control_intr += 1;
  bool rx;
  CHECK_DIF_OK(dif_uart_irq_is_pending(uart, kDifUartIrqRxWatermark, &rx));
  if (rx) {
    manage_flow_control(uart, kFlowControlAuto);
    CHECK_DIF_OK(dif_uart_irq_acknowledge(uart, kDifUartIrqRxWatermark));
    return true;
  }
  return false;
}

// The public API has to save and restore interrupts to avoid an
// unexpected write to the global `flow_control_state`.
status_t ottf_flow_control(const dif_uart_t *uart, flow_control_t ctrl) {
  dif_uart_irq_enable_snapshot_t snapshot;
  CHECK_DIF_OK(dif_uart_irq_disable_all(uart, &snapshot));
  status_t s = manage_flow_control(uart, ctrl);
  CHECK_DIF_OK(dif_uart_irq_restore_all(uart, &snapshot));
  return s;
}
