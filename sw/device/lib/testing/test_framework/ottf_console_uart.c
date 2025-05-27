// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_console.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_console_internal.h"

// TODO: make this toplevel agnostic.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * OTTF console configuration parameters.
 */
enum {
  /**
   * Flow control parameters.
   */
  kFlowControlLowWatermark = 4,   // bytes
  kFlowControlHighWatermark = 8,  // bytes
  kFlowControlRxWatermark = kDifUartWatermarkByte8,
  /**
   * HART PLIC Target.
   */
  kPlicTarget = kTopEarlgreyPlicTargetIbex0,
};

#define MODULE_ID MAKE_MODULE_ID('o', 't', 'u')

// This variable is shared between
// the interrupt service handler and user code.
static volatile ottf_console_flow_control_t flow_control_state;

void ottf_console_configure_uart(ottf_console_t *console, uintptr_t base_addr) {
  CHECK_DIF_OK(
      dif_uart_init(mmio_region_from_addr(base_addr), &console->data.uart.dif));
  CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");
  CHECK_DIF_OK(dif_uart_configure(
      &console->data.uart.dif, (dif_uart_config_t){
                              .baudrate = (uint32_t)kUartBaudrate,
                              .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                              .parity_enable = kDifToggleDisabled,
                              .parity = kDifUartParityEven,
                              .tx_enable = kDifToggleEnabled,
                              .rx_enable = kDifToggleEnabled,
                          }));

  console->getc = ottf_console_uart_getc;
  console->sink = ottf_console_uart_sink;
}

size_t ottf_console_uart_sink(void *io, const char *buf, size_t len) {
  ottf_console_t *console = io;
  const dif_uart_t *uart = &console->data.uart.dif;
  for (size_t i = 0; i < len; ++i) {
    if (dif_uart_byte_send_polled(uart, (uint8_t)buf[i]) != kDifOk) {
      return i;
    }
  }
  return len;
}

status_t ottf_console_uart_getc(void *io) {
  ottf_console_t *console = io;
  const dif_uart_t *uart = &console->data.uart.dif;
  uint8_t byte;
  TRY(dif_uart_byte_receive_polled(uart, &byte));
  TRY(ottf_console_flow_control(console, kOttfConsoleFlowControlAuto));
  return OK_STATUS(byte);
}

// This version of the function is safe to call from within the ISR.
static status_t manage_flow_control(const ottf_console_t *console,
                                    ottf_console_flow_control_t ctrl) {
  const dif_uart_t *uart = &console->data.uart.dif;
  if (flow_control_state == kOttfConsoleFlowControlNone) {
    return OK_STATUS((int32_t)flow_control_state);
  }
  if (ctrl == kOttfConsoleFlowControlAuto) {
    uint32_t avail;
    TRY(dif_uart_rx_bytes_available(uart, &avail));
    if (avail < kFlowControlLowWatermark &&
        flow_control_state != kOttfConsoleFlowControlResume) {
      // Enable RX watermark interrupt when RX FIFO level is below the
      // watermark.
      CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                            kDifToggleEnabled));
      ctrl = kOttfConsoleFlowControlResume;
    } else if (avail >= kFlowControlHighWatermark &&
               flow_control_state != kOttfConsoleFlowControlPause) {
      ctrl = kOttfConsoleFlowControlPause;
      // RX watermark interrupt is status type, so disable the interrupt whilst
      // RX FIFO is above the watermark to avoid an inifite loop of ISRs.
      CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                            kDifToggleDisabled));
    } else {
      return OK_STATUS((int32_t)flow_control_state);
    }
  }
  uint8_t byte = (uint8_t)ctrl;
  CHECK_DIF_OK(dif_uart_bytes_send(uart, &byte, 1, NULL));
  flow_control_state = ctrl;
  return OK_STATUS((int32_t)flow_control_state);
}

static uint32_t get_flow_control_watermark_plic_id(uint32_t base_addr) {
  switch (base_addr) {
#if !OT_IS_ENGLISH_BREAKFAST
    case TOP_EARLGREY_UART1_BASE_ADDR:
      return kTopEarlgreyPlicIrqIdUart1RxWatermark;
    case TOP_EARLGREY_UART2_BASE_ADDR:
      return kTopEarlgreyPlicIrqIdUart2RxWatermark;
    case TOP_EARLGREY_UART3_BASE_ADDR:
      return kTopEarlgreyPlicIrqIdUart3RxWatermark;
#endif
    case TOP_EARLGREY_UART0_BASE_ADDR:
    default:
      return kTopEarlgreyPlicIrqIdUart0RxWatermark;
  }
}

void ottf_console_uart_flow_control_enable(ottf_console_t *console, dif_rv_plic_t *plic) {
  const dif_uart_t *uart = &console->data.uart.dif;
  CHECK_DIF_OK(dif_uart_watermark_rx_set(uart, kFlowControlRxWatermark));
  CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                        kDifToggleEnabled));

  uint32_t plic_id = get_flow_control_watermark_plic_id((uint32_t)console->data.uart.dif.base_addr.base);
  // Set IRQ priorities to MAX
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, plic_id, kDifRvPlicMaxPriority));
  // Set Ibex IRQ priority threshold level
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(plic, kPlicTarget,
                                                kDifRvPlicMinPriority));
  // Enable IRQs in PLIC
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic,
                                           plic_id,
                                           kPlicTarget, kDifToggleEnabled));

  flow_control_state = kOttfConsoleFlowControlAuto;
}

// The public API has to save and restore interrupts to avoid an
// unexpected write to the global `flow_control_state`.
status_t ottf_console_uart_flow_control(ottf_console_t *console,
                                   ottf_console_flow_control_t ctrl) {
  const dif_uart_t *uart = &console->data.uart.dif;
  dif_uart_irq_enable_snapshot_t snapshot;
  CHECK_DIF_OK(dif_uart_irq_disable_all(uart, &snapshot));
  status_t s = manage_flow_control(console, ctrl);
  CHECK_DIF_OK(dif_uart_irq_restore_all(uart, &snapshot));
  return s;
}

bool ottf_console_uart_flow_control_isr(ottf_console_t *console) {
  const dif_uart_t *uart = &console->data.uart.dif;
  bool rx;
  CHECK_DIF_OK(dif_uart_irq_is_pending(uart, kDifUartIrqRxWatermark, &rx));
  if (rx) {
    manage_flow_control(console, kOttfConsoleFlowControlAuto);
    CHECK_DIF_OK(dif_uart_irq_acknowledge(uart, kDifUartIrqRxWatermark));
    return true;
  }
  return false;
}
