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

static flow_control_t flow_control_state;
#define FLOW_CONTROL_LOW_WATERMARK 4
#define FLOW_CONTROL_HIGH_WATERMARK 4

const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
dif_rv_plic_t ottf_plic;

void ottf_flow_control_enable(void) {
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &ottf_plic));

  dif_uart_t *uart = ottf_console();
  CHECK_DIF_OK(dif_uart_watermark_rx_set(uart, kDifUartWatermarkByte16));

  // Set IRQ priorities to MAX
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      &ottf_plic, kTopEarlgreyPlicIrqIdUart0RxOverflow, kDifRvPlicMaxPriority));
  // Set Ibex IRQ priority threshold level
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&ottf_plic, kPlicTarget,
                                                kDifRvPlicMinPriority));
  // Enable IRQs in PLIC
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&ottf_plic,
                                           kTopEarlgreyPlicIrqIdUart0RxOverflow,
                                           kPlicTarget, kDifToggleEnabled));

  flow_control_state = kFlowControlAuto;
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

bool ottf_flow_control_isr(void) {
  dif_uart_t *uart = ottf_console();
  bool rx;
  CHECK_DIF_OK(dif_uart_irq_is_pending(uart, kDifUartIrqRxWatermark, &rx));
  if (rx) {
    ottf_flow_control(uart, kFlowControlPause);
    CHECK_DIF_OK(dif_uart_irq_acknowledge(uart, kDifUartIrqRxWatermark));
    return true;
  }
  return false;
}

void ottf_external_isr(void) {
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&ottf_plic, kPlicTarget, &plic_irq_id));

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  if (peripheral == kTopEarlgreyPlicPeripheralUart0 &&
      ottf_flow_control_isr()) {
    // Complete the IRQ at PLIC.
    CHECK_DIF_OK(
        dif_rv_plic_irq_complete(&ottf_plic, kPlicTarget, plic_irq_id));
    return;
  }

  ottf_generic_fault_print("External IRQ", ibex_mcause_read());
  abort();
}

status_t ottf_flow_control(const dif_uart_t *uart, flow_control_t ctrl) {
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
