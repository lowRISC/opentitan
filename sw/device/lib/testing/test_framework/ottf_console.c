// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_console.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

// TODO: make this toplevel agnostic.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * OTTF console configuration parameters.
 */
enum {
  /**
   * SPI device console configuration parameters.
   */
  kSpiDeviceRxCommitWait = 63,  // clock cycles
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

// Potential DIF handles for OTTF console communication.
static dif_spi_device_handle_t ottf_console_spi_device;
static dif_uart_t ottf_console_uart;

// The `flow_control_state` and `flow_control_irqs` variables are shared between
// the interrupt service handler and user code.
static volatile ottf_console_flow_control_t flow_control_state;
static volatile uint32_t flow_control_irqs;

void *ottf_console_get() {
  switch (kOttfTestConfig.console.type) {
    case kOttfConsoleSpiDevice:
      return &ottf_console_spi_device;
    default:
      return &ottf_console_uart;
  }
}

void ottf_console_init(void) {
  // Initialize/Configure the console device.
  uintptr_t base_addr = kOttfTestConfig.console.base_addr;
  switch (kOttfTestConfig.console.type) {
    case kOttfConsoleUart:
      // Set a default for the console base address if the base address is not
      // configured. The default is to use UART0.
      if (base_addr == 0) {
        CHECK(kOttfTestConfig.console.type == kOttfConsoleUart);
        base_addr = TOP_EARLGREY_UART0_BASE_ADDR;
      }
      CHECK_DIF_OK(
          dif_uart_init(mmio_region_from_addr(base_addr), &ottf_console_uart));
      CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
      CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
            "kClockFreqPeripheralHz must fit in uint32_t");
      CHECK_DIF_OK(dif_uart_configure(
          &ottf_console_uart,
          (dif_uart_config_t){
              .baudrate = (uint32_t)kUartBaudrate,
              .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
              .parity_enable = kDifToggleDisabled,
              .parity = kDifUartParityEven,
              .tx_enable = kDifToggleEnabled,
              .rx_enable = kDifToggleEnabled,
          }));
      base_uart_stdout(&ottf_console_uart);

      // Initialize/Configure console flow control (if requested).
      if (kOttfTestConfig.enable_uart_flow_control) {
        ottf_console_flow_control_enable();
      }
      break;
    case (kOttfConsoleSpiDevice):
      CHECK_DIF_OK(dif_spi_device_init_handle(
          mmio_region_from_addr(kOttfTestConfig.console.base_addr),
          &ottf_console_spi_device));
      CHECK_DIF_OK(dif_spi_device_configure(
          &ottf_console_spi_device,
          (dif_spi_device_config_t){
              .clock_polarity = kDifSpiDeviceEdgePositive,
              .data_phase = kDifSpiDeviceEdgeNegative,
              .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
              .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
              .device_mode = kDifSpiDeviceModeGeneric,
              .mode_cfg =
                  {
                      .generic =
                          {
                              .rx_fifo_commit_wait = kSpiDeviceRxCommitWait,
                              .rx_fifo_len = kDifSpiDeviceBufferLen / 2,
                              .tx_fifo_len = kDifSpiDeviceBufferLen / 2,
                          },
                  },
          }));
      base_spi_device_stdout(&ottf_console_spi_device);
      break;
    default:
      CHECK(false, "unsupported OTTF console interface.");
      break;
  }
}

static uint32_t get_flow_control_watermark_plic_id() {
  switch (kOttfTestConfig.console.base_addr) {
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

void ottf_console_flow_control_enable(void) {
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &ottf_plic));

  dif_uart_t *uart = (dif_uart_t *)ottf_console_get();
  CHECK_DIF_OK(dif_uart_watermark_rx_set(uart, kFlowControlRxWatermark));
  CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                        kDifToggleEnabled));

  // Set IRQ priorities to MAX
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      &ottf_plic, get_flow_control_watermark_plic_id(), kDifRvPlicMaxPriority));
  // Set Ibex IRQ priority threshold level
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&ottf_plic, kPlicTarget,
                                                kDifRvPlicMinPriority));
  // Enable IRQs in PLIC
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&ottf_plic,
                                           get_flow_control_watermark_plic_id(),
                                           kPlicTarget, kDifToggleEnabled));

  flow_control_state = kOttfConsoleFlowControlAuto;
  irq_global_ctrl(true);
  irq_external_ctrl(true);
  // Make sure we're in the Resume state and we emit a Resume to the UART.
  ottf_console_flow_control((dif_uart_t *)ottf_console_get(),
                            kOttfConsoleFlowControlResume);
}

// This version of the function is safe to call from within the ISR.
static status_t manage_flow_control(const dif_uart_t *uart,
                                    ottf_console_flow_control_t ctrl) {
  if (flow_control_state == kOttfConsoleFlowControlNone) {
    return OK_STATUS((int32_t)flow_control_state);
  }
  if (ctrl == kOttfConsoleFlowControlAuto) {
    uint32_t avail;
    TRY(dif_uart_rx_bytes_available(uart, &avail));
    if (avail < kFlowControlLowWatermark &&
        flow_control_state != kOttfConsoleFlowControlResume) {
      ctrl = kOttfConsoleFlowControlResume;
    } else if (avail >= kFlowControlHighWatermark &&
               flow_control_state != kOttfConsoleFlowControlPause) {
      ctrl = kOttfConsoleFlowControlPause;
    } else {
      return OK_STATUS((int32_t)flow_control_state);
    }
  }
  uint8_t byte = (uint8_t)ctrl;
  CHECK_DIF_OK(dif_uart_bytes_send(uart, &byte, 1, NULL));
  flow_control_state = ctrl;
  return OK_STATUS((int32_t)flow_control_state);
}

bool ottf_console_flow_control_isr(void) {
  dif_uart_t *uart = (dif_uart_t *)ottf_console_get();
  flow_control_irqs += 1;
  bool rx;
  CHECK_DIF_OK(dif_uart_irq_is_pending(uart, kDifUartIrqRxWatermark, &rx));
  if (rx) {
    manage_flow_control(uart, kOttfConsoleFlowControlAuto);
    CHECK_DIF_OK(dif_uart_irq_acknowledge(uart, kDifUartIrqRxWatermark));
    return true;
  }
  return false;
}

// The public API has to save and restore interrupts to avoid an
// unexpected write to the global `flow_control_state`.
status_t ottf_console_flow_control(const dif_uart_t *uart,
                                   ottf_console_flow_control_t ctrl) {
  dif_uart_irq_enable_snapshot_t snapshot;
  CHECK_DIF_OK(dif_uart_irq_disable_all(uart, &snapshot));
  status_t s = manage_flow_control(uart, ctrl);
  CHECK_DIF_OK(dif_uart_irq_restore_all(uart, &snapshot));
  return s;
}

uint32_t ottf_console_get_flow_control_irqs(void) { return flow_control_irqs; }
