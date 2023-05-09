// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

static dif_rv_plic_t plic0;
static dif_uart_t uart0;

// These flags are used in the test routine to verify that a corresponding
// interrupt has elapsed, and has been serviced. These are declared as volatile
// since they are referenced in the ISR routine as well as in the main program
// flow.
static volatile bool uart_rx_overflow_handled;
static volatile bool uart_tx_empty_handled;

/**
 * UART ISR.
 *
 * Services UART interrupts, sets the appropriate flags that are used to
 * determine success or failure of the test.
 */
static void handle_uart_isr(const dif_rv_plic_irq_id_t interrupt_id) {
  // NOTE: This initialization is superfluous, since the `default` case below
  // is effectively noreturn, but the compiler is unable to prove this.
  dif_uart_irq_t uart_irq = 0;

  switch (interrupt_id) {
    case kTopEarlgreyPlicIrqIdUart0RxOverflow:
      CHECK(!uart_rx_overflow_handled,
            "UART RX overflow IRQ asserted more than once");

      uart_irq = kDifUartIrqRxOverflow;
      uart_rx_overflow_handled = true;
      break;
    case kTopEarlgreyPlicIrqIdUart0TxEmpty:
      CHECK(!uart_tx_empty_handled,
            "UART TX empty IRQ asserted more than once");

      uart_irq = kDifUartIrqTxEmpty;
      uart_tx_empty_handled = true;
      break;
    default:
      LOG_FATAL("ISR is not implemented!");
      test_status_set(kTestStatusFailed);
  }

  CHECK_DIF_OK(dif_uart_irq_acknowledge(&uart0, uart_irq));
}

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
void ottf_external_isr(void) {
  // Claim the IRQ by reading the Ibex specific CC register.
  dif_rv_plic_irq_id_t interrupt_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic0, kPlicTarget, &interrupt_id));

  // Check if the interrupted peripheral is UART.
  top_earlgrey_plic_peripheral_t peripheral_id =
      top_earlgrey_plic_interrupt_for_peripheral[interrupt_id];
  CHECK(peripheral_id == kTopEarlgreyPlicPeripheralUart0,
        "ISR interrupted peripheral is not UART!");
  handle_uart_isr(interrupt_id);

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic0, kPlicTarget, interrupt_id));
}

static void uart_initialise(mmio_region_t base_addr, dif_uart_t *uart) {
  CHECK_DIF_OK(dif_uart_init(base_addr, uart));
  CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");
  CHECK_DIF_OK(dif_uart_configure(
      uart, (dif_uart_config_t){
                .baudrate = (uint32_t)kUartBaudrate,
                .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                .parity_enable = kDifToggleDisabled,
                .parity = kDifUartParityEven,
                .tx_enable = kDifToggleEnabled,
                .rx_enable = kDifToggleEnabled,
            }));
}

/**
 * Configures all the relevant interrupts in UART.
 */
static void uart_configure_irqs(dif_uart_t *uart) {
  CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart0, kDifUartIrqRxOverflow,
                                        kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_uart_irq_set_enabled(&uart0, kDifUartIrqTxEmpty, kDifToggleEnabled));
}

/**
 * Configures all the relevant interrupts in PLIC.
 */
static void plic_configure_irqs(dif_rv_plic_t *plic) {
  // Set IRQ priorities to MAX
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, kTopEarlgreyPlicIrqIdUart0RxOverflow, kDifRvPlicMaxPriority));

  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, kTopEarlgreyPlicIrqIdUart0TxEmpty, kDifRvPlicMaxPriority));

  // Set Ibex IRQ priority threshold level
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&plic0, kPlicTarget,
                                                kDifRvPlicMinPriority));

  // Enable IRQs in PLIC
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic,
                                           kTopEarlgreyPlicIrqIdUart0RxOverflow,
                                           kPlicTarget, kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      plic, kTopEarlgreyPlicIrqIdUart0TxEmpty, kPlicTarget, kDifToggleEnabled));
}

static void execute_test(dif_uart_t *uart) {
  // Force UART RX overflow interrupt.
  uart_rx_overflow_handled = false;
  CHECK_DIF_OK(dif_uart_irq_force(uart, kDifUartIrqRxOverflow, true));
  // Check if the IRQ has occured and has been handled appropriately.
  if (!uart_rx_overflow_handled) {
    busy_spin_micros(10);
  }
  CHECK(uart_rx_overflow_handled, "RX overflow IRQ has not been handled!");

  // Force UART TX empty interrupt.
  uart_tx_empty_handled = false;
  CHECK_DIF_OK(dif_uart_irq_force(uart, kDifUartIrqTxEmpty, true));
  // Check if the IRQ has occured and has been handled appropriately.
  if (!uart_tx_empty_handled) {
    busy_spin_micros(10);
  }
  CHECK(uart_tx_empty_handled, "TX empty IRQ has not been handled!");
}

OTTF_DEFINE_TEST_CONFIG(.console.test_may_clobber = true);

bool test_main(void) {
  // Enable IRQs on Ibex
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // No debug output in case of UART initialisation failure.
  mmio_region_t uart_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR);
  uart_initialise(uart_base_addr, &uart0);

  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(plic_base_addr, &plic0));

  uart_configure_irqs(&uart0);
  plic_configure_irqs(&plic0);
  execute_test(&uart0);

  return true;
}
