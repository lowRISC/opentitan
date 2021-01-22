// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_plic.h"

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"
#include "sw/device/lib/testing/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

static dif_plic_t plic0;
static dif_uart_t uart0;

// These flags are used in the test routine to verify that a corresponding
// interrupt has elapsed, and has been serviced. These are declared as volatile
// since they are referenced in the ISR routine as well as in the main program
// flow.
static volatile bool uart_rx_overflow_handled;
static volatile bool uart_tx_empty_handled;

/**
 * UART interrupt handler
 *
 * Services UART interrupts, sets the appropriate flags that are used to
 * determine success or failure of the test.
 */
static void handle_uart_isr(const dif_plic_irq_id_t interrupt_id) {
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

  CHECK(dif_uart_irq_acknowledge(&uart0, uart_irq) == kDifUartOk,
        "ISR failed to clear IRQ!");
}

/**
 * External interrupt handler
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this handler. This handler
 * overrides the default implementation, and prototype for this handler must
 * include appropriate attributes.
 */
void handler_irq_external(void) {
  // Claim the IRQ by reading the Ibex specific CC register.
  dif_plic_irq_id_t interrupt_id;
  CHECK(dif_plic_irq_claim(&plic0, kPlicTarget, &interrupt_id) == kDifPlicOk,
        "ISR is not implemented!");

  // Check if the interrupted peripheral is UART.
  top_earlgrey_plic_peripheral_t peripheral_id =
      top_earlgrey_plic_interrupt_for_peripheral[interrupt_id];
  CHECK(peripheral_id == kTopEarlgreyPlicPeripheralUart0,
        "ISR interrupted peripheral is not UART!");
  handle_uart_isr(interrupt_id);

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  CHECK(dif_plic_irq_complete(&plic0, kPlicTarget, &interrupt_id) == kDifPlicOk,
        "Unable to complete the IRQ request!");
}

static void uart_initialise(mmio_region_t base_addr, dif_uart_t *uart) {
  CHECK(dif_uart_init(
            (dif_uart_params_t){
                .base_addr = base_addr,
            },
            uart) == kDifUartOk);
  CHECK(dif_uart_configure(uart,
                           (dif_uart_config_t){
                               .baudrate = kUartBaudrate,
                               .clk_freq_hz = kClockFreqPeripheralHz,
                               .parity_enable = kDifUartToggleDisabled,
                               .parity = kDifUartParityEven,
                           }) == kDifUartConfigOk,
        "UART config failed!");
}

static void plic_initialise(mmio_region_t base_addr, dif_plic_t *plic) {
  CHECK(dif_plic_init((dif_plic_params_t){.base_addr = base_addr}, plic) ==
            kDifPlicOk,
        "PLIC init failed!");
}

/**
 * Configures all the relevant interrupts in UART.
 */
static void uart_configure_irqs(dif_uart_t *uart) {
  CHECK(dif_uart_irq_set_enabled(&uart0, kDifUartIrqRxOverflow,
                                 kDifUartToggleEnabled) == kDifUartOk,
        "RX overflow IRQ enable failed!");
  CHECK(dif_uart_irq_set_enabled(&uart0, kDifUartIrqTxEmpty,
                                 kDifUartToggleEnabled) == kDifUartOk,
        "TX empty IRQ enable failed!");
}

/**
 * Configures all the relevant interrupts in PLIC.
 */
static void plic_configure_irqs(dif_plic_t *plic) {
  // Set IRQ triggers to be level triggered
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdUart0RxOverflow,
                                 kDifPlicIrqTriggerLevel) == kDifPlicOk,
        "RX overflow trigger type set failed!");
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdUart0TxEmpty,
                                 kDifPlicIrqTriggerLevel) == kDifPlicOk,
        "TX empty trigger type set failed!");

  // Set IRQ priorities to MAX
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdUart0RxOverflow,
                                  kDifPlicMaxPriority) == kDifPlicOk,
        "priority set for RX overflow failed!");

  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdUart0TxEmpty,
                                  kDifPlicMaxPriority) == kDifPlicOk,
        "priority set for TX empty failed!");

  // Set Ibex IRQ priority threshold level
  CHECK(dif_plic_target_set_threshold(&plic0, kPlicTarget,
                                      kDifPlicMinPriority) == kDifPlicOk,
        "threshold set failed!");

  // Enable IRQs in PLIC
  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdUart0RxOverflow,
                                 kPlicTarget,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "interrupt Enable for RX overflow failed!");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdUart0TxEmpty,
                                 kPlicTarget,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "interrupt Enable for TX empty failed!");
}

static void execute_test(dif_uart_t *uart) {
  // Force UART RX overflow interrupt.
  uart_rx_overflow_handled = false;
  CHECK(dif_uart_irq_force(uart, kDifUartIrqRxOverflow) == kDifUartOk,
        "failed to force RX overflow IRQ!");
  // Check if the IRQ has occured and has been handled appropriately.
  if (!uart_rx_overflow_handled) {
    usleep(10);
  }
  CHECK(uart_rx_overflow_handled, "RX overflow IRQ has not been handled!");

  // Force UART TX empty interrupt.
  uart_tx_empty_handled = false;
  CHECK(dif_uart_irq_force(uart, kDifUartIrqTxEmpty) == kDifUartOk,
        "failed to force TX empty IRQ!");
  // Check if the IRQ has occured and has been handled appropriately.
  if (!uart_tx_empty_handled) {
    usleep(10);
  }
  CHECK(uart_tx_empty_handled, "TX empty IRQ has not been handled!");
}

const test_config_t kTestConfig = {
    .can_clobber_uart = true,
};

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
  plic_initialise(plic_base_addr, &plic0);

  uart_configure_irqs(&uart0);
  plic_configure_irqs(&plic0);
  execute_test(&uart0);

  return true;
}
