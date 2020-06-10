// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_plic.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/log.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_main.h"
#include "sw/device/lib/testing/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

#define PLIC_TARGET kTopEarlgreyPlicTargetIbex0

#define kDifPlicMinPriority 0u

static dif_plic_t plic0;
static dif_uart_t uart0;

// These flags are used in the test routine to verify that a corresponding
// interrupt has elapsed, and has been serviced. These are declared as volatile
// since they are referenced in the ISR routine as well as in the main program
// flow.
static volatile bool uart_rx_overflow_handled;
static volatile bool uart_tx_empty_handled;
static volatile bool uart_handled_more_than_once;

#define LOG_FATAL_AND_ABORT(...)        \
  do {                                  \
    LOG_FATAL(__VA_ARGS__);             \
    test_status_set(kTestStatusFailed); \
    abort();                            \
  } while (false)

/**
 * UART interrupt handler
 *
 * Services UART interrupts, sets the appropriate flags that are used to
 * determine success or failure of the test.
 */
static void handle_uart_isr(const dif_plic_irq_id_t interrupt_id) {
  const dif_uart_t *uart = &uart0;

  dif_uart_interrupt_t uart_irq;
  switch (interrupt_id) {
    case kTopEarlgreyPlicIrqIdUartRxOverflow:
      uart_irq = kDifUartInterruptRxOverflow;

      // It is an error if this IRQ is asserted more than once.
      if (uart_rx_overflow_handled) {
        uart_handled_more_than_once = true;
      } else {
        uart_rx_overflow_handled = true;
      }
      break;
    case kTopEarlgreyPlicIrqIdUartTxEmpty:
      uart_irq = kDifUartInterruptTxEmpty;

      // It is an error if this IRQ is asserted more than once.
      if (uart_tx_empty_handled) {
        uart_handled_more_than_once = true;
      } else {
        uart_tx_empty_handled = true;
      }
      break;
    default:
      LOG_FATAL_AND_ABORT("ISR is not implemented!");
  }

  if (dif_uart_irq_state_clear(uart, uart_irq) != kDifUartOk) {
    LOG_FATAL_AND_ABORT("ISR failed to clear IRQ!");
  }
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
  if (dif_plic_irq_claim(&plic0, PLIC_TARGET, &interrupt_id) != kDifPlicOk) {
    LOG_FATAL_AND_ABORT("ISR is not implemented!");
  }

  // Check if the interrupted peripheral is UART.
  top_earlgrey_plic_peripheral_t peripheral_id =
      top_earlgrey_plic_interrupt_for_peripheral[interrupt_id];
  if (peripheral_id != kTopEarlgreyPlicPeripheralUart) {
    LOG_FATAL_AND_ABORT("ISR interrupted peripheral is not UART!");
  }
  handle_uart_isr(interrupt_id);

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  if (dif_plic_irq_complete(&plic0, PLIC_TARGET, &interrupt_id) != kDifPlicOk) {
    LOG_FATAL_AND_ABORT("Unable to complete the IRQ request!");
  }
}

static void uart_initialise(mmio_region_t base_addr, dif_uart_t *uart) {
  dif_uart_config_t config = {
      .baudrate = kUartBaudrate,
      .clk_freq_hz = kClockFreqHz,
      .parity_enable = kDifUartDisable,
      .parity = kDifUartParityEven,
  };

  // No debug output in case of UART initialisation failure.
  if (dif_uart_init(base_addr, &config, uart) != kDifUartConfigOk) {
    LOG_FATAL_AND_ABORT("UART init failed!");
  }
}

static void plic_initialise(mmio_region_t base_addr, dif_plic_t *plic) {
  if (dif_plic_init(base_addr, plic) != kDifPlicOk) {
    LOG_FATAL_AND_ABORT("PLIC init failed!");
  }
}

/**
 * Configures all the relevant interrupts in UART.
 */
static bool uart_configure_irqs(dif_uart_t *uart) {
  if (dif_uart_irq_enable(&uart0, kDifUartInterruptRxOverflow,
                          kDifUartEnable) != kDifUartOk) {
    LOG_ERROR("RX overflow IRQ enable failed!");
    return false;
  }
  if (dif_uart_irq_enable(&uart0, kDifUartInterruptTxEmpty, kDifUartEnable) !=
      kDifUartOk) {
    LOG_ERROR("TX empty IRQ enable failed!");
    return false;
  }

  return true;
}

/**
 * Configures all the relevant interrupts in PLIC.
 */
static bool plic_configure_irqs(dif_plic_t *plic) {
  // Set IRQ triggers to be level triggered
  if (dif_plic_irq_trigger_type_set(plic, kTopEarlgreyPlicIrqIdUartRxOverflow,
                                    kDifPlicDisable) != kDifPlicOk) {
    LOG_ERROR("RX overflow trigger type set failed!");
    return false;
  }
  if (dif_plic_irq_trigger_type_set(plic, kTopEarlgreyPlicIrqIdUartTxEmpty,
                                    kDifPlicDisable) != kDifPlicOk) {
    LOG_ERROR("TX empty trigger type set failed!");
    return false;
  }

  // Set IRQ priorities to MAX
  if (dif_plic_irq_priority_set(plic, kTopEarlgreyPlicIrqIdUartRxOverflow,
                                kDifPlicMaxPriority) != kDifPlicOk) {
    LOG_ERROR("priority set for RX overflow failed!");
    return false;
  }

  if (dif_plic_irq_priority_set(plic, kTopEarlgreyPlicIrqIdUartTxEmpty,
                                kDifPlicMaxPriority) != kDifPlicOk) {
    LOG_ERROR("priority set for TX empty failed!");
    return false;
  }

  // Set Ibex IRQ priority threshold level
  if (dif_plic_target_threshold_set(&plic0, PLIC_TARGET, kDifPlicMinPriority) !=
      kDifPlicOk) {
    LOG_ERROR("threshold set failed!");
    return false;
  }

  // Enable IRQs in PLIC
  if (dif_plic_irq_enable_set(plic, kTopEarlgreyPlicIrqIdUartRxOverflow,
                              PLIC_TARGET, kDifPlicEnable) != kDifPlicOk) {
    LOG_ERROR("interrupt Enable for RX overflow failed!");
    return false;
  }
  if (dif_plic_irq_enable_set(plic, kTopEarlgreyPlicIrqIdUartTxEmpty,
                              PLIC_TARGET, kDifPlicEnable) != kDifPlicOk) {
    LOG_ERROR("interrupt Enable for TX empty failed!");
    return false;
  }

  return true;
}

static bool execute_test(dif_uart_t *uart) {
  // Initialize the global variables.
  uart_rx_overflow_handled = false;
  uart_tx_empty_handled = false;
  uart_handled_more_than_once = false;

  // Force UART RX overflow interrupt.
  if (dif_uart_irq_force(uart, kDifUartInterruptRxOverflow) != kDifUartOk) {
    LOG_ERROR("failed to force RX overflow IRQ!");
    return false;
  }
  // Check if the IRQ has occured and has been handled appropriately.
  if (!uart_rx_overflow_handled) {
    usleep(10);
  }
  if (!uart_rx_overflow_handled) {
    LOG_ERROR("RX overflow IRQ has not been handled!");
    return false;
  }
  // Check that the IRQ has not been asserted more than once.
  if (uart_handled_more_than_once) {
    LOG_ERROR("RX overflow IRQ was asserted more than once!");
    return false;
  }

  // Force UART TX empty interrupt.
  if (dif_uart_irq_force(uart, kDifUartInterruptTxEmpty) != kDifUartOk) {
    LOG_ERROR("failed to force TX empty IRQ!");
    return false;
  }
  // Check if the IRQ has occured and has been handled appropriately.
  if (!uart_tx_empty_handled) {
    usleep(10);
  }
  if (!uart_tx_empty_handled) {
    LOG_ERROR("TX empty IRQ has not been handled!");
    return false;
  }
  // Check that the IRQ has not been asserted more than once.
  if (uart_handled_more_than_once) {
    LOG_ERROR("TX empty IRQ was asserted more than once!");
    return false;
  }

  return true;
}

bool test_main(void) {
  // Enable IRQs on Ibex
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // No debug output in case of UART initialisation failure.
  mmio_region_t uart_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_UART_BASE_ADDR);
  uart_initialise(uart_base_addr, &uart0);

  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  plic_initialise(plic_base_addr, &plic0);

  if (!uart_configure_irqs(&uart0) || !plic_configure_irqs(&plic0)) {
    return false;
  }

  return (execute_test(&uart0));
}
