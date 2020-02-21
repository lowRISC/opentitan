// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/common.h"
#include "sw/device/lib/dif/dif_plic.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/print_log.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"

#define UART0_BASE_ADDR 0x40000000u
#define PLIC0_BASE_ADDR 0x40090000u

#define PLIC_TARGET kDifPlicTargetIbex0

#define PLIC_PRIORITY_MIN 0u
#define PLIC_PRIORITY_MAX 3u

static dif_plic_t plic0;
static dif_uart_t uart0;

// These flags are used in the test routine to verify that a corresponding
// interrupt has elapsed, and has been serviced.
static bool uart_rx_overflow_handled = false;
static bool uart_tx_empty_handled = false;
static bool uart_handled_more_than_once = false;

void uart_print_char(char c) {
  if (!dif_uart_byte_send_polled(&uart0, (uint8_t)c)) {
    abort();
  }
}
print_char_func uart_print_char_p = &uart_print_char;

static void debug_msg_and_abort(const char *msg) {
  print_log(uart_print_char_p, msg);
  print_log(uart_print_char_p, "FAIL!\n");
  abort();
}

/**
 * UART interrupt handler
 *
 * Services UART interrupts, sets the appropriate flags that are used to
 * determine success or failure of the test.
 */
static void handler_uart_isr(const dif_irq_claim_data_t *data) {
  const dif_uart_t *uart = &uart0;

  dif_uart_interrupt_t uart_irq;
  switch (data->source) {
    case kDifPlicIrqIdUartRxOverflow:
      uart_irq = kDifUartInterruptRxOverflow;

      // It is an error if this IRQ is asserted more than once.
      if (uart_rx_overflow_handled) {
        uart_handled_more_than_once = true;
      } else {
        uart_rx_overflow_handled = true;
      }
      break;
    case kDifPlicIrqIdUartTxEmpty:
      uart_irq = kDifUartInterruptTxEmpty;

      // It is an error if this IRQ is asserted more than once.
      if (uart_tx_empty_handled) {
        uart_handled_more_than_once = true;
      } else {
        uart_tx_empty_handled = true;
      }
      break;
    default:
      debug_msg_and_abort("HANDLER UART: ISR is not implemented!\n");
  }

  if (!dif_uart_irq_state_clear(uart, uart_irq)) {
    debug_msg_and_abort("HANDLER UART: ISR failed to clear IRQ!\n");
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
  dif_irq_claim_data_t claim_data;
  if (!dif_plic_irq_claim(&plic0, PLIC_TARGET, &claim_data)) {
    debug_msg_and_abort("HANDLER: ISR is not implemented!\n");
  }

  // Check if the interrupted peripheral is UART.
  if (claim_data.peripheral != kDifPlicPeripheralUart) {
    debug_msg_and_abort("HANDLER: ISR interrupted peripheral is not UART!\n");
  }
  handler_uart_isr(&claim_data);

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  if (!dif_plic_irq_complete(&plic0, &claim_data)) {
    debug_msg_and_abort("HANDLER: unable to complete the IRQ request!\n");
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
  if (!dif_uart_init(base_addr, &config, uart)) {
    abort();
  }
}

static bool plic_initialise(mmio_region_t base_addr, dif_plic_t *plic) {
  if (!dif_plic_init(base_addr, plic)) {
    print_log(uart_print_char_p, "PLIC: init failed!\n");
    return false;
  }

  return true;
}

/**
 * Configures all the relevant interrupts in UART.
 */
static bool uart_configure_irqs(dif_uart_t *uart) {
  if (!dif_uart_irq_enable(&uart0, kDifUartInterruptRxOverflow,
                           kDifUartEnable)) {
    print_log(uart_print_char_p, "UART: RX overflow IRQ enable failed!\n");
    return false;
  }
  if (!dif_uart_irq_enable(&uart0, kDifUartInterruptTxEmpty, kDifUartEnable)) {
    print_log(uart_print_char_p, "UART: TX empty IRQ enable failed!\n");
    return false;
  }

  return true;
}

/**
 * Configures all the relevant interrupts in PLIC.
 */
static bool plic_configure_irqs(dif_plic_t *plic) {
  // Set IRQ triggers to be level triggered
  if (!dif_plic_irq_trigger_type_set(plic, kDifPlicIrqIdUartRxOverflow,
                                     kDifPlicDisable)) {
    print_log(uart_print_char_p,
              "PLIC: RX overflow trigger type set failed!\n");
    return false;
  }
  if (!dif_plic_irq_trigger_type_set(plic, kDifPlicIrqIdUartTxEmpty,
                                     kDifPlicDisable)) {
    print_log(uart_print_char_p, "PLIC: TX empty trigger type set failed!\n");
    return false;
  }

  // Set IRQ priorities to MAX
  if (!dif_plic_irq_priority_set(plic, kDifPlicIrqIdUartRxOverflow,
                                 PLIC_PRIORITY_MAX)) {
    print_log(uart_print_char_p,
              "PLIC: priority set for RX overflow failed!\n");
    return false;
  }
  if (!dif_plic_irq_priority_set(plic, kDifPlicIrqIdUartTxEmpty,
                                 PLIC_PRIORITY_MAX)) {
    print_log(uart_print_char_p, "PLIC: priority set for TX empty failed!\n");
    return false;
  }

  // Set Ibex IRQ priority threshold level
  if (!dif_plic_target_threshold_set(&plic0, PLIC_TARGET, PLIC_PRIORITY_MIN)) {
    print_log(uart_print_char_p, "PLIC: threshold set failed!\n");
    return false;
  }

  // Enable IRQs in PLIC
  if (!dif_plic_irq_enable_set(plic, kDifPlicIrqIdUartRxOverflow, PLIC_TARGET,
                               kDifPlicEnable)) {
    print_log(uart_print_char_p,
              "PLIC: interrupt Enable for RX overflow failed!\n");
    return false;
  }
  if (!dif_plic_irq_enable_set(plic, kDifPlicIrqIdUartTxEmpty, PLIC_TARGET,
                               kDifPlicEnable)) {
    print_log(uart_print_char_p,
              "PLIC: interrupt Enable for TX empty failed!\n");
    return false;
  }

  return true;
}

static bool execute_test(dif_uart_t *uart) {
  // Force UART RX overflow interrupt.
  if (!dif_uart_irq_force(uart, kDifUartInterruptRxOverflow)) {
    print_log(uart_print_char_p, "TEST: failed to force RX overflow IRQ!\n");
    return false;
  }
  // Check if the IRQ has occured and has been handled appropriately.
  if (!uart_rx_overflow_handled) {
    usleep(10);
  }
  if (!uart_rx_overflow_handled) {
    print_log(uart_print_char_p,
              "TEST: RX overflow IRQ has not been handled!\n");
    return false;
  }
  // Check that the IRQ has not been asserted more than once.
  if (uart_handled_more_than_once) {
    print_log(uart_print_char_p,
              "TEST: RX overflow IRQ was asserted more than once!\n");
    return false;
  }

  // Force UART TX empty interrupt.
  if (!dif_uart_irq_force(uart, kDifUartInterruptTxEmpty)) {
    print_log(uart_print_char_p, "TEST: failed to force TX empty IRQ!\n");
    return false;
  }
  // Check if the IRQ has occured and has been handled appropriately.
  if (!uart_tx_empty_handled) {
    usleep(10);
  }
  if (!uart_tx_empty_handled) {
    print_log(uart_print_char_p, "TEST: TX empty IRQ has not been handled!\n");
    return false;
  }
  // Check that the IRQ has not been asserted more than once.
  if (uart_handled_more_than_once) {
    print_log(uart_print_char_p,
              "TEST: TX empty IRQ was asserted more than once!\n");
    return false;
  }

  return true;
}

int main(int argc, char **argv) {
  // Enable IRQs on Ibex
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // No debug output in case of UART initialisation failure.
  mmio_region_t uart_base_addr = mmio_region_from_addr(UART0_BASE_ADDR);
  uart_initialise(uart_base_addr, &uart0);

  mmio_region_t plic_base_addr = mmio_region_from_addr(PLIC0_BASE_ADDR);
  if (!plic_initialise(plic_base_addr, &plic0)) {
    print_log(uart_print_char_p, "FAIL!\n");
    return -1;
  }

  if (!uart_configure_irqs(&uart0) || !plic_configure_irqs(&plic0)) {
    print_log(uart_print_char_p, "FAIL!\n");
    return -1;
  }

  if (!execute_test(&uart0)) {
    print_log(uart_print_char_p, "FAIL!\n");
    return -1;
  }

  print_log(uart_print_char_p, "PASS!\n");

  return 0;
}
