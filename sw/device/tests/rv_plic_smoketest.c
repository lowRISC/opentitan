// Copyright lowRISC contributors (OpenTitan project).
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

static_assert(kDtRvPlicCount == 1, "This test expects exactly one rv_plic");

static const dt_rv_plic_t kTestRvPlic = (dt_rv_plic_t)0;
static const dt_uart_t kTestUart = (dt_uart_t)0;

enum {
  kPlicTarget = 0,
};

static dif_rv_plic_t plic0;
static dif_uart_t uart0;

// These flags are used in the test routine to verify that a corresponding
// interrupt has elapsed, and has been serviced. These are declared as volatile
// since they are referenced in the ISR routine as well as in the main program
// flow.
static volatile bool uart_rx_overflow_handled;
static volatile bool uart_tx_done_handled;

/**
 * UART ISR.
 *
 * Services UART interrupts, sets the appropriate flags that are used to
 * determine success or failure of the test.
 */
static void handle_uart_isr(const dif_rv_plic_irq_id_t plic_irq_id) {
  dt_uart_irq_t uart_irq = dt_uart_irq_from_plic_id(kTestUart, plic_irq_id);

  switch (uart_irq) {
    case kDtUartIrqRxOverflow:
      CHECK(!uart_rx_overflow_handled,
            "UART RX overflow IRQ asserted more than once");

      uart_rx_overflow_handled = true;
      break;
    case kDtUartIrqTxDone:
      CHECK(!uart_tx_done_handled, "UART TX done IRQ asserted more than once");

      uart_tx_done_handled = true;
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
void ottf_external_isr(uint32_t *exc_info) {
  // Claim the IRQ by reading the Ibex specific CC register.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic0, kPlicTarget, &plic_irq_id));

  // Check if the interrupted peripheral is UART.
  dt_instance_id_t inst_id = dt_plic_id_to_instance_id(plic_irq_id);
  CHECK(inst_id == dt_uart_instance_id(kTestUart),
        "Interrupt from incorrect peripheral: (exp: %d, obs: %s)",
        dt_uart_instance_id(kTestUart), inst_id);
  handle_uart_isr(plic_irq_id);

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic0, kPlicTarget, plic_irq_id));
}

static void uart_initialise(dt_uart_t uart_id, dif_uart_t *uart) {
  CHECK_DIF_OK(dif_uart_init_from_dt(uart_id, uart));
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
      dif_uart_irq_set_enabled(&uart0, kDifUartIrqTxDone, kDifToggleEnabled));
}

/**
 * Configures all the relevant interrupts in PLIC.
 */
static void plic_configure_irqs(dif_rv_plic_t *plic) {
  dt_plic_irq_id_t rx_ovf_irq =
      dt_uart_irq_to_plic_id(kTestUart, kDtUartIrqRxOverflow);
  dt_plic_irq_id_t tx_done_irq =
      dt_uart_irq_to_plic_id(kTestUart, kDtUartIrqTxDone);

  // Set IRQ priorities to MAX
  CHECK_DIF_OK(
      dif_rv_plic_irq_set_priority(plic, rx_ovf_irq, kDifRvPlicMaxPriority));

  CHECK_DIF_OK(
      dif_rv_plic_irq_set_priority(plic, tx_done_irq, kDifRvPlicMaxPriority));

  // Set Ibex IRQ priority threshold level
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&plic0, kPlicTarget,
                                                kDifRvPlicMinPriority));

  // Enable IRQs in PLIC
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic, rx_ovf_irq, kPlicTarget,
                                           kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic, tx_done_irq, kPlicTarget,
                                           kDifToggleEnabled));
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

  // Force UART TX done interrupt.
  uart_tx_done_handled = false;
  CHECK_DIF_OK(dif_uart_irq_force(uart, kDifUartIrqTxDone, true));
  // Check if the IRQ has occured and has been handled appropriately.
  if (!uart_tx_done_handled) {
    busy_spin_micros(10);
  }
  CHECK(uart_tx_done_handled, "TX done IRQ has not been handled!");
}

OTTF_DEFINE_TEST_CONFIG(.console.test_may_clobber = true);

bool test_main(void) {
  // Enable IRQs on Ibex
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // No debug output in case of UART initialisation failure.
  uart_initialise(kTestUart, &uart0);

  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kTestRvPlic, &plic0));

  uart_configure_irqs(&uart0);
  plic_configure_irqs(&plic0);
  execute_test(&uart0);

  return true;
}
