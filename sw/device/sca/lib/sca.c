// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/sca/lib/sca.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/print.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Macro for ignoring return values.
 *
 * This is needed because ‘(void)expr;` does not work for gcc.
 */
#define IGNORE_RESULT(expr) \
  if (expr) {               \
  }

enum {
  /**
   * GPIO capture trigger values.
   */
  kGpioCaptureTriggerHigh = 0x08200,
  kGpioCaptureTriggerLow = 0x00000,
  /**
   * RV timer settings.
   */
  kRvTimerComparator = 0,
  kRvTimerHart = kTopEarlgreyPlicTargetIbex0,
};

static dif_uart_t uart;
static dif_gpio_t gpio;
static dif_rv_timer_t timer;

// TODO(alphan): Handle return values as long as they don't affect capture rate.

/**
 * Initializes the UART peripheral.
 */
static void sca_init_uart(void) {
  IGNORE_RESULT(dif_uart_init(
      (dif_uart_params_t){
          .base_addr = mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR),
      },
      &uart));
  IGNORE_RESULT(
      dif_uart_configure(&uart, (dif_uart_config_t){
                                    .baudrate = kUartBaudrate,
                                    .clk_freq_hz = kClockFreqPeripheralHz,
                                    .parity_enable = kDifUartToggleDisabled,
                                    .parity = kDifUartParityEven,
                                }));
  base_uart_stdout(&uart);
}

/**
 * Initializes the GPIO peripheral.
 */
static void sca_init_gpio(void) {
  dif_gpio_params_t gpio_params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR)};
  IGNORE_RESULT(dif_gpio_init(gpio_params, &gpio));
  IGNORE_RESULT(
      dif_gpio_output_set_enabled_all(&gpio, kGpioCaptureTriggerHigh));
}

/**
 * Initializes the timer peripheral.
 */
static void sca_init_timer(void) {
  IGNORE_RESULT(dif_rv_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR),
      (dif_rv_timer_config_t){.hart_count = 1, .comparator_count = 1}, &timer));
  dif_rv_timer_tick_params_t tick_params;
  IGNORE_RESULT(dif_rv_timer_approximate_tick_params(
      kClockFreqPeripheralHz, kClockFreqCpuHz, &tick_params));
  IGNORE_RESULT(
      dif_rv_timer_set_tick_params(&timer, kRvTimerHart, tick_params));
  IGNORE_RESULT(dif_rv_timer_irq_enable(
      &timer, kRvTimerHart, kRvTimerComparator, kDifRvTimerEnabled));
  irq_timer_ctrl(true);
  irq_global_ctrl(true);
}

/**
 * Timer IRQ handler.
 *
 * Disables the counter and clears pending interrupts.
 */
void handler_irq_timer(void) {
  // Return values of below functions are ignored to improve capture
  // performance.
  IGNORE_RESULT(dif_rv_timer_counter_set_enabled(&timer, kRvTimerHart,
                                                 kDifRvTimerDisabled));
  IGNORE_RESULT(
      dif_rv_timer_irq_clear(&timer, kRvTimerHart, kRvTimerComparator));
}

void sca_init(void) {
  pinmux_init();
  sca_init_uart();
  sca_init_gpio();
  sca_init_timer();
}

void sca_get_uart(const dif_uart_t **uart_out) { *uart_out = &uart; }

void sca_set_trigger_high() {
  IGNORE_RESULT(dif_gpio_write_all(&gpio, kGpioCaptureTriggerHigh));
}

void sca_set_trigger_low() {
  IGNORE_RESULT(dif_gpio_write_all(&gpio, kGpioCaptureTriggerLow));
}

void sca_call_and_sleep(sca_callee callee, uint32_t sleep_cycles) {
  // Start timer to wake Ibex after the callee is done.
  uint64_t current_time;
  // Return values of below functions are ignored to improve capture
  // performance.
  IGNORE_RESULT(dif_rv_timer_counter_read(&timer, kRvTimerHart, &current_time));
  IGNORE_RESULT(dif_rv_timer_arm(&timer, kRvTimerHart, kRvTimerComparator,
                                 current_time + sleep_cycles));
  IGNORE_RESULT(dif_rv_timer_counter_set_enabled(&timer, kRvTimerHart,
                                                 kDifRvTimerEnabled));

  callee();

  wait_for_interrupt();
}
