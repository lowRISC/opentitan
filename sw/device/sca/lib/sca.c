// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/sca/lib/sca.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_entropy.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/print.h"

#include "clkmgr_regs.h"  // Generated
#include "csrng_regs.h"   // Generated
#include "edn_regs.h"     // Generated
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
   *
   * GPIO10[11:9]: Trigger select, 000 for AES, see chiplevel.sv.tpl for
   *               details.
   * GPIO8:        Trigger enable
   */
  kGpioCaptureTriggerSelMask = 0x00E00,
  kGpioCaptureTriggerEnMask = 0x00100,
  kGpioCaptureTriggerSel = 0x00000,
  kGpioCaptureTriggerHigh = 0x00100,
  kGpioCaptureTriggerLow = 0x00000,
  /**
   * RV timer settings.
   */
  kRvTimerComparator = 0,
  kRvTimerHart = kTopEarlgreyPlicTargetIbex0,
};

static dif_uart_t uart0;
static dif_uart_t uart1;
static dif_gpio_t gpio;
static dif_rv_timer_t timer;

// TODO(alphan): Handle return values as long as they don't affect capture rate.

/**
 * Initializes the UART peripheral.
 */
static void sca_init_uart(void) {
  const dif_uart_config_t uart_config = {
      .baudrate = kUartBaudrate,
      .clk_freq_hz = kClockFreqPeripheralHz,
      .parity_enable = kDifUartToggleDisabled,
      .parity = kDifUartParityEven,
  };

  IGNORE_RESULT(dif_uart_init(
      (dif_uart_params_t){
          .base_addr = mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR),
      },
      &uart0));
  IGNORE_RESULT(dif_uart_configure(&uart0, uart_config));
  base_uart_stdout(&uart0);

  IGNORE_RESULT(dif_uart_init(
      (dif_uart_params_t){
          .base_addr = mmio_region_from_addr(TOP_EARLGREY_UART1_BASE_ADDR),
      },
      &uart1));
  IGNORE_RESULT(dif_uart_configure(&uart1, uart_config));
}

/**
 * Initializes the GPIO peripheral.
 */
static void sca_init_gpio(void) {
  dif_gpio_params_t gpio_params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR)};
  IGNORE_RESULT(dif_gpio_init(gpio_params, &gpio));
  IGNORE_RESULT(dif_gpio_output_set_enabled_all(
      &gpio, kGpioCaptureTriggerSelMask | kGpioCaptureTriggerEnMask));
  IGNORE_RESULT(dif_gpio_write_masked(&gpio, kGpioCaptureTriggerSelMask,
                                      kGpioCaptureTriggerSel));
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

void sca_reduce_noise() {
  // Disable/stopping functionality not yet provided by EDN and CSRNG DIFs.
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR),
                      EDN_CTRL_REG_OFFSET, EDN_CTRL_REG_RESVAL);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR),
                      EDN_CTRL_REG_OFFSET, EDN_CTRL_REG_RESVAL);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR),
                      CSRNG_CTRL_REG_OFFSET, CSRNG_CTRL_REG_RESVAL);

  // Disable entropy source through DIF.
  const dif_entropy_params_t entropy_params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR),
  };
  dif_entropy_t entropy;
  IGNORE_RESULT(dif_entropy_init(entropy_params, &entropy) == kDifEntropyOk);
  IGNORE_RESULT(dif_entropy_disable(&entropy) == kDifEntropyOk);

  // Disable HMAC, KMAC, OTBN and USB clocks through CLKMGR DIF.
  const dif_clkmgr_params_t clkmgr_params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR),
      .last_gateable_clock = CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT,
      .last_hintable_clock = CLKMGR_CLK_HINTS_STATUS_CLK_MAIN_OTBN_VAL_BIT};
  dif_clkmgr_t clkmgr;
  IGNORE_RESULT(dif_clkmgr_init(clkmgr_params, &clkmgr) == kDifClkmgrOk);
  IGNORE_RESULT(dif_clkmgr_hintable_clock_set_hint(
                    &clkmgr, CLKMGR_CLK_HINTS_CLK_MAIN_HMAC_HINT_BIT,
                    kDifClkmgrToggleDisabled) == kDifClkmgrOk);
  IGNORE_RESULT(dif_clkmgr_hintable_clock_set_hint(
                    &clkmgr, CLKMGR_CLK_HINTS_CLK_MAIN_KMAC_HINT_BIT,
                    kDifClkmgrToggleDisabled) == kDifClkmgrOk);
  IGNORE_RESULT(dif_clkmgr_hintable_clock_set_hint(
                    &clkmgr, CLKMGR_CLK_HINTS_CLK_IO_DIV4_OTBN_HINT_BIT,
                    kDifClkmgrToggleDisabled) == kDifClkmgrOk);
  IGNORE_RESULT(dif_clkmgr_hintable_clock_set_hint(
                    &clkmgr, CLKMGR_CLK_HINTS_CLK_MAIN_OTBN_HINT_BIT,
                    kDifClkmgrToggleDisabled) == kDifClkmgrOk);
  IGNORE_RESULT(dif_clkmgr_gateable_clock_set_enabled(
                    &clkmgr, CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT,
                    kDifClkmgrToggleDisabled) == kDifClkmgrOk);
}

void sca_get_uart(const dif_uart_t **uart_out) { *uart_out = &uart1; }

void sca_set_trigger_high() {
  IGNORE_RESULT(dif_gpio_write_masked(&gpio, kGpioCaptureTriggerEnMask,
                                      kGpioCaptureTriggerHigh));
}

void sca_set_trigger_low() {
  IGNORE_RESULT(dif_gpio_write_masked(&gpio, kGpioCaptureTriggerEnMask,
                                      kGpioCaptureTriggerLow));
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
