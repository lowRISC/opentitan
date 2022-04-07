// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/sca/lib/sca.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"

#include "clkmgr_regs.h"  // Generated
#include "csrng_regs.h"   // Generated
#include "edn_regs.h"     // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#if !OT_IS_ENGLISH_BREAKFAST
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#endif

/**
 * Macro for ignoring return values.
 *
 * This is needed because ‘(void)expr;` does not work for gcc.
 */
#define IGNORE_RESULT(expr) \
  if (expr) {               \
  }

/**
 * Bitfield for the trigger source.
 *
 * Bits 9 to 11 are used to select the trigger source. See chiplevel.sv.tpl for
 * details.
 */
static const bitfield_field32_t kTriggerSourceBitfield = {
    .index = 9,
    .mask = 0x7,
};

enum {
  /**
   * Bit index of the trigger gate signal for gating the trigger from software.
   *
   * See chiplevel.sv.tpl for details.
   */
  kTriggerGateBitIndex = 8,
  /**
   * RV timer settings.
   */
  kRvTimerComparator = 0,
  kRvTimerHart = kTopEarlgreyPlicTargetIbex0,
};

static dif_uart_t uart0;
static dif_gpio_t gpio;
static dif_rv_timer_t timer;

#if !OT_IS_ENGLISH_BREAKFAST
static dif_uart_t uart1;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
#endif

// TODO(alphan): Handle return values as long as they don't affect capture rate.

/**
 * Initializes the UART peripheral.
 */
static void sca_init_uart(void) {
  const dif_uart_config_t uart_config = {
      .baudrate = kUartBaudrate,
      .clk_freq_hz = kClockFreqPeripheralHz,
      .parity_enable = kDifToggleDisabled,
      .parity = kDifUartParityEven,
  };

  IGNORE_RESULT(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart0));
  IGNORE_RESULT(dif_uart_configure(&uart0, uart_config));
  base_uart_stdout(&uart0);

#if !OT_IS_ENGLISH_BREAKFAST
  IGNORE_RESULT(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART1_BASE_ADDR), &uart1));
  IGNORE_RESULT(dif_uart_configure(&uart1, uart_config));
#endif
}

/**
 * Initializes the GPIO peripheral.
 *
 * @param trigger Trigger source.
 */
static void sca_init_gpio(sca_trigger_source_t trigger) {
  IGNORE_RESULT(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));

  uint32_t select_mask =
      bitfield_field32_write(0, kTriggerSourceBitfield, UINT32_MAX);
  uint32_t enable_mask = bitfield_bit32_write(0, kTriggerGateBitIndex, true);
  IGNORE_RESULT(
      dif_gpio_output_set_enabled_all(&gpio, select_mask | enable_mask));

  IGNORE_RESULT(dif_gpio_write_masked(
      &gpio, select_mask,
      bitfield_field32_write(0, kTriggerSourceBitfield, trigger)));
}

/**
 * Initializes the timer peripheral.
 */
static void sca_init_timer(void) {
  IGNORE_RESULT(dif_rv_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR), &timer));
  IGNORE_RESULT(dif_rv_timer_reset(&timer));
  dif_rv_timer_tick_params_t tick_params;
  IGNORE_RESULT(dif_rv_timer_approximate_tick_params(
      kClockFreqPeripheralHz, kClockFreqCpuHz, &tick_params));
  IGNORE_RESULT(
      dif_rv_timer_set_tick_params(&timer, kRvTimerHart, tick_params));
  IGNORE_RESULT(dif_rv_timer_irq_set_enabled(
      &timer, kDifRvTimerIrqTimerExpiredHart0Timer0, kDifToggleEnabled));
  irq_timer_ctrl(true);
  irq_global_ctrl(true);
}

/**
 * Initializes the CSRNG handle.
 */
static void sca_init_csrng(void) {
#if !OT_IS_ENGLISH_BREAKFAST
  IGNORE_RESULT(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
#endif
}

/**
 * Initializes the EDN handle.
 */
static void sca_init_edn(void) {
#if !OT_IS_ENGLISH_BREAKFAST
  IGNORE_RESULT(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));

  IGNORE_RESULT(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
#endif
}

/**
 * Override default Timer ISR.
 *
 * Disables the counter and clears pending interrupts.
 */
void ottf_timer_isr(void) {
  // Return values of below functions are ignored to improve capture
  // performance.
  IGNORE_RESULT(dif_rv_timer_counter_set_enabled(&timer, kRvTimerHart,
                                                 kDifToggleDisabled));
  IGNORE_RESULT(dif_rv_timer_irq_acknowledge(
      &timer, kDifRvTimerIrqTimerExpiredHart0Timer0));
}

/**
 * Disables the given peripherals to reduce noise during SCA.
 *
 * Care must be taken when disabling the entropy complex if a peripheral that
 * depends on it will be used in SCA. E.g., We can disable the entropy complex
 * when analyzing AES only because AES features a parameter to skip PRNG
 * reseeding for SCA experiments. Without this parameter, AES would simply get
 * stalled with a disabled entropy complex.
 *
 * @param disable Set of peripherals to disable.
 */
void sca_disable_peripherals(sca_peripherals_t disable) {
#if !OT_IS_ENGLISH_BREAKFAST
  if (disable & kScaPeripheralEdn) {
    IGNORE_RESULT(dif_edn_stop(&edn0));
    IGNORE_RESULT(dif_edn_stop(&edn1));
  }
  if (disable & kScaPeripheralCsrng) {
    IGNORE_RESULT(dif_csrng_stop(&csrng));
  }
  if (disable & kScaPeripheralEntropy) {
    dif_entropy_src_t entropy;
    IGNORE_RESULT(dif_entropy_src_init(
        mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy));
    IGNORE_RESULT(dif_entropy_src_disable(&entropy));
  }
#endif

  // Disable HMAC, KMAC, OTBN and USB clocks through CLKMGR DIF.
  dif_clkmgr_t clkmgr;
  IGNORE_RESULT(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  if (disable & kScaPeripheralAes) {
    IGNORE_RESULT(dif_clkmgr_hintable_clock_set_hint(
        &clkmgr, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, kDifToggleDisabled));
  }
  if (disable & kScaPeripheralHmac) {
    IGNORE_RESULT(dif_clkmgr_hintable_clock_set_hint(
        &clkmgr, CLKMGR_CLK_HINTS_CLK_MAIN_HMAC_HINT_BIT, kDifToggleDisabled));
  }
  if (disable & kScaPeripheralUsb) {
    IGNORE_RESULT(dif_clkmgr_gateable_clock_set_enabled(
        &clkmgr, CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT, kDifToggleDisabled));
  }

#if !OT_IS_ENGLISH_BREAKFAST
  if (disable & kScaPeripheralKmac) {
    IGNORE_RESULT(dif_clkmgr_hintable_clock_set_hint(
        &clkmgr, CLKMGR_CLK_HINTS_CLK_MAIN_KMAC_HINT_BIT, kDifToggleDisabled));
  }
  if (disable & kScaPeripheralOtbn) {
    IGNORE_RESULT(dif_clkmgr_hintable_clock_set_hint(
        &clkmgr, CLKMGR_CLK_HINTS_CLK_MAIN_OTBN_HINT_BIT, kDifToggleDisabled));
  }
#endif
}

void sca_init(sca_trigger_source_t trigger, sca_peripherals_t enable) {
  pinmux_init();
  sca_init_uart();
  sca_init_gpio(trigger);
  sca_init_timer();
  sca_init_csrng();
  sca_init_edn();
  sca_disable_peripherals(~enable);
}

void sca_get_uart(const dif_uart_t **uart_out) {
#if !OT_IS_ENGLISH_BREAKFAST
  *uart_out = &uart1;
#else
  *uart_out = &uart0;
#endif
}

void sca_set_trigger_high() {
  IGNORE_RESULT(dif_gpio_write(&gpio, kTriggerGateBitIndex, true));
}

void sca_set_trigger_low() {
  IGNORE_RESULT(dif_gpio_write(&gpio, kTriggerGateBitIndex, false));
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
                                                 kDifToggleEnabled));

  callee();

  wait_for_interrupt();
}
