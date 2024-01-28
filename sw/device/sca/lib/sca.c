// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/sca/lib/sca.h"

#include "hw/ip/aes/model/aes.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#if !OT_IS_ENGLISH_BREAKFAST
#include "sw/ip/csrng/dif/dif_csrng.h"
#include "sw/ip/edn/dif/dif_edn.h"
#endif
#include "sw/ip/clkmgr/dif/dif_clkmgr.h"
#include "sw/ip/gpio/dif/dif_gpio.h"
#include "sw/ip/pinmux/dif/dif_pinmux.h"
#include "sw/ip/pinmux/test/utils/pinmux_testutils.h"
#include "sw/ip/rv_timer/dif/dif_rv_timer.h"
#include "sw/ip/uart/dif/dif_uart.h"
#include "sw/lib/sw/device/arch/device.h"
#include "sw/lib/sw/device/base/bitfield.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/runtime/hart.h"
#include "sw/lib/sw/device/runtime/irq.h"
#include "sw/lib/sw/device/runtime/print.h"

#include "clkmgr_regs.h"  // Generated
#include "csrng_regs.h"   // Generated
#include "edn_regs.h"     // Generated
#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

/**
 * Bitfield for the trigger source.
 *
 * Bits 10 and 11 are used to select the trigger source. See chiplevel.sv.tpl
 * for details.
 */
static const bitfield_field32_t kTriggerSourceBitfield = {
    .index = 10,
    .mask = 0x3,
};

enum {
  /**
   * Bit index of the hardware trigger gate signal for gating the hardware
   * trigger from software.
   *
   * See chiplevel.sv.tpl for details.
   */
  kTriggerHwGateBitIndex = 9,
  /**
   * Bit index of the software trigger signal.
   *
   * See chiplevel.sv.tpl for details.
   */
  kTriggerSwBitIndex = 8,
  /**
   * RV timer settings.
   */
  kRvTimerComparator = 0,
  kRvTimerHart = kTopDarjeelingPlicTargetIbex0,
};

// By default, we use the precise, hardware-gated capture trigger.
static unsigned int trigger_bit_index = kTriggerHwGateBitIndex;

static dif_uart_t uart0;
static dif_gpio_t gpio;
static dif_pinmux_t pinmux;
static dif_rv_timer_t timer;

static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;

// TODO(alphan): Handle return values as long as they don't affect capture rate.

/**
 * Initializes the UART peripheral.
 */
static void sca_init_uart(void) {
  CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");
  const dif_uart_config_t uart_config = {
      .baudrate = (uint32_t)kUartBaudrate,
      .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
      .parity_enable = kDifToggleDisabled,
      .parity = kDifUartParityEven,
      .tx_enable = kDifToggleEnabled,
      .rx_enable = kDifToggleEnabled,
  };

  OT_DISCARD(dif_uart_init(
      mmio_region_from_addr(TOP_DARJEELING_UART0_BASE_ADDR), &uart0));
  OT_DISCARD(dif_uart_configure(&uart0, uart_config));
  base_uart_stdout(&uart0);
}

/**
 * Initializes the GPIO peripheral.
 *
 * @param trigger Trigger source.
 */
static void sca_init_gpio(sca_trigger_source_t trigger) {
  OT_DISCARD(dif_gpio_init(mmio_region_from_addr(TOP_DARJEELING_GPIO_BASE_ADDR),
                           &gpio));

  uint32_t select_mask =
      bitfield_field32_write(0, kTriggerSourceBitfield, UINT32_MAX);
  uint32_t enable_mask = bitfield_bit32_write(0, kTriggerHwGateBitIndex, true);
  enable_mask = bitfield_bit32_write(enable_mask, kTriggerSwBitIndex, true);

  OT_DISCARD(dif_gpio_output_set_enabled_all(&gpio, select_mask | enable_mask));

  OT_DISCARD(dif_gpio_write_masked(
      &gpio, select_mask,
      bitfield_field32_write(0, kTriggerSourceBitfield, trigger)));
}

/**
 * Initializes the timer peripheral.
 */
static void sca_init_timer(void) {
  OT_DISCARD(dif_rv_timer_init(
      mmio_region_from_addr(TOP_DARJEELING_RV_TIMER_BASE_ADDR), &timer));
  OT_DISCARD(dif_rv_timer_reset(&timer));
  dif_rv_timer_tick_params_t tick_params;
  OT_DISCARD(dif_rv_timer_approximate_tick_params(
      kClockFreqPeripheralHz, kClockFreqCpuHz, &tick_params));
  OT_DISCARD(dif_rv_timer_set_tick_params(&timer, kRvTimerHart, tick_params));
  OT_DISCARD(dif_rv_timer_irq_set_enabled(
      &timer, kDifRvTimerIrqTimerExpiredHart0Timer0, kDifToggleEnabled));
  irq_timer_ctrl(true);
  irq_global_ctrl(true);
}

/**
 * Initializes the CSRNG handle.
 */
static void sca_init_csrng(void) {
#if !OT_IS_ENGLISH_BREAKFAST
  OT_DISCARD(dif_csrng_init(
      mmio_region_from_addr(TOP_DARJEELING_CSRNG_BASE_ADDR), &csrng));
  OT_DISCARD(dif_csrng_init(
      mmio_region_from_addr(TOP_DARJEELING_CSRNG_BASE_ADDR), &csrng));
#endif
}

/**
 * Initializes the EDN handle.
 */
static void sca_init_edn(void) {
#if !OT_IS_ENGLISH_BREAKFAST
  OT_DISCARD(dif_edn_init(mmio_region_from_addr(TOP_DARJEELING_EDN0_BASE_ADDR),
                          &edn0));

  OT_DISCARD(dif_edn_init(mmio_region_from_addr(TOP_DARJEELING_EDN1_BASE_ADDR),
                          &edn1));
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
  OT_DISCARD(dif_rv_timer_counter_set_enabled(&timer, kRvTimerHart,
                                              kDifToggleDisabled));
  OT_DISCARD(dif_rv_timer_irq_acknowledge(
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
    OT_DISCARD(dif_edn_stop(&edn0));
    OT_DISCARD(dif_edn_stop(&edn1));
  }
  if (disable & kScaPeripheralCsrng) {
    OT_DISCARD(dif_csrng_stop(&csrng));
  }
#endif

  // Disable HMAC, KMAC, OTBN and USB clocks through CLKMGR DIF.
  dif_clkmgr_t clkmgr;
  OT_DISCARD(dif_clkmgr_init(
      mmio_region_from_addr(TOP_DARJEELING_CLKMGR_AON_BASE_ADDR), &clkmgr));

  if (disable & kScaPeripheralAes) {
    OT_DISCARD(dif_clkmgr_hintable_clock_set_hint(
        &clkmgr, CLKMGR_CLK_HINTS_CLK_MAIN_AES_HINT_BIT, kDifToggleDisabled));
  }
#if !OT_IS_ENGLISH_BREAKFAST
  if (disable & kScaPeripheralHmac) {
    OT_DISCARD(dif_clkmgr_hintable_clock_set_hint(
        &clkmgr, CLKMGR_CLK_HINTS_CLK_MAIN_HMAC_HINT_BIT, kDifToggleDisabled));
  }
#endif
  if (disable & kScaPeripheralIoDiv4) {
    OT_DISCARD(dif_clkmgr_gateable_clock_set_enabled(
        &clkmgr, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT,
        kDifToggleDisabled));
  }
  if (disable & kScaPeripheralIoDiv2) {
    OT_DISCARD(dif_clkmgr_gateable_clock_set_enabled(
        &clkmgr, CLKMGR_CLK_ENABLES_CLK_IO_DIV2_PERI_EN_BIT,
        kDifToggleDisabled));
  }
  if (disable & kScaPeripheralUsb) {
    OT_DISCARD(dif_clkmgr_gateable_clock_set_enabled(
        &clkmgr, CLKMGR_CLK_ENABLES_CLK_USB_PERI_EN_BIT, kDifToggleDisabled));
  }
  if (disable & kScaPeripheralIo) {
    OT_DISCARD(dif_clkmgr_gateable_clock_set_enabled(
        &clkmgr, CLKMGR_CLK_ENABLES_CLK_IO_PERI_EN_BIT, kDifToggleDisabled));
  }

#if !OT_IS_ENGLISH_BREAKFAST
  if (disable & kScaPeripheralKmac) {
    OT_DISCARD(dif_clkmgr_hintable_clock_set_hint(
        &clkmgr, CLKMGR_CLK_HINTS_CLK_MAIN_KMAC_HINT_BIT, kDifToggleDisabled));
  }
  if (disable & kScaPeripheralOtbn) {
    OT_DISCARD(dif_clkmgr_hintable_clock_set_hint(
        &clkmgr, CLKMGR_CLK_HINTS_CLK_MAIN_OTBN_HINT_BIT, kDifToggleDisabled));
  }
#endif
}

void sca_init(sca_trigger_source_t trigger, sca_peripherals_t enable) {
  OT_DISCARD(dif_pinmux_init(
      mmio_region_from_addr(TOP_DARJEELING_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  sca_init_uart();
  sca_init_gpio(trigger);
  sca_init_timer();
  sca_init_csrng();
  sca_init_edn();
  sca_disable_peripherals(~enable);
}

const dif_uart_t *sca_get_uart(void) { return &uart0; }

void sca_select_trigger_type(sca_trigger_type_t trigger_type) {
  if (trigger_type == kScaTriggerTypeHwGated) {
    trigger_bit_index = kTriggerHwGateBitIndex;
  } else if (trigger_type == kScaTriggerTypeSw) {
    trigger_bit_index = kTriggerSwBitIndex;
  }
}

void sca_set_trigger_high(void) {
  OT_DISCARD(dif_gpio_write(&gpio, trigger_bit_index, true));
}

void sca_set_trigger_low(void) {
  OT_DISCARD(dif_gpio_write(&gpio, trigger_bit_index, false));
}

void sca_call_and_sleep(sca_callee callee, uint32_t sleep_cycles) {
  // Disable the IO_DIV4_PERI clock to reduce noise during the actual capture.
  // This also disables the UART(s) and GPIO modules required for
  // communication with the scope. Therefore, it has to be re-enabled after
  // the capture.
  dif_clkmgr_t clkmgr;
  OT_DISCARD(dif_clkmgr_init(
      mmio_region_from_addr(TOP_DARJEELING_CLKMGR_AON_BASE_ADDR), &clkmgr));

  // Start timer to wake Ibex after the callee is done.
  uint64_t current_time;
  // Return values of below functions are ignored to improve capture
  // performance.
  OT_DISCARD(dif_rv_timer_counter_read(&timer, kRvTimerHart, &current_time));
  OT_DISCARD(dif_rv_timer_arm(&timer, kRvTimerHart, kRvTimerComparator,
                              current_time + sleep_cycles));
  OT_DISCARD(dif_rv_timer_counter_set_enabled(&timer, kRvTimerHart,
                                              kDifToggleEnabled));

  callee();

  wait_for_interrupt();

  // Re-enable IO_DIV4_PERI clock to resume communication with the scope.
  OT_DISCARD(dif_clkmgr_gateable_clock_set_enabled(
      &clkmgr, CLKMGR_CLK_ENABLES_CLK_IO_DIV4_PERI_EN_BIT, kDifToggleEnabled));
}

static uint32_t sca_lfsr_state_masking = 0xdeadbeef;
static uint32_t sca_lfsr_state_order = 0x99999999;

void sca_seed_lfsr(uint32_t seed, sca_lfsr_context_t context) {
  if (context == kScaLfsrMasking) {
    sca_lfsr_state_masking = seed;
  }
  if (context == kScaLfsrOrder) {
    sca_lfsr_state_masking = seed;
  }
}

uint32_t sca_next_lfsr(uint16_t num_steps, sca_lfsr_context_t context) {
  uint32_t sca_lfsr_state;
  if (context == kScaLfsrMasking) {
    sca_lfsr_state = sca_lfsr_state_masking;
  }
  if (context == kScaLfsrOrder) {
    sca_lfsr_state = sca_lfsr_state_order;
  }
  const uint32_t lfsr_out = sca_lfsr_state;
  for (size_t i = 0; i < num_steps; ++i) {
    bool lfsr_bit = sca_lfsr_state & 0x00000001;
    sca_lfsr_state = sca_lfsr_state >> 1;
    if (lfsr_bit) {
      sca_lfsr_state ^= 0x80000057;
    }
  }
  if (context == kScaLfsrMasking) {
    sca_lfsr_state_masking = sca_lfsr_state;
  }
  if (context == kScaLfsrOrder) {
    sca_lfsr_state_order = sca_lfsr_state;
  }
  return lfsr_out;
}

uint32_t sca_linear_layer(uint32_t input) {
  uint32_t output =
      // output[7:0]
      (((input >> 0) & 0x1) << 7) | (((input >> 6) & 0x1) << 6) |
      (((input >> 11) & 0x1) << 5) | (((input >> 14) & 0x1) << 4) |
      (((input >> 1) & 0x1) << 3) | (((input >> 7) & 0x1) << 2) |
      (((input >> 10) & 0x1) << 1) | (((input >> 13) & 0x1) << 0) |
      // output[15:8]
      (((input >> 2) & 0x1) << 15) | (((input >> 4) & 0x1) << 14) |
      (((input >> 9) & 0x1) << 13) | (((input >> 12) & 0x1) << 12) |
      (((input >> 3) & 0x1) << 11) | (((input >> 5) & 0x1) << 10) |
      (((input >> 8) & 0x1) << 9) | (((input >> 15) & 0x1) << 8) |
      // output[23:16]
      (((input >> 16) & 0x1) << 23) | (((input >> 22) & 0x1) << 22) |
      (((input >> 27) & 0x1) << 21) | (((input >> 30) & 0x1) << 20) |
      (((input >> 17) & 0x1) << 19) | (((input >> 23) & 0x1) << 18) |
      (((input >> 26) & 0x1) << 17) | (((input >> 29) & 0x1) << 16) |
      // output[31:24]
      (((input >> 18) & 0x1) << 31) | (((input >> 20) & 0x1) << 30) |
      (((input >> 25) & 0x1) << 29) | (((input >> 28) & 0x1) << 28) |
      (((input >> 19) & 0x1) << 27) | (((input >> 21) & 0x1) << 26) |
      (((input >> 24) & 0x1) << 25) | (((input >> 31) & 0x1) << 24);

  return output;
}

uint32_t sca_non_linear_layer(uint32_t input) {
  uint32_t output;
  if (input != 0) {
    // Perform the AES S-Box look ups bytewise.
    output = (uint32_t)(sbox[(input >> 24) & 0xFF] << 24) |
             (uint32_t)(sbox[(input >> 16) & 0xFF] << 16) |
             (uint32_t)(sbox[(input >> 8) & 0xFF] << 8) | sbox[input & 0xFF];
  } else {
    output = input;
  }

  return output;
}
