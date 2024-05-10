// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

// PLIC structures
static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static dif_gpio_t gpio;
static dif_pwrmgr_t pwrmgr;
static dif_pinmux_t pinmux;
static dif_pwrmgr_domain_config_t pwrmgr_domain_cfg;
static dif_rv_plic_t plic;

static plic_isr_ctx_t plic_ctx = {.rv_plic = &plic, .hart_id = kPlicTarget};
static pwrmgr_isr_ctx_t pwrmgr_isr_ctx = {
    .pwrmgr = &pwrmgr,
    .plic_pwrmgr_start_irq_id = kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
    .expected_irq = kDifPwrmgrIrqWakeup,
    .is_only_irq = true};

// SV randomizes the round of entering/exiting sleep then set this volatile
// variable via backdoor_overwrite.
static volatile const uint8_t kRounds = 2;

// To wakeup and maintain GPIO, for now test enters to normal sleep only.
static const bool deepPowerdown = false;

// Num of GPIO Pads to test
enum { kNumGpioPadsDv = 8, kNumGpioPadsSiVal = 4 };
int num_gpio_pads;  // One of the above, based on the actual environment.

unsigned gpio_mask;

static int first_gpio_pin;

/**
 * External interrupt handler.
 */
void ottf_external_isr(uint32_t *exc_info) {
  dif_pwrmgr_irq_t irq_id;
  top_earlgrey_plic_peripheral_t peripheral;

  isr_testutils_pwrmgr_isr(plic_ctx, pwrmgr_isr_ctx, &peripheral, &irq_id);

  // Check that both the peripheral and the irq id is correct
  CHECK(peripheral == kTopEarlgreyPlicPeripheralPwrmgrAon,
        "IRQ peripheral: %d is incorrect", peripheral);
  CHECK(irq_id == kDifPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq_id);

  // Clear PINMUX WKUP_CAUSE reg
  CHECK_DIF_OK(dif_pinmux_wakeup_cause_clear(&pinmux));
}

/**
 * A round of GPIO[num_gpio_pads-1:0] retention value test.
 *
 * The test sequence is:
 *
 * 1. Randomly choose GPIO[num_gpio_pads-1:0] value using rand_testutils.
 * 2. Drive GPIO with the chosen value.
 * 3. Send the chosen values to SV/host via LOG_INFO.
 * 4. Configure PINMUX Retention value opposit to the chosen value for
 *    GPIO[num_gpio_pads-1:0].
 * 5. Initiate sleep mode (assuming pinmux pin wake up has been configured.)
 * 6. WFI()
 * 7. At this point, chip has been waken up by DV/host. Send a log to DV/host
 *    that the chip has waken up.
 *
 * DV/host env checks all PIN value. SW simply drives the GPIO and invert the
 * value for retention.
 */
void gpio_test(dif_pwrmgr_t *pwrmgr, dif_pinmux_t *pinmux, dif_gpio_t *gpio,
               int round) {
  uint8_t gpio_val = 0;
  dif_pinmux_pad_kind_t pad_kind;
  dif_pinmux_sleep_mode_t pad_mode;

  LOG_INFO("Current Test Round: %1d", round);

  // 1. Randomly choose GPIO value
  gpio_val = (uint8_t)(rand_testutils_gen32_range(0, gpio_mask));

  // 2. Drive GPIO with the chosen value.
  CHECK_DIF_OK(dif_gpio_write_masked(gpio, (dif_gpio_mask_t)gpio_mask,
                                     (dif_gpio_state_t)gpio_val));

  // 3. Send the chosen value to SV via LOG_INFO.
  //
  // The format is:
  //
  //     Chosen GPIO value: %2x
  LOG_INFO("Chosen GPIO value: %2x", gpio_val);

  // 4. Configure PINMUX Retention value opposite to the chosen value.
  pad_kind = kDifPinmuxPadKindMio;
  for (int i = 0; i < num_gpio_pads; i++) {
    // GPIO are assigned starting from MIO0
    pad_mode = ((gpio_val >> i) & 0x1) ? kDifPinmuxSleepModeLow
                                       : kDifPinmuxSleepModeHigh;
    CHECK_DIF_OK(dif_pinmux_pad_sleep_enable(
        pinmux, (dif_pinmux_index_t)(first_gpio_pin + i), pad_kind, pad_mode));
  }

  // 5. Initiate sleep mode
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      pwrmgr, kDifPwrmgrWakeupRequestSourceThree, pwrmgr_domain_cfg));
  // 6. WFI()
  LOG_INFO("Entering low power mode.");
  wait_for_interrupt();

  // 7. Turn-off retention.
  for (int i = 0; i < num_gpio_pads; i++) {
    CHECK_DIF_OK(dif_pinmux_pad_sleep_clear_state(
        pinmux, (dif_pinmux_index_t)(first_gpio_pin + i), pad_kind));
  }

  LOG_INFO("Woke up from low power mode.");

  // When running outside DV, wait until the host is ready to end this round.
  bool end_round = false;
  if (kDeviceType != kDeviceSimDV)
    do {
      CHECK_DIF_OK(dif_gpio_read(gpio, 8, &end_round));
    } while (!end_round);
}

/**
 * Configure GPIO
 *
 * gpio_init() configures first 8 MIO PADs to GPIO[7:0].
 */
void gpio_init(const dif_pinmux_t *pinmux, const dif_gpio_t *gpio) {
  // Drive GPIO first
  CHECK_DIF_OK(
      dif_gpio_output_set_enabled_all(gpio, (dif_gpio_state_t)gpio_mask));
  CHECK_DIF_OK(dif_gpio_write_masked(gpio, (dif_gpio_mask_t)gpio_mask,
                                     (dif_gpio_state_t)0x00000000));

  // Configure PINMUX to GPIO
  for (int i = 0; i < num_gpio_pads; i++) {
    CHECK_DIF_OK(dif_pinmux_input_select(
        pinmux,
        (dif_pinmux_index_t)(kTopEarlgreyPinmuxPeripheralInGpioGpio0 + i),
        (dif_pinmux_index_t)(first_gpio_pin + i)));
    CHECK_DIF_OK(dif_pinmux_output_select(
        pinmux, (dif_pinmux_index_t)(first_gpio_pin + i),
        (dif_pinmux_index_t)(kTopEarlgreyPinmuxOutselGpioGpio0 + i)));
  }

  // Configure PINMUX an additional GPIO pin for the SiVal host to sync with
  // the device and indicate the round can end.
  CHECK_DIF_OK(dif_pinmux_input_select(
      pinmux, (dif_pinmux_index_t)kTopEarlgreyPinmuxPeripheralInGpioGpio8,
      (dif_pinmux_index_t)kTopEarlgreyPinmuxInselIor11));
}

bool test_main(void) {
  bool result = true;

  num_gpio_pads =
      kDeviceType == kDeviceSimDV ? kNumGpioPadsDv : kNumGpioPadsSiVal;
  gpio_mask = (1 << num_gpio_pads) - 1;
  first_gpio_pin = kDeviceType == kDeviceSimDV ? kTopEarlgreyPinmuxMioOutIoa0
                                               : kTopEarlgreyPinmuxMioOutIob0;

  dif_pinmux_wakeup_config_t wakeup_cfg;

  // Default Deep Power Down

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Initialize power manager
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&plic, kPlicTarget,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);
  // Enable pwrmgr interrupt
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  // Wakeup configs
  wakeup_cfg.mode = kDifPinmuxWakeupModePositiveEdge;
  wakeup_cfg.signal_filter = false;
  wakeup_cfg.pad_type = kDifPinmuxPadKindMio;
  wakeup_cfg.pad_select = kDeviceType == kDeviceSimDV
                              ? kTopEarlgreyPinmuxInselIoa8
                              : kTopEarlgreyPinmuxInselIor10;

  // Configure Wakeup Detector 0
  CHECK_DIF_OK(dif_pinmux_wakeup_detector_enable(&pinmux, 0, wakeup_cfg));

  if (deepPowerdown == false) {
    // Configure Normal Sleep
    pwrmgr_domain_cfg = kDifPwrmgrDomainOptionMainPowerInLowPower |
                        kDifPwrmgrDomainOptionUsbClockInActivePower;
  }

  LOG_INFO("Num Rounds: %3d", kRounds);

  // Select the appropriate GPIO pins
  gpio_init(&pinmux, &gpio);

  for (int i = kRounds - 1; i >= 0; i--) {
    gpio_test(&pwrmgr, &pinmux, &gpio, i);
  }

  return result;
}
