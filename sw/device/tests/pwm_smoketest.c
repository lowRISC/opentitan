// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwm.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static volatile const uint8_t kClocksHz[] = {24, 48, 96};
static volatile const uint8_t kDutyCycles[] = {11, 36, 50, 71, 91};

static dif_pwm_config_t compute_clk_config(uint32_t pwm_clk) {
  enum {
    kDutyCycleResolution = 5,
    kBeatsPerCycle = 1 << (kDutyCycleResolution + 1),  // 2 ^ (DC_RESN + 1)
  };
  return (dif_pwm_config_t){
      .beats_per_pulse_cycle = kBeatsPerCycle,
      .clock_divisor =
          ((uint32_t)kClockFreqAonHz / (kBeatsPerCycle * pwm_clk)) - 1};
}

bool test_main(void) {
  dif_pwm_t pwm;
  mmio_region_t addr = mmio_region_from_addr(TOP_EARLGREY_PWM_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwm_init(addr, &pwm));

  dif_pinmux_t pinmux;
  addr = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pinmux_init(addr, &pinmux));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoa8,
                                        kTopEarlgreyPinmuxOutselPwmAonPwm0));

  dif_gpio_t gpio;
  addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR);
  CHECK_DIF_OK(dif_gpio_init(addr, &gpio));
  CHECK_DIF_OK(dif_gpio_output_set_enabled_all(&gpio, 0x1));

  // The host uses IOA7 to let the device know when the sampling started.
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInGpioGpio0,
                                       kTopEarlgreyPinmuxInselIoa7));

  for (size_t i = 0; i < ARRAYSIZE(kClocksHz); ++i) {
    dif_pwm_config_t pwm_config = compute_clk_config(kClocksHz[i]);
    for (size_t j = 0; j < ARRAYSIZE(kDutyCycles); ++j) {
      dif_pwm_channel_config_t channel_config = {
          .duty_cycle_a = (uint16_t)(pwm_config.beats_per_pulse_cycle *
                                     kDutyCycles[j] / 100),
          .duty_cycle_b = 0,
          .phase_delay = 0,
          .mode = kDifPwmModeFirmware,
          .polarity = kDifPwmPolarityActiveHigh,
          .blink_parameter_x = 0,
          .blink_parameter_y = 0,
      };

      CHECK_DIF_OK(dif_pwm_configure(&pwm, pwm_config));
      CHECK_DIF_OK(
          dif_pwm_configure_channel(&pwm, kDifPwmChannel0, channel_config));

      // The IOA7 goes low when the host is sampling.
      bool not_sampling = true;
      do {
        CHECK_DIF_OK(dif_gpio_read(&gpio, 0, &not_sampling));
        if (!not_sampling) {  // Debounce
          busy_spin_micros(50);
          CHECK_DIF_OK(dif_gpio_read(&gpio, 0, &not_sampling));
        }
      } while (not_sampling);

      CHECK_DIF_OK(dif_pwm_phase_cntr_set_enabled(&pwm, kDifToggleEnabled));
      CHECK_DIF_OK(dif_pwm_channel_set_enabled(&pwm, kDifPwmChannel0,
                                               kDifToggleEnabled));

      // The goes high when the host stop sampling.
      do {
        CHECK_DIF_OK(dif_gpio_read(&gpio, 0, &not_sampling));
      } while (!not_sampling);

      CHECK_DIF_OK(dif_pwm_channel_set_enabled(&pwm, kDifPwmChannel0,
                                               kDifToggleDisabled));
      CHECK_DIF_OK(dif_pwm_phase_cntr_set_enabled(&pwm, kDifToggleDisabled));
    }
  }
  return true;
}
