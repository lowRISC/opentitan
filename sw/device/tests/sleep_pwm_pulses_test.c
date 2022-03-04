// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwm.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pwm_regs.h"

/**
 * SLEEP PWM PULSES test
 *
 * This test configure 6 pwm channels with a fixed duty cycle
 * then kicks power manager sleep mode to see pwm pluses are
 * not affected by power down event.
 * pwm out --> pinmux setup is chosen arbitrary as below
 *      pwmout[0] -> IOB10
 *      pwmout[1] -> IOB11
 *      pwmout[2] -> IOB12
 *      pwmout[3] -> IOc10
 *      pwmout[4] -> IOc11
 *      pwmout[5] -> IOc12
 *
 * Since purpose of this test is to check pwm -> pinmux
 * connectivity and pulse integrity under sleep event,
 * Fixed pwm configuration, mode and 0 phase delay are chosen.
 */

static const dif_pinmux_index_t kPinmuxOutsel[PWM_PARAM_N_OUTPUTS] = {
    kTopEarlgreyPinmuxOutselPwmAonPwm0, kTopEarlgreyPinmuxOutselPwmAonPwm1,
    kTopEarlgreyPinmuxOutselPwmAonPwm2, kTopEarlgreyPinmuxOutselPwmAonPwm3,
    kTopEarlgreyPinmuxOutselPwmAonPwm4, kTopEarlgreyPinmuxOutselPwmAonPwm5,
};

static const dif_pinmux_index_t kPinmuxMioOut[PWM_PARAM_N_OUTPUTS] = {
    kTopEarlgreyPinmuxMioOutIob10, kTopEarlgreyPinmuxMioOutIob11,
    kTopEarlgreyPinmuxMioOutIob12, kTopEarlgreyPinmuxMioOutIoc10,
    kTopEarlgreyPinmuxMioOutIoc11, kTopEarlgreyPinmuxMioOutIoc12,
};

static const dif_pwm_channel_t kPwmChannel[PWM_PARAM_N_OUTPUTS] = {
    kDifPwmChannel0, kDifPwmChannel1, kDifPwmChannel2,
    kDifPwmChannel3, kDifPwmChannel4, kDifPwmChannel5,
};

// Duty cycle in the unit of beat
// These are random numbers betwen [1,beats_per_pulse_cycle)
// make 'static volatile' to overwrite from
// hw/top_earlgrey/dv/env/seq_lib/chip_sw_pwm_pulses_vseq.sv
// via backdoor
static volatile const uint16_t kPwmDutycycle[PWM_PARAM_N_OUTPUTS] = {
    6, 11, 27, 8, 17, 7,
};

static const dif_pwm_config_t config_ = {
    // set beat period to 3
    .clock_divisor = 2,

    // upper 5bits of phase cntr only matter
    // and total(on+off) beats per cycle will be 32
    .beats_per_pulse_cycle = 32,
};

// This is initial value of config variable
static const dif_pwm_channel_config_t default_ch_cfg_ = {
    .duty_cycle_a = 0,
    .duty_cycle_b = 0,
    .phase_delay = 0,
    .mode = kDifPwmModeFirmware,
    .polarity = kDifPwmPolarityActiveHigh,
    .blink_parameter_x = 0,
    .blink_parameter_y = 0,
};

// Configure pwm channel register for all 6 channels.
// This also contain disable and enable each channel.
void config_pwm_channels(dif_pwm_t *pwm) {
  dif_pwm_channel_config_t channel_config_ = default_ch_cfg_;

  for (int i = 0; i < PWM_PARAM_N_OUTPUTS; ++i) {
    CHECK_DIF_OK(
        dif_pwm_channel_set_enabled(pwm, kPwmChannel[i], kDifToggleDisabled));
    channel_config_.duty_cycle_a = kPwmDutycycle[i];
    CHECK_DIF_OK(
        dif_pwm_configure_channel(pwm, kPwmChannel[i], channel_config_));
    CHECK_DIF_OK(
        dif_pwm_channel_set_enabled(pwm, kPwmChannel[i], kDifToggleEnabled));
  }
}

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;

  // Issue a wakeup signal in ~150us through the AON timer.
  //
  // At 200kHz, threshold of 30 is equal to 150us. There is an additional
  // ~4 cycle overhead for the CSR value to synchronize with the AON clock.
  // We should expect the wake up to trigger in ~170us. This is sufficient
  // time to allow pwrmgr config and the low power entry on WFI to complete.
  //
  // Adjust the threshold for Verilator since it runs on different clock
  // frequencies.
  uint32_t wakeup_threshold = 30;
  if (kDeviceType == kDeviceSimVerilator) {
    wakeup_threshold = 300;
  }

  // Initialize pwrmgr
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));

  // Initialize rstmgr since this will check some registers.
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Assuming the chip hasn't slept yet, wakeup reason should be empty.

  // Notice we are clearing rstmgr's RESET_INFO, so after the aon wakeup there
  // is only one bit set.
  if (pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) {
    dif_pwm_t pwm;
    dif_pinmux_t pinmux;
    // Initialize pwm
    CHECK_DIF_OK(dif_pwm_init(
        mmio_region_from_addr(TOP_EARLGREY_PWM_AON_BASE_ADDR), &pwm));

    // Update pwm.CFG
    CHECK_DIF_OK(dif_pwm_configure(&pwm, config_));

    // Update all 6 pwm channels
    config_pwm_channels(&pwm);

    // enable phase count to make the change effective
    CHECK_DIF_OK(dif_pwm_phase_cntr_set_enabled(&pwm, kDifToggleEnabled));

    // Initialize pinmux - this assigns PwmAonPwm[0..5] to
    // IOB10..12 and IOC10..12
    // LOG_INFO is used to indicate pwmout is available to
    // SV pwm_monitor
    CHECK_DIF_OK(dif_pinmux_init(
        mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

    LOG_INFO("pinmux_init begin");
    for (int i = 0; i < PWM_PARAM_N_OUTPUTS; ++i) {
      CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kPinmuxMioOut[i],
                                            kPinmuxOutsel[i]));
    }
    LOG_INFO("pinmux_init end");

    // Add 1ms to initial pulses go through before sleep event
    busy_spin_micros(1 * 1000);

    LOG_INFO("POR reset");
    CHECK(rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoPor));

    // Prepare rstmgr for a reset.
    rstmgr_testutils_pre_reset(&rstmgr);

    dif_aon_timer_t aon_timer;
    CHECK_DIF_OK(dif_aon_timer_init(
        mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR),
        &aon_timer));
    aon_timer_testutils_wakeup_config(&aon_timer, wakeup_threshold);
    // Deep sleep.
    pwrmgr_testutils_enable_low_power(&pwrmgr,
                                      kDifPwrmgrWakeupRequestSourceFive, 0);

    // Enter low power mode.
    LOG_INFO("Issue WFI to enter sleep");
    wait_for_interrupt();

  } else if (pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr, kDifPwrmgrWakeupRequestSourceFive)) {
    LOG_INFO("Wakeup reset");

    CHECK(rstmgr_testutils_is_reset_info(&rstmgr,
                                         kDifRstmgrResetInfoLowPowerExit));
    LOG_INFO("Aon timer wakeup detected");
    rstmgr_testutils_post_reset(&rstmgr, kDifRstmgrResetInfoLowPowerExit, 0, 0,
                                0, 0);

    // add another 2ms to give more time to pwm pulses sequences
    busy_spin_micros(2 * 1000);

    return true;
  } else {
    dif_pwrmgr_wakeup_reason_t wakeup_reason;
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
    LOG_ERROR("Unexpected wakeup detected: type = %d, request_source = %d",
              wakeup_reason.types, wakeup_reason.request_sources);
    return false;
  }

  return false;
}
