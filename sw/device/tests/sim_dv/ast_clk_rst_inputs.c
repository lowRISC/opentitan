// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sensor_ctrl_regs.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

#define kAlertSet true
#define kAlertClear false
#define kAlertVal7 7
#define kAlertVal8 8
#define kDifNoWakeup 0

OTTF_DEFINE_TEST_CONFIG();

static volatile const uint8_t kNumLowPowerSamples;
static volatile const uint8_t kNumNormalPowerSamples;
static volatile const uint8_t kWakeUpTimeInUs;

static volatile const uint8_t kChannel0MaxLowByte;
static volatile const uint8_t kChannel0MaxHighByte;
static volatile const uint8_t kChannel0MinLowByte;
static volatile const uint8_t kChannel0MinHighByte;

static volatile const uint8_t kChannel1MaxLowByte;
static volatile const uint8_t kChannel1MaxHighByte;
static volatile const uint8_t kChannel1MinLowByte;
static volatile const uint8_t kChannel1MinHighByte;

static dif_sensor_ctrl_t sensor_ctrl;
static dif_alert_handler_t alert_handler;
static dif_aon_timer_t aon_timer;
static dif_rv_plic_t rv_plic;
static dif_rv_plic_t plic;
static dif_pwrmgr_t pwrmgr;
static dif_rstmgr_t rstmgr;
static dif_entropy_src_t entropy_src;

static dif_clkmgr_t clkmgr;
static dif_adc_ctrl_t adc_ctrl;

static volatile bool interrupt_serviced = false;
static bool first_adc_setup = true;

enum {
  /**
   * The size of the buffer used in firmware to process the entropy bits in
   * firmware override mode.
   */
  kEntropyFifoBufferSize = 32,
};

enum {
  kPowerUpTimeInUs = 30,
};

static uint32_t read_fifo_depth(dif_entropy_src_t *entropy) {
  uint32_t fifo_depth = 0;
  CHECK_DIF_OK(dif_entropy_src_get_fifo_depth(entropy, &fifo_depth));
  return fifo_depth;
}

static uint32_t get_events(dif_toggle_t fatal) {
  dif_sensor_ctrl_events_t events = 0;
  if (dif_toggle_to_bool(fatal)) {
    CHECK_DIF_OK(dif_sensor_ctrl_get_fatal_events(&sensor_ctrl, &events));
  } else {
    CHECK_DIF_OK(dif_sensor_ctrl_get_recov_events(&sensor_ctrl, &events));
  }
  return events;
}

/**
 *  Clear event trigger and recoverable status.
 */
static void clear_event(uint32_t idx, dif_toggle_t fatal) {
  CHECK_DIF_OK(dif_sensor_ctrl_set_ast_event_trigger(&sensor_ctrl, idx,
                                                     kDifToggleDisabled));
  if (!dif_toggle_to_bool(fatal)) {
    CHECK_DIF_OK(dif_sensor_ctrl_clear_recov_event(&sensor_ctrl, idx));
  }
}

/**
 *  Check alert cause registers are correctly set
 */
static void check_alert_state(dif_toggle_t fatal) {
  bool fatal_cause = false;
  bool recov_cause = false;

  CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
      &alert_handler, kTopEarlgreyAlertIdSensorCtrlFatalAlert, &fatal_cause));

  CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
      &alert_handler, kTopEarlgreyAlertIdSensorCtrlRecovAlert, &recov_cause));

  if (dif_toggle_to_bool(fatal)) {
    CHECK(fatal_cause & !recov_cause,
          "Fatal alert not correctly observed in alert handler");
  } else {
    CHECK(recov_cause & !fatal_cause,
          "Recov alert not correctly observed in alert handler");
  }

  CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
      &alert_handler, kTopEarlgreyAlertIdSensorCtrlRecovAlert));
  CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
      &alert_handler, kTopEarlgreyAlertIdSensorCtrlFatalAlert));
}

/**
 *  First configure fatality of the desired event.
 *  Then trigger the event from sensor_ctrl to ast.
 *  Next poll for setting of correct events inside sensor_ctrl status.
 *  When a recoverable event is triggerd, make sure only recoverable
 *  status is seen, likewise for fatal events.
 *  Finally, check for correct capture of cause in alert handler.
 */
static void test_event(uint32_t idx, dif_toggle_t fatal, bool set_event) {
  if (set_event) {
    // Configure event fatality
    CHECK_DIF_OK(dif_sensor_ctrl_set_alert_fatal(&sensor_ctrl, idx, fatal));

    // Trigger event
    CHECK_DIF_OK(dif_sensor_ctrl_set_ast_event_trigger(&sensor_ctrl, idx,
                                                       kDifToggleEnabled));
    // wait for events to set
    IBEX_SPIN_FOR(get_events(fatal) > 0, 1);

    // Check for the event in ast sensor_ctrl
    // if the event is not set, error
    CHECK(((get_events(fatal) >> idx) & 0x1) == 1,
          "Event %d not observed in AST", idx);

    // check the opposite fatality setting, should not be set
    CHECK(((get_events(!fatal) >> idx) & 0x1) == 0,
          "Event %d observed in AST when it should not be", idx);
  } else {
    // clear event trigger
    clear_event(idx, fatal);

    // check whether alert handler captured the event
    check_alert_state(fatal);
  }
}

void init_units(void) {
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &rv_plic));
  CHECK_DIF_OK(dif_sensor_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR), &sensor_ctrl));
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));
  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));
  CHECK_DIF_OK(dif_adc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR), &adc_ctrl));
}

/**
 *  configure adc module
 */
static void configure_adc_ctrl(const dif_adc_ctrl_t *adc_ctrl) {
  uint32_t wake_up_time_aon_cycles = 0;
  uint32_t power_up_time_aon_cycles = 0;

  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_from_us(
      kPowerUpTimeInUs, &power_up_time_aon_cycles));
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_from_us(
      kWakeUpTimeInUs, &wake_up_time_aon_cycles));
  CHECK_DIF_OK(dif_adc_ctrl_set_enabled(adc_ctrl, kDifToggleDisabled));
  CHECK_DIF_OK(dif_adc_ctrl_reset(adc_ctrl));
  CHECK_DIF_OK(dif_adc_ctrl_configure(
      adc_ctrl,
      (dif_adc_ctrl_config_t){
          .mode = kDifAdcCtrlLowPowerScanMode,
          .num_low_power_samples = kNumLowPowerSamples,
          .num_normal_power_samples = kNumNormalPowerSamples,
          .power_up_time_aon_cycles = (uint8_t)power_up_time_aon_cycles + 1,
          .wake_up_time_aon_cycles = wake_up_time_aon_cycles}));
}

static void en_plic_irqs(dif_rv_plic_t *plic) {
  top_earlgrey_plic_irq_id_t plic_irqs[] = {
      kTopEarlgreyPlicIrqIdAdcCtrlAonMatchDone};

  for (uint32_t i = 0; i < ARRAYSIZE(plic_irqs); ++i) {
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        plic, plic_irqs[i], kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));

    // Assign a default priority
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(plic, plic_irqs[i], 0x1));
  }

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

void adc_setup(bool first_adc_setup) {
  // Enable adc interrupts.
  CHECK_DIF_OK(dif_adc_ctrl_irq_set_enabled(&adc_ctrl, kDifAdcCtrlIrqMatchDone,
                                            kDifToggleEnabled));

  uint16_t channel0_filter0_max =
      ((uint16_t)(kChannel0MaxHighByte << 8)) | kChannel0MaxLowByte;
  uint16_t channel0_filter0_min =
      ((uint16_t)(kChannel0MinHighByte << 8)) | kChannel0MinLowByte;
  uint16_t channel1_filter0_max =
      ((uint16_t)(kChannel1MaxHighByte << 8)) | kChannel1MaxLowByte;
  uint16_t channel1_filter0_min =
      ((uint16_t)(kChannel1MinHighByte << 8)) | kChannel1MinLowByte;

  if (first_adc_setup) {
    // Setup ADC configuration.
    configure_adc_ctrl(&adc_ctrl);
  } else {
    CHECK_DIF_OK(dif_adc_ctrl_reset(&adc_ctrl));
  }

  en_plic_irqs(&plic);
  // Setup ADC filters. There is one filter for each channel.
  CHECK_DIF_OK(dif_adc_ctrl_configure_filter(
      &adc_ctrl, kDifAdcCtrlChannel0,
      (dif_adc_ctrl_filter_config_t){.filter = kDifAdcCtrlFilter0,
                                     .generate_irq_on_match = true,
                                     .generate_wakeup_on_match = true,
                                     .in_range = true,
                                     .max_voltage = channel0_filter0_max,
                                     .min_voltage = channel0_filter0_min},
      kDifToggleDisabled));
  CHECK_DIF_OK(dif_adc_ctrl_configure_filter(
      &adc_ctrl, kDifAdcCtrlChannel1,
      (dif_adc_ctrl_filter_config_t){.filter = kDifAdcCtrlFilter0,
                                     .generate_irq_on_match = true,
                                     .generate_wakeup_on_match = true,
                                     .in_range = true,
                                     .max_voltage = channel1_filter0_max,
                                     .min_voltage = channel1_filter0_min},
      kDifToggleDisabled));

  // enable filters.
  CHECK_DIF_OK(dif_adc_ctrl_filter_set_enabled(
      &adc_ctrl, kDifAdcCtrlChannel0, kDifAdcCtrlFilter0, kDifToggleEnabled));
  CHECK_DIF_OK(dif_adc_ctrl_filter_set_enabled(
      &adc_ctrl, kDifAdcCtrlChannel1, kDifAdcCtrlFilter0, kDifToggleEnabled));

  if (first_adc_setup) {
    CHECK_DIF_OK(dif_adc_ctrl_set_enabled(&adc_ctrl, kDifToggleEnabled));
  }
}

void entropy_config(dif_entropy_src_config_t entropy_src_config) {
  CHECK_DIF_OK(dif_entropy_src_set_enabled(&entropy_src, kDifToggleDisabled));

  const dif_entropy_src_fw_override_config_t fw_override_config = {
      .entropy_insert_enable = true,
      .buffer_threshold = kEntropyFifoBufferSize,
  };

  CHECK_DIF_OK(dif_entropy_src_fw_override_configure(
      &entropy_src, fw_override_config, kDifToggleEnabled));

  CHECK_DIF_OK(dif_entropy_src_configure(&entropy_src, entropy_src_config,
                                         kDifToggleEnabled));
}

void ast_enter_sleep_states_and_check_functionality(
    dif_pwrmgr_domain_config_t pwrmgr_config,
    dif_entropy_src_config_t entropy_src_config, uint32_t alert_idx) {
  bool deepsleep;
  uint32_t read_fifo_depth_val = 0;
  uint32_t unhealthy_fifos, errors, alerts;

  const dif_edn_t edn0 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};
  const dif_edn_t edn1 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR)};

  if ((pwrmgr_config & (~kDifPwrmgrDomainOptionUsbClockInActivePower)) == 0) {
    deepsleep = true;
  } else {
    deepsleep = false;
  }

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, kDifNoWakeup)) ==
      true) {
    entropy_config(entropy_src_config);

    // Verify that the FIFO depth is non-zero via SW - indicating the reception
    // of data over the AST RNG interface.
    IBEX_SPIN_FOR(read_fifo_depth(&entropy_src) > 0, 1000);

    // test recoverable event
    test_event(alert_idx, kDifToggleDisabled, kAlertSet);

    // Enable all the AON interrupts used in this test.
    rv_plic_testutils_irq_range_enable(
        &rv_plic, kTopEarlgreyPlicTargetIbex0,
        kTopEarlgreyPlicIrqIdAdcCtrlAonMatchDone,
        kTopEarlgreyPlicIrqIdAdcCtrlAonMatchDone);
    CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

    // Setup low power.
    CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));

    if (!deepsleep) {
      // read fifo depth before enter sleep mode
      read_fifo_depth_val = read_fifo_depth(&entropy_src);
    }

    // Configure ADC
    adc_setup(first_adc_setup);

    // set sleep mode
    CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
        &pwrmgr, kDifPwrmgrWakeupRequestSourceTwo, pwrmgr_config));

    // Enter low power mode.
    LOG_INFO("Issued WFI to enter sleep.");

    wait_for_interrupt();

    // Interrupt should have been serviced.
    CHECK(interrupt_serviced);

    interrupt_serviced = false;

  } else if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr, kDifPwrmgrWakeupRequestSourceTwo)) == true) {
    if (deepsleep) {
      if (read_fifo_depth(&entropy_src) != 0)
        LOG_ERROR("read_fifo_depth after reset=%0d should be 0",
                  read_fifo_depth(&entropy_src));

      first_adc_setup = false;
      // Configure ADC after deep sleep
      adc_setup(first_adc_setup);
    }

    entropy_config(entropy_src_config);

    IBEX_SPIN_FOR(read_fifo_depth(&entropy_src) > 0, 1000);
  }

  if (!deepsleep) {
    if (read_fifo_depth_val >= read_fifo_depth(&entropy_src))
      LOG_ERROR(
          "read_fifo_depth after exit from idle=%0d should be equal/greater "
          "than previous read value (%0d)",
          read_fifo_depth(&entropy_src), read_fifo_depth_val);
  }

  IBEX_SPIN_FOR(read_fifo_depth(&entropy_src) > 0, 1000);

  test_event(alert_idx, kDifToggleDisabled, kAlertClear);

  CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));

  // test event after exit from low power
  test_event(alert_idx, kDifToggleDisabled, kAlertSet);
  test_event(alert_idx, kDifToggleDisabled, kAlertClear);

  // verify there are no any edn alerts/errors
  CHECK_DIF_OK(dif_edn_get_errors(&edn0, &unhealthy_fifos, &errors));
  CHECK_DIF_OK(dif_edn_get_recoverable_alerts(&edn0, &alerts));
  if (unhealthy_fifos != 0 || errors != 0 || alerts != 0)
    LOG_ERROR("edn0: error=0x%x, unhealthy_fifos=0x%x, alerts=0x%x", errors,
              unhealthy_fifos, alerts);

  CHECK_DIF_OK(dif_edn_get_errors(&edn1, &unhealthy_fifos, &errors));
  CHECK_DIF_OK(dif_edn_get_recoverable_alerts(&edn1, &alerts));
  if (unhealthy_fifos != 0 || errors != 0 || alerts != 0)
    LOG_ERROR("edn1: error=0x%x, unhealthy_fifos=0x%x, alerts=0x%x", errors,
              unhealthy_fifos, alerts);
}

/**
 *  set edn auto mode
 */
void set_edn_auto_mode(void) {
  const dif_edn_t edn0 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};
  const dif_edn_t edn1 = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR)};

  CHECK_DIF_OK(dif_edn_stop(&edn0));
  CHECK_DIF_OK(dif_edn_stop(&edn1));

  // Re-enable EDN0 in auto mode.
  const dif_edn_auto_params_t edn0_params = {
      // EDN0 provides lower-quality entropy.  Let one generate command return 8
      // blocks, and reseed every 32 generates.
      .instantiate_cmd =
          {
              .cmd = 0x00000001 |  // Reseed from entropy source only.
                     kMultiBitBool4False << 8,
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .reseed_cmd =
          {
              .cmd = 0x00008002 |  // One generate returns 8 blocks, reseed
                                   // from entropy source only.
                     kMultiBitBool4False << 8,
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .generate_cmd =
          {
              .cmd = 0x00008003,  // One generate returns 8 blocks.
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .reseed_interval = 32,  // Reseed every 32 generates.
  };
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn0, edn0_params));

  // Re-enable EDN1 in auto mode.
  const dif_edn_auto_params_t edn1_params = {
      // EDN1 provides highest-quality entropy.  Let one generate command
      // return 1 block, and reseed after every generate.
      .instantiate_cmd =
          {
              .cmd = 0x00000001 |  // Reseed from entropy source only.
                     kMultiBitBool4False << 8,
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .reseed_cmd =
          {
              .cmd = 0x00001002 |  // One generate returns 1 block, reseed
                                   // from entropy source only.
                     kMultiBitBool4False << 8,
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .generate_cmd =
          {
              .cmd = 0x00001003,  // One generate returns 1 block.
              .seed_material =
                  {
                      .len = 0,
                  },
          },
      .reseed_interval = 4,  // Reseed after every 4 generates.
  };
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn1, edn1_params));
}

void ottf_external_isr(void) {
  plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                             .hart_id = kTopEarlgreyPlicTargetIbex0};

  adc_ctrl_isr_ctx_t adc_ctrl_ctx = {
      .adc_ctrl = &adc_ctrl,
      .plic_adc_ctrl_start_irq_id = kTopEarlgreyPlicIrqIdAdcCtrlAonMatchDone,
      .expected_irq = 0,
      .is_only_irq = true};

  top_earlgrey_plic_peripheral_t peripheral;
  dif_adc_ctrl_irq_t adc_ctrl_irq;
  isr_testutils_adc_ctrl_isr(plic_ctx, adc_ctrl_ctx, &peripheral,
                             &adc_ctrl_irq);

  CHECK(peripheral == kTopEarlgreyPlicPeripheralAdcCtrlAon);
  CHECK(adc_ctrl_irq == kDifAdcCtrlIrqMatchDone);
  interrupt_serviced = true;
}

bool test_main(void) {
  dif_pwrmgr_domain_config_t pwrmgr_config;

  const dif_entropy_src_config_t entropy_src_config = {
      .fips_enable = true,
      // Route the entropy data received from RNG to the FIFO.
      .route_to_firmware = true,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .health_test_threshold_scope = false,
      .health_test_window_size = 0x0200,
      .alert_threshold = 2,
  };

  init_units();

  set_edn_auto_mode();
  CHECK_DIF_OK(dif_clkmgr_jitter_set_enabled(&clkmgr, kDifToggleEnabled));

  // Enable both recoverable and fatal alerts
  CHECK_DIF_OK(dif_alert_handler_configure_alert(
      &alert_handler, kTopEarlgreyAlertIdSensorCtrlRecovAlert,
      kDifAlertHandlerClassA, kDifToggleEnabled, kDifToggleEnabled));
  CHECK_DIF_OK(dif_alert_handler_configure_alert(
      &alert_handler, kTopEarlgreyAlertIdSensorCtrlFatalAlert,
      kDifAlertHandlerClassA, kDifToggleEnabled, kDifToggleEnabled));

  LOG_INFO("1 test alert/rng after Deep sleep 1");
  pwrmgr_config = kDifPwrmgrDomainOptionUsbClockInActivePower;
  ast_enter_sleep_states_and_check_functionality(
      pwrmgr_config, entropy_src_config, kAlertVal7);

  LOG_INFO("2 test alert/rng after regular sleep (usb clk enabled)");
  LOG_INFO("force new adc conv set");
  pwrmgr_config = kDifPwrmgrDomainOptionUsbClockInActivePower |
                  kDifPwrmgrDomainOptionUsbClockInLowPower |
                  kDifPwrmgrDomainOptionMainPowerInLowPower;
  ast_enter_sleep_states_and_check_functionality(
      pwrmgr_config, entropy_src_config, kAlertVal8);

  LOG_INFO("3 test alert/rng after regular sleep (all clk disabled in lp)");
  LOG_INFO("force new adc conv set");
  pwrmgr_config = kDifPwrmgrDomainOptionMainPowerInLowPower |
                  kDifPwrmgrDomainOptionUsbClockInActivePower;
  ast_enter_sleep_states_and_check_functionality(
      pwrmgr_config, entropy_src_config, kAlertVal7);

  LOG_INFO("c code is finished");

  return true;
}
