// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_macros.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "adc_ctrl_regs.h"     // Generated.
#include "entropy_src_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_concurrency = true,
                        .can_clobber_uart = false, );

/**
 * Peripheral DIF Handles.
 */
static dif_pinmux_t pinmux;
static dif_gpio_t gpio;
static dif_adc_ctrl_t adc_ctrl;
static dif_entropy_src_t entropy_src;
static dif_csrng_t csrng;
static dif_edn_t edn_0;
static dif_edn_t edn_1;

/**
 * Test configuration parameters.
 */
enum {
  /**
   * ADC controller parameters.
   */
  kAdcCtrlPowerUpTimeAonCycles = 15,  // maximum power-up time
  /**
   * EDN parameters.
   */
  kEdn0ReseedInterval = 32,
  kEdn1ReseedInterval = 4,
};

/**
 * Initializes all DIF handles for each peripheral used in this test.
 */
static void init_peripheral_handles() {
  CHECK_DIF_OK(dif_adc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR), &adc_ctrl));
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn_0));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn_1));
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
}

/**
 * Configures GPIO 0 (mapped to pad IOA2) as an indicator pin, to go high during
 * the power state(s) of interest.
 */
static void configure_gpio_indicator_pin() {
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoa2,
                                        kTopEarlgreyPinmuxOutselGpioGpio0));
  CHECK_DIF_OK(
      dif_gpio_output_set_enabled(&gpio, /*pin=*/0, kDifToggleEnabled));
}

/**
 * Configures adc_ctrl to continuously sample data (applying all filters across
 * both channels) in normal power mode, which is the most power intensive
 * sampling mode.
 */
static void configure_adc_ctrl_to_continuously_sample() {
  CHECK_DIF_OK(dif_adc_ctrl_configure(
      &adc_ctrl,
      (dif_adc_ctrl_config_t){
          .mode = kDifAdcCtrlNormalPowerScanMode,
          .power_up_time_aon_cycles = kAdcCtrlPowerUpTimeAonCycles,
          // Below configurations are unused, so set them to their reset values.
          .wake_up_time_aon_cycles = ADC_CTRL_ADC_PD_CTL_WAKEUP_TIME_MASK,
          .num_low_power_samples = ADC_CTRL_ADC_LP_SAMPLE_CTL_REG_RESVAL,
          .num_normal_power_samples = ADC_CTRL_ADC_SAMPLE_CTL_REG_RESVAL,
      }));
  for (size_t filter = 0; filter < ADC_CTRL_PARAM_NUM_ADC_FILTER; ++filter) {
    for (size_t channel = 0; channel < ADC_CTRL_PARAM_NUM_ADC_CHANNEL;
         ++channel) {
      CHECK_DIF_OK(dif_adc_ctrl_configure_filter(
          &adc_ctrl, (dif_adc_ctrl_channel_t)channel,
          (dif_adc_ctrl_filter_config_t){
              .filter = (dif_adc_ctrl_filter_t)filter,
              // Set max range.
              .min_voltage = 0,
              .max_voltage = ADC_CTRL_ADC_CHN0_FILTER_CTL_0_MAX_V_0_MASK,
              .in_range = true,
              .generate_wakeup_on_match = false,
              .generate_irq_on_match = false,
          },
          kDifToggleEnabled));
    }
  }
}

static void configure_entropy_complex() {
  // The (test) ROM enables the entropy complex, and to reconfigure it requires
  // temporarily disabling it.
  entropy_testutils_stop_all();

  CHECK_DIF_OK(dif_entropy_src_configure(
      &entropy_src,
      (dif_entropy_src_config_t){
          .fips_enable = true,
          .route_to_firmware = true,
          .bypass_conditioner = false,
          .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
          .health_test_threshold_scope = false,
          .health_test_window_size = 0x200,
          .alert_threshold = UINT16_MAX},
      kDifToggleDisabled));
  CHECK_DIF_OK(dif_entropy_src_health_test_configure(
      &entropy_src, (dif_entropy_src_health_test_config_t){
                        .test_type = kDifEntropySrcTestRepetitionCount,
                        .high_threshold = UINT16_MAX,
                        .low_threshold = 0}));
  CHECK_DIF_OK(dif_entropy_src_health_test_configure(
      &entropy_src, (dif_entropy_src_health_test_config_t){
                        .test_type = kDifEntropySrcTestRepetitionCountSymbol,
                        .high_threshold = UINT16_MAX,
                        .low_threshold = 0}));
  CHECK_DIF_OK(dif_entropy_src_health_test_configure(
      &entropy_src, (dif_entropy_src_health_test_config_t){
                        .test_type = kDifEntropySrcTestAdaptiveProportion,
                        .high_threshold = UINT16_MAX,
                        .low_threshold = 0}));
  CHECK_DIF_OK(dif_entropy_src_health_test_configure(
      &entropy_src, (dif_entropy_src_health_test_config_t){
                        .test_type = kDifEntropySrcTestBucket,
                        .high_threshold = UINT16_MAX,
                        .low_threshold = 0}));
  CHECK_DIF_OK(dif_entropy_src_health_test_configure(
      &entropy_src, (dif_entropy_src_health_test_config_t){
                        .test_type = kDifEntropySrcTestMarkov,
                        .high_threshold = UINT16_MAX,
                        .low_threshold = 0}));
  CHECK_DIF_OK(dif_entropy_src_fw_override_configure(
      &entropy_src,
      (dif_entropy_src_fw_override_config_t){
          .entropy_insert_enable = false,
          .buffer_threshold = ENTROPY_SRC_OBSERVE_FIFO_THRESH_REG_RESVAL,
      },
      kDifToggleDisabled));

  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  dif_edn_seed_material_t edn_empty_seed = {
      .len = 0,
  };
  dif_edn_seed_material_t edn_384_bit_seed = {
      .len = 12,
      .data = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12},
  };
  dif_edn_auto_params_t edn_auto_params = {
      // EDN0 provides lower-quality entropy. Let one generate command return
      // eight 128-bit blocks, and reseed every 32 generates.
      .instantiate_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdInstantiate,
                                            kDifCsrngEntropySrcToggleEnable,
                                            /*cmd_len=*/12,
                                            /*generate_len=*/0),
              .seed_material = edn_384_bit_seed,
          },
      .reseed_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdReseed,
                                            kDifCsrngEntropySrcToggleEnable,
                                            /*cmd_len=*/12, /*generate_len=*/0),
              .seed_material = edn_384_bit_seed,
          },
      .generate_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdGenerate,
                                            kDifCsrngEntropySrcToggleEnable,
                                            /*cmd_len=*/0,
                                            /*generate_len=*/8),
              .seed_material = edn_empty_seed,
          },
      .reseed_interval = 0,
  };
  edn_auto_params.reseed_interval = kEdn0ReseedInterval;
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn_0, edn_auto_params));
  edn_auto_params.reseed_interval = kEdn1ReseedInterval;
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn_1, edn_auto_params));
  CHECK_DIF_OK(dif_edn_configure(&edn_0));
  CHECK_DIF_OK(dif_edn_configure(&edn_1));
}

bool test_main(void) {
  init_peripheral_handles();
  configure_gpio_indicator_pin();
  configure_adc_ctrl_to_continuously_sample();
  configure_entropy_complex();
  return true;
}
