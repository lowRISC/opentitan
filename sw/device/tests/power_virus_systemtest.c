// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
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
static dif_aes_t aes;
static dif_hmac_t hmac;
static dif_kmac_t kmac;
static dif_i2c_t i2c_0;
static dif_i2c_t i2c_1;
static dif_i2c_t i2c_2;
static dif_spi_device_handle_t spi_device;
static dif_uart_t uart_1;
static dif_uart_t uart_2;
static dif_uart_t uart_3;

/**
 * Test configuration parameters.
 */
enum {
  /**
   * Test timeout parameter.
   */
  kTestTimeoutMicros = 100000,
  /**
   * ADC controller parameters.
   */
  kAdcCtrlPowerUpTimeAonCycles = 15,  // maximum power-up time
  /**
   * EDN parameters.
   */
  kEdn0ReseedInterval = 32,
  kEdn1ReseedInterval = 4,
  /**
   * KMAC parameters.
   */
  kKmacEntropyReseedInterval = 1,
  kKmacEntropyHashThreshold = 1,  // KMAC operations between entropy requests
  kKmacEntropyWaitTimer = 0xffff,
  kKmacEntropyPrescaler = 0x3ff,
  kKmacDigestLength = 16,
  /**
   * I2C parameters.
   */
  kI2cSdaRiseFallTimeNs = 10,
  kI2cSclPeriodNs = 1000,
  kI2cDeviceMask = 0x7f,
  kI2c0DeviceAddress0 = 0x11,
  kI2c0DeviceAddress1 = 0x22,
  kI2c1DeviceAddress0 = 0x33,
  kI2c1DeviceAddress1 = 0x44,
  kI2c2DeviceAddress0 = 0x55,
  kI2c2DeviceAddress1 = 0x66,
};

/**
 * The mask share, used to mask kAesKey.
 */
static const uint8_t kAesKeyShare1[] = {
    0x0f, 0x1f, 0x2f, 0x3f, 0x4f, 0x5f, 0x6f, 0x7f, 0x8f, 0x9f, 0xaf,
    0xbf, 0xcf, 0xdf, 0xef, 0xff, 0x0a, 0x1a, 0x2a, 0x3a, 0x4a, 0x5a,
    0x6a, 0x7a, 0x8a, 0x9a, 0xaa, 0xba, 0xca, 0xda, 0xea, 0xfa,
};

static const uint8_t kHmacKey[] = {
    0x0f, 0x1f, 0x2f, 0x3f, 0x4f, 0x5f, 0x6f, 0x7f,
};

static const dif_kmac_key_t kKmacKey = {
    .share0 = {0x43424140, 0x47464544, 0x4b4a4948, 0x4f4e4f4c, 0x53525150,
               0x57565554, 0x5b5a5958, 0x5f5e5d5c},
    .share1 = {0},
    .length = kDifKmacKeyLen256,
};

/**
 * Initializes all DIF handles for each peripheral used in this test.
 */
static void init_peripheral_handles() {
  CHECK_DIF_OK(dif_adc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR), &adc_ctrl));
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn_0));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn_1));
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  CHECK_DIF_OK(
      dif_hmac_init(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac));
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  // UART 0 is already configured (and used) by the OTTF.
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART1_BASE_ADDR), &uart_1));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART2_BASE_ADDR), &uart_2));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART3_BASE_ADDR), &uart_3));
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR), &i2c_0));
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C1_BASE_ADDR), &i2c_1));
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C2_BASE_ADDR), &i2c_2));
  CHECK_DIF_OK(dif_spi_device_init_handle(
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spi_device));
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

static void configure_aes() {
  // Prepare and load AES key shares.
  uint8_t aes_key_share0[sizeof(kAesModesKey256)];
  for (size_t i = 0; i < sizeof(kAesModesKey256); ++i) {
    aes_key_share0[i] = kAesModesKey256[i] ^ kAesKeyShare1[i];
  }
  dif_aes_key_share_t aes_key;
  memcpy(aes_key.share0, aes_key_share0, sizeof(aes_key.share0));
  memcpy(aes_key.share1, kAesKeyShare1, sizeof(aes_key.share1));

  // Prepare and load AES IV.
  dif_aes_iv_t aes_iv;
  memcpy(aes_iv.iv, kAesModesIvCbc, sizeof(aes_iv.iv));

  // Setup AES in automatic, 256-bit SW provided key, CBC encryption mode. We
  // need to be in automatic mode to mamimize throughput. Additionally, we want
  // to keep the entropy complex busing by constantly reseeding PRNGs.
  dif_aes_transaction_t aes_transaction_cfg = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeCbc,
      .key_len = kDifAesKey256,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  // Start the AES operation. Since we are in auto-mode, the encryption will not
  // start until plain text data is loaded into the appropriate CSRs.
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                kTestTimeoutMicros);
  CHECK_DIF_OK(dif_aes_start(&aes, &aes_transaction_cfg, &aes_key, &aes_iv));
}

static void configure_hmac() {
  dif_hmac_transaction_t hmac_transaction_cfg = {
      .digest_endianness = kDifHmacEndiannessLittle,
      .message_endianness = kDifHmacEndiannessLittle,
  };
  CHECK_DIF_OK(dif_hmac_mode_hmac_start(&hmac, kHmacKey, hmac_transaction_cfg));
}

static void configure_kmac() {
  dif_kmac_config_t kmac_cfg = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeEdn,
      .entropy_fast_process = kDifToggleDisabled,
      .entropy_hash_threshold = kKmacEntropyHashThreshold,
      .entropy_wait_timer = kKmacEntropyWaitTimer,
      .entropy_prescaler = kKmacEntropyPrescaler,
      .message_big_endian = false,
      .output_big_endian = false,
      .sideload = false,
      .msg_mask = false,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, kmac_cfg));

  dif_kmac_customization_string_t kmac_customization_string;
  CHECK_DIF_OK(dif_kmac_customization_string_init("Power Virus Test", 16,
                                                  &kmac_customization_string));

  dif_kmac_operation_state_t kmac_operation_state;
  CHECK_DIF_OK(dif_kmac_mode_kmac_start(
      &kmac, &kmac_operation_state, kDifKmacModeKmacLen256, kKmacDigestLength,
      &kKmacKey, &kmac_customization_string));
}

static void configure_uart(dif_uart_t *uart) {
  CHECK_DIF_OK(
      dif_uart_configure(uart, (dif_uart_config_t){
                                   .baudrate = kUartBaudrate,
                                   .clk_freq_hz = kClockFreqPeripheralHz,
                                   .parity_enable = kDifToggleEnabled,
                                   .parity = kDifUartParityEven,
                               }));
  CHECK_DIF_OK(
      dif_uart_loopback_set(uart, kDifUartLoopbackSystem, kDifToggleEnabled));
}

static void configure_i2c(dif_i2c_t *i2c, uint8_t device_addr_0,
                          uint8_t device_addr_1) {
  uint32_t peripheral_clock_period_ns =
      udiv64_slow(1000000000, kClockFreqPeripheralHz, NULL);
  dif_i2c_config_t config;

  CHECK_DIF_OK(dif_i2c_compute_timing(
      (dif_i2c_timing_config_t){
          .lowest_target_device_speed = kDifI2cSpeedFastPlus,
          .clock_period_nanos = peripheral_clock_period_ns,
          .sda_rise_nanos = kI2cSdaRiseFallTimeNs,
          .sda_fall_nanos = kI2cSdaRiseFallTimeNs,
          .scl_period_nanos = kI2cSclPeriodNs},
      &config));
  CHECK_DIF_OK(dif_i2c_configure(i2c, config));
  dif_i2c_id_t id_0 = {.mask = kI2cDeviceMask, .address = device_addr_0};
  dif_i2c_id_t id_1 = {.mask = kI2cDeviceMask, .address = device_addr_1};
  CHECK_DIF_OK(dif_i2c_set_device_id(i2c, &id_0, &id_1));
  CHECK_DIF_OK(dif_i2c_line_loopback_set_enabled(i2c, kDifToggleEnabled));
}

bool test_main(void) {
  init_peripheral_handles();
  configure_gpio_indicator_pin();
  configure_adc_ctrl_to_continuously_sample();
  configure_entropy_complex();
  configure_aes();
  configure_hmac();
  configure_kmac();
  configure_uart(&uart_1);
  configure_uart(&uart_2);
  configure_uart(&uart_3);
  configure_i2c(&i2c_0, kI2c0DeviceAddress0, kI2c0DeviceAddress1);
  configure_i2c(&i2c_1, kI2c1DeviceAddress0, kI2c1DeviceAddress1);
  configure_i2c(&i2c_2, kI2c2DeviceAddress0, kI2c2DeviceAddress1);
  spi_device_testutils_configure_passthrough(&spi_device, /*filters=*/0,
                                             /*upload_write_commands=*/false);
  return true;
}
