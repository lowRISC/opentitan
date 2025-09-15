// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// clang-format off

//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_verbano/data/top_verbano.hjson \
//                -o hw/top_verbano/
#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/autogen/dif_adc_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_aes_autogen.h"
#include "sw/device/lib/dif/autogen/dif_alert_handler_autogen.h"
#include "sw/device/lib/dif/autogen/dif_aon_timer_autogen.h"
#include "sw/device/lib/dif/autogen/dif_clkmgr_autogen.h"
#include "sw/device/lib/dif/autogen/dif_csrng_autogen.h"
#include "sw/device/lib/dif/autogen/dif_edn_autogen.h"
#include "sw/device/lib/dif/autogen/dif_entropy_src_autogen.h"
#include "sw/device/lib/dif/autogen/dif_flash_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_gpio_autogen.h"
#include "sw/device/lib/dif/autogen/dif_hmac_autogen.h"
#include "sw/device/lib/dif/autogen/dif_i2c_autogen.h"
#include "sw/device/lib/dif/autogen/dif_keymgr_autogen.h"
#include "sw/device/lib/dif/autogen/dif_kmac_autogen.h"
#include "sw/device/lib/dif/autogen/dif_lc_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_otbn_autogen.h"
#include "sw/device/lib/dif/autogen/dif_otp_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_pattgen_autogen.h"
#include "sw/device/lib/dif/autogen/dif_pinmux_autogen.h"
#include "sw/device/lib/dif/autogen/dif_pwm_autogen.h"
#include "sw/device/lib/dif/autogen/dif_pwrmgr_autogen.h"
#include "sw/device/lib/dif/autogen/dif_rom_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_rstmgr_autogen.h"
#include "sw/device/lib/dif/autogen/dif_rv_core_ibex_autogen.h"
#include "sw/device/lib/dif/autogen/dif_rv_plic_autogen.h"
#include "sw/device/lib/dif/autogen/dif_rv_timer_autogen.h"
#include "sw/device/lib/dif/autogen/dif_sensor_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_spi_device_autogen.h"
#include "sw/device/lib/dif/autogen/dif_spi_host_autogen.h"
#include "sw/device/lib/dif/autogen/dif_sram_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_sysrst_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_uart_autogen.h"
#include "sw/device/lib/dif/autogen/dif_usbdev_autogen.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

#include "alert_handler_regs.h"  // Generated.
#include "hw/top_verbano/sw/autogen/top_verbano.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_alert_handler_t alert_handler;
static dif_adc_ctrl_t adc_ctrl_aon;
static dif_aes_t aes;
static dif_aon_timer_t aon_timer_aon;
static dif_clkmgr_t clkmgr_aon;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_entropy_src_t entropy_src;
static dif_flash_ctrl_t flash_ctrl;
static dif_gpio_t gpio;
static dif_hmac_t hmac;
static dif_i2c_t i2c0;
static dif_i2c_t i2c1;
static dif_i2c_t i2c2;
static dif_keymgr_t keymgr;
static dif_kmac_t kmac;
static dif_lc_ctrl_t lc_ctrl;
static dif_otbn_t otbn;
static dif_otp_ctrl_t otp_ctrl;
static dif_pattgen_t pattgen;
static dif_pinmux_t pinmux_aon;
static dif_pwm_t pwm_aon;
static dif_pwrmgr_t pwrmgr_aon;
static dif_rom_ctrl_t rom_ctrl;
static dif_rstmgr_t rstmgr_aon;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_rv_plic_t rv_plic;
static dif_rv_timer_t rv_timer;
static dif_sensor_ctrl_t sensor_ctrl_aon;
static dif_spi_device_t spi_device;
static dif_spi_host_t spi_host0;
static dif_spi_host_t spi_host1;
static dif_sram_ctrl_t sram_ctrl_main;
static dif_sram_ctrl_t sram_ctrl_ret_aon;
static dif_sysrst_ctrl_t sysrst_ctrl_aon;
static dif_uart_t uart0;
static dif_uart_t uart1;
static dif_uart_t uart2;
static dif_uart_t uart3;
static dif_usbdev_t usbdev;

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  mmio_region_t base_addr;
  base_addr = mmio_region_from_addr(TOP_VERBANO_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, &alert_handler));

  base_addr = mmio_region_from_addr(TOP_VERBANO_ADC_CTRL_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_adc_ctrl_init(base_addr, &adc_ctrl_aon));

  base_addr = mmio_region_from_addr(TOP_VERBANO_AES_BASE_ADDR);
  CHECK_DIF_OK(dif_aes_init(base_addr, &aes));

  base_addr = mmio_region_from_addr(TOP_VERBANO_AON_TIMER_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_aon_timer_init(base_addr, &aon_timer_aon));

  base_addr = mmio_region_from_addr(TOP_VERBANO_CLKMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_clkmgr_init(base_addr, &clkmgr_aon));

  base_addr = mmio_region_from_addr(TOP_VERBANO_CSRNG_BASE_ADDR);
  CHECK_DIF_OK(dif_csrng_init(base_addr, &csrng));

  base_addr = mmio_region_from_addr(TOP_VERBANO_EDN0_BASE_ADDR);
  CHECK_DIF_OK(dif_edn_init(base_addr, &edn0));

  base_addr = mmio_region_from_addr(TOP_VERBANO_EDN1_BASE_ADDR);
  CHECK_DIF_OK(dif_edn_init(base_addr, &edn1));

  base_addr = mmio_region_from_addr(TOP_VERBANO_ENTROPY_SRC_BASE_ADDR);
  CHECK_DIF_OK(dif_entropy_src_init(base_addr, &entropy_src));

  base_addr = mmio_region_from_addr(TOP_VERBANO_FLASH_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_flash_ctrl_init(base_addr, &flash_ctrl));

  base_addr = mmio_region_from_addr(TOP_VERBANO_GPIO_BASE_ADDR);
  CHECK_DIF_OK(dif_gpio_init(base_addr, &gpio));

  base_addr = mmio_region_from_addr(TOP_VERBANO_HMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_hmac_init(base_addr, &hmac));

  base_addr = mmio_region_from_addr(TOP_VERBANO_I2C0_BASE_ADDR);
  CHECK_DIF_OK(dif_i2c_init(base_addr, &i2c0));

  base_addr = mmio_region_from_addr(TOP_VERBANO_I2C1_BASE_ADDR);
  CHECK_DIF_OK(dif_i2c_init(base_addr, &i2c1));

  base_addr = mmio_region_from_addr(TOP_VERBANO_I2C2_BASE_ADDR);
  CHECK_DIF_OK(dif_i2c_init(base_addr, &i2c2));

  base_addr = mmio_region_from_addr(TOP_VERBANO_KEYMGR_BASE_ADDR);
  CHECK_DIF_OK(dif_keymgr_init(base_addr, &keymgr));

  base_addr = mmio_region_from_addr(TOP_VERBANO_KMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_kmac_init(base_addr, &kmac));

  base_addr = mmio_region_from_addr(TOP_VERBANO_LC_CTRL_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_lc_ctrl_init(base_addr, &lc_ctrl));

  base_addr = mmio_region_from_addr(TOP_VERBANO_OTBN_BASE_ADDR);
  CHECK_DIF_OK(dif_otbn_init(base_addr, &otbn));

  base_addr = mmio_region_from_addr(TOP_VERBANO_OTP_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_otp_ctrl_init(base_addr, &otp_ctrl));

  base_addr = mmio_region_from_addr(TOP_VERBANO_PATTGEN_BASE_ADDR);
  CHECK_DIF_OK(dif_pattgen_init(base_addr, &pattgen));

  base_addr = mmio_region_from_addr(TOP_VERBANO_PINMUX_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pinmux_init(base_addr, &pinmux_aon));

  base_addr = mmio_region_from_addr(TOP_VERBANO_PWM_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwm_init(base_addr, &pwm_aon));

  base_addr = mmio_region_from_addr(TOP_VERBANO_PWRMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwrmgr_init(base_addr, &pwrmgr_aon));

  base_addr = mmio_region_from_addr(TOP_VERBANO_ROM_CTRL_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_rom_ctrl_init(base_addr, &rom_ctrl));

  base_addr = mmio_region_from_addr(TOP_VERBANO_RSTMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_rstmgr_init(base_addr, &rstmgr_aon));

  base_addr = mmio_region_from_addr(TOP_VERBANO_RV_CORE_IBEX_CFG_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_core_ibex_init(base_addr, &rv_core_ibex));

  base_addr = mmio_region_from_addr(TOP_VERBANO_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &rv_plic));

  base_addr = mmio_region_from_addr(TOP_VERBANO_RV_TIMER_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_timer_init(base_addr, &rv_timer));

  base_addr = mmio_region_from_addr(TOP_VERBANO_SENSOR_CTRL_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_sensor_ctrl_init(base_addr, &sensor_ctrl_aon));

  base_addr = mmio_region_from_addr(TOP_VERBANO_SPI_DEVICE_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_device_init(base_addr, &spi_device));

  base_addr = mmio_region_from_addr(TOP_VERBANO_SPI_HOST0_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_host_init(base_addr, &spi_host0));

  base_addr = mmio_region_from_addr(TOP_VERBANO_SPI_HOST1_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_host_init(base_addr, &spi_host1));

  base_addr = mmio_region_from_addr(TOP_VERBANO_SRAM_CTRL_MAIN_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_sram_ctrl_init(base_addr, &sram_ctrl_main));

  base_addr = mmio_region_from_addr(TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_sram_ctrl_init(base_addr, &sram_ctrl_ret_aon));

  base_addr = mmio_region_from_addr(TOP_VERBANO_SYSRST_CTRL_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_sysrst_ctrl_init(base_addr, &sysrst_ctrl_aon));

  base_addr = mmio_region_from_addr(TOP_VERBANO_UART0_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart0));

  base_addr = mmio_region_from_addr(TOP_VERBANO_UART1_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart1));

  base_addr = mmio_region_from_addr(TOP_VERBANO_UART2_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart2));

  base_addr = mmio_region_from_addr(TOP_VERBANO_UART3_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart3));

  base_addr = mmio_region_from_addr(TOP_VERBANO_USBDEV_BASE_ADDR);
  CHECK_DIF_OK(dif_usbdev_init(base_addr, &usbdev));

}

/**
 * Configure the alert handler to escalate on alerts upto phase 1 (i.e. wipe
 * secret) but not trigger reset. Then CPU can check if alert_handler triggers the correct
 * alert_cause register.
 */
static void alert_handler_config(void) {
  dif_alert_handler_alert_t alerts[ALERT_HANDLER_PARAM_N_ALERTS];
  dif_alert_handler_class_t alert_classes[ALERT_HANDLER_PARAM_N_ALERTS];

  // Enable all incoming alerts and configure them to classa.
  // This alert should never fire because we do not expect any incoming alerts.
  for (dif_alert_handler_alert_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    alerts[i] = i;
    alert_classes[i] = kDifAlertHandlerClassA;
  }

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = 2000}};

  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = 10000,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  dif_alert_handler_class_config_t class_configs[] = {class_config,
                                                      class_config};

  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassA,
                                         kDifAlertHandlerClassB};
  dif_alert_handler_config_t config = {
      .alerts = alerts,
      .alert_classes = alert_classes,
      .alerts_len = ARRAYSIZE(alerts),
      .classes = classes,
      .class_configs = class_configs,
      .classes_len = ARRAYSIZE(class_configs),
      .ping_timeout = 1000,
  };

 CHECK_STATUS_OK(alert_handler_testutils_configure_all(&alert_handler, config,
                                        kDifToggleEnabled));
}

// Trigger alert for each module by writing one to `alert_test` register.
// Then check alert_handler's alert_cause register to make sure the correct alert reaches
// alert_handler.
static void trigger_alert_test(void) {
  bool is_cause;
  dif_alert_handler_alert_t exp_alert;

  // Write adc_ctrl's alert_test reg and check alert_cause.
  for (dif_adc_ctrl_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_adc_ctrl_alert_force(&adc_ctrl_aon, kDifAdcCtrlAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdAdcCtrlAonFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write aes's alert_test reg and check alert_cause.
  for (dif_aes_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_aes_alert_force(&aes, kDifAesAlertRecovCtrlUpdateErr + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdAesRecovCtrlUpdateErr + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write aon_timer's alert_test reg and check alert_cause.
  for (dif_aon_timer_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_aon_timer_alert_force(&aon_timer_aon, kDifAonTimerAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdAonTimerAonFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write clkmgr's alert_test reg and check alert_cause.
  for (dif_clkmgr_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_clkmgr_alert_force(&clkmgr_aon, kDifClkmgrAlertRecovFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdClkmgrAonRecovFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write csrng's alert_test reg and check alert_cause.
  for (dif_csrng_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_csrng_alert_force(&csrng, kDifCsrngAlertRecovAlert + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdCsrngRecovAlert + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write edn's alert_test reg and check alert_cause.
  for (dif_edn_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_edn_alert_force(&edn0, kDifEdnAlertRecovAlert + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdEdn0RecovAlert + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write edn's alert_test reg and check alert_cause.
  for (dif_edn_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_edn_alert_force(&edn1, kDifEdnAlertRecovAlert + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdEdn1RecovAlert + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write entropy_src's alert_test reg and check alert_cause.
  for (dif_entropy_src_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_entropy_src_alert_force(&entropy_src, kDifEntropySrcAlertRecovAlert + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdEntropySrcRecovAlert + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write flash_ctrl's alert_test reg and check alert_cause.
  for (dif_flash_ctrl_alert_t i = 0; i < 5; ++i) {
    CHECK_DIF_OK(dif_flash_ctrl_alert_force(&flash_ctrl, kDifFlashCtrlAlertRecovErr + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdFlashCtrlRecovErr + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write gpio's alert_test reg and check alert_cause.
  for (dif_gpio_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_gpio_alert_force(&gpio, kDifGpioAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdGpioFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write hmac's alert_test reg and check alert_cause.
  for (dif_hmac_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_hmac_alert_force(&hmac, kDifHmacAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdHmacFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write i2c's alert_test reg and check alert_cause.
  for (dif_i2c_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_i2c_alert_force(&i2c0, kDifI2cAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdI2c0FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write i2c's alert_test reg and check alert_cause.
  for (dif_i2c_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_i2c_alert_force(&i2c1, kDifI2cAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdI2c1FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write i2c's alert_test reg and check alert_cause.
  for (dif_i2c_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_i2c_alert_force(&i2c2, kDifI2cAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdI2c2FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write keymgr's alert_test reg and check alert_cause.
  for (dif_keymgr_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_keymgr_alert_force(&keymgr, kDifKeymgrAlertRecovOperationErr + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdKeymgrRecovOperationErr + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write kmac's alert_test reg and check alert_cause.
  for (dif_kmac_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_kmac_alert_force(&kmac, kDifKmacAlertRecovOperationErr + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdKmacRecovOperationErr + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write lc_ctrl's alert_test reg and check alert_cause.
  for (dif_lc_ctrl_alert_t i = 0; i < 3; ++i) {
    CHECK_DIF_OK(dif_lc_ctrl_alert_force(&lc_ctrl, kDifLcCtrlAlertFatalProgError + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdLcCtrlFatalProgError + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write otbn's alert_test reg and check alert_cause.
  for (dif_otbn_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_otbn_alert_force(&otbn, kDifOtbnAlertFatal + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdOtbnFatal + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // TODO(lowrisc/opentitan#20348): Enable otp_ctrl when this is fixed.
  if (kBootStage != kBootStageOwner) {
    // Write otp_ctrl's alert_test reg and check alert_cause.
    for (dif_otp_ctrl_alert_t i = 0; i < 5; ++i) {
      CHECK_DIF_OK(dif_otp_ctrl_alert_force(&otp_ctrl, kDifOtpCtrlAlertFatalMacroError + i));

      // Verify that alert handler received it.
      exp_alert = kTopVerbanoAlertIdOtpCtrlFatalMacroError + i;
      CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
          &alert_handler, exp_alert, &is_cause));
      CHECK(is_cause, "Expect alert %d!", exp_alert);

      // Clear alert cause register
      CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
          &alert_handler, exp_alert));
    }
  }

  // Write pattgen's alert_test reg and check alert_cause.
  for (dif_pattgen_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_pattgen_alert_force(&pattgen, kDifPattgenAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdPattgenFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write pinmux's alert_test reg and check alert_cause.
  for (dif_pinmux_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_pinmux_alert_force(&pinmux_aon, kDifPinmuxAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdPinmuxAonFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write pwm's alert_test reg and check alert_cause.
  for (dif_pwm_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_pwm_alert_force(&pwm_aon, kDifPwmAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdPwmAonFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write pwrmgr's alert_test reg and check alert_cause.
  for (dif_pwrmgr_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_pwrmgr_alert_force(&pwrmgr_aon, kDifPwrmgrAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdPwrmgrAonFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write rom_ctrl's alert_test reg and check alert_cause.
  for (dif_rom_ctrl_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_rom_ctrl_alert_force(&rom_ctrl, kDifRomCtrlAlertFatal + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdRomCtrlFatal + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write rstmgr's alert_test reg and check alert_cause.
  for (dif_rstmgr_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_rstmgr_alert_force(&rstmgr_aon, kDifRstmgrAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdRstmgrAonFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write rv_core_ibex's alert_test reg and check alert_cause.
  for (dif_rv_core_ibex_alert_t i = 0; i < 4; ++i) {
    CHECK_DIF_OK(dif_rv_core_ibex_alert_force(&rv_core_ibex, kDifRvCoreIbexAlertFatalSwErr + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdRvCoreIbexFatalSwErr + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write rv_plic's alert_test reg and check alert_cause.
  for (dif_rv_plic_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_rv_plic_alert_force(&rv_plic, kDifRvPlicAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdRvPlicFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write rv_timer's alert_test reg and check alert_cause.
  for (dif_rv_timer_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_rv_timer_alert_force(&rv_timer, kDifRvTimerAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdRvTimerFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write sensor_ctrl's alert_test reg and check alert_cause.
  for (dif_sensor_ctrl_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_sensor_ctrl_alert_force(&sensor_ctrl_aon, kDifSensorCtrlAlertRecovAlert + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdSensorCtrlAonRecovAlert + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write spi_device's alert_test reg and check alert_cause.
  for (dif_spi_device_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_spi_device_alert_force(&spi_device, kDifSpiDeviceAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdSpiDeviceFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write spi_host's alert_test reg and check alert_cause.
  for (dif_spi_host_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_spi_host_alert_force(&spi_host0, kDifSpiHostAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdSpiHost0FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write spi_host's alert_test reg and check alert_cause.
  for (dif_spi_host_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_spi_host_alert_force(&spi_host1, kDifSpiHostAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdSpiHost1FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write sram_ctrl's alert_test reg and check alert_cause.
  for (dif_sram_ctrl_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_sram_ctrl_alert_force(&sram_ctrl_main, kDifSramCtrlAlertFatalError + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdSramCtrlMainFatalError + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write sram_ctrl's alert_test reg and check alert_cause.
  for (dif_sram_ctrl_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_sram_ctrl_alert_force(&sram_ctrl_ret_aon, kDifSramCtrlAlertFatalError + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdSramCtrlRetAonFatalError + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write sysrst_ctrl's alert_test reg and check alert_cause.
  for (dif_sysrst_ctrl_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_sysrst_ctrl_alert_force(&sysrst_ctrl_aon, kDifSysrstCtrlAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdSysrstCtrlAonFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write uart's alert_test reg and check alert_cause.
  for (dif_uart_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_uart_alert_force(&uart0, kDifUartAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdUart0FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write uart's alert_test reg and check alert_cause.
  for (dif_uart_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_uart_alert_force(&uart1, kDifUartAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdUart1FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write uart's alert_test reg and check alert_cause.
  for (dif_uart_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_uart_alert_force(&uart2, kDifUartAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdUart2FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write uart's alert_test reg and check alert_cause.
  for (dif_uart_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_uart_alert_force(&uart3, kDifUartAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdUart3FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write usbdev's alert_test reg and check alert_cause.
  for (dif_usbdev_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_usbdev_alert_force(&usbdev, kDifUsbdevAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopVerbanoAlertIdUsbdevFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }
}

bool test_main(void) {
  init_peripherals();
  alert_handler_config();
  trigger_alert_test();
  return true;
}
