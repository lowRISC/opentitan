// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// clang-format off

//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
// -o hw/top_englishbreakfast
#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rom_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

#include "alert_handler_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_alert_handler_t alert_handler;
static dif_aes_t aes;
static dif_aon_timer_t aon_timer_aon;
static dif_clkmgr_t clkmgr_aon;
static dif_flash_ctrl_t flash_ctrl;
static dif_gpio_t gpio;
static dif_pinmux_t pinmux_aon;
static dif_pwrmgr_t pwrmgr_aon;
static dif_rom_ctrl_t rom_ctrl;
static dif_rstmgr_t rstmgr_aon;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_rv_plic_t rv_plic;
static dif_rv_timer_t rv_timer;
static dif_spi_device_t spi_device;
static dif_spi_host_t spi_host0;
static dif_sram_ctrl_t sram_ctrl_main;
static dif_uart_t uart0;
static dif_uart_t uart1;
static dif_usbdev_t usbdev;

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  mmio_region_t base_addr;
  base_addr = mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, &alert_handler));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_AES_BASE_ADDR);
  CHECK_DIF_OK(dif_aes_init(base_addr, &aes));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_AON_TIMER_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_aon_timer_init(base_addr, &aon_timer_aon));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_CLKMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_clkmgr_init(base_addr, &clkmgr_aon));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_flash_ctrl_init(base_addr, &flash_ctrl));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_GPIO_BASE_ADDR);
  CHECK_DIF_OK(dif_gpio_init(base_addr, &gpio));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_PINMUX_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pinmux_init(base_addr, &pinmux_aon));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_PWRMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwrmgr_init(base_addr, &pwrmgr_aon));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_rom_ctrl_init(base_addr, &rom_ctrl));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_RSTMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_rstmgr_init(base_addr, &rstmgr_aon));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_core_ibex_init(base_addr, &rv_core_ibex));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &rv_plic));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_RV_TIMER_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_timer_init(base_addr, &rv_timer));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_SPI_DEVICE_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_device_init(base_addr, &spi_device));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_SPI_HOST0_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_host_init(base_addr, &spi_host0));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_sram_ctrl_init(base_addr, &sram_ctrl_main));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_UART0_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart0));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_UART1_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart1));

  base_addr = mmio_region_from_addr(TOP_ENGLISHBREAKFAST_USBDEV_BASE_ADDR);
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

  // Write aes's alert_test reg and check alert_cause.
  for (dif_aes_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_aes_alert_force(&aes, kDifAesAlertRecovCtrlUpdateErr + i));

    // Verify that alert handler received it.
    exp_alert = kTopEnglishbreakfastAlertIdAesRecovCtrlUpdateErr + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdAonTimerAonFatalFault + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdClkmgrAonRecovFault + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdFlashCtrlRecovErr + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdGpioFatalFault + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdPinmuxAonFatalFault + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdPwrmgrAonFatalFault + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdRomCtrlFatal + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdRstmgrAonFatalFault + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdRvCoreIbexFatalSwErr + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdRvPlicFatalFault + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdRvTimerFatalFault + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdSpiDeviceFatalFault + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdSpiHost0FatalFault + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdSramCtrlMainFatalError + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdUart0FatalFault + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdUart1FatalFault + i;
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
    exp_alert = kTopEnglishbreakfastAlertIdUsbdevFatalFault + i;
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
