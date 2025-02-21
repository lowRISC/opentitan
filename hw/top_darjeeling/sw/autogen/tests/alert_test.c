// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// clang-format off

//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson
// -o hw/top_darjeeling
#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/autogen/dif_aes_autogen.h"
#include "sw/device/lib/dif/autogen/dif_alert_handler_autogen.h"
#include "sw/device/lib/dif/autogen/dif_aon_timer_autogen.h"
#include "sw/device/lib/dif/autogen/dif_clkmgr_autogen.h"
#include "sw/device/lib/dif/autogen/dif_csrng_autogen.h"
#include "sw/device/lib/dif/autogen/dif_dma_autogen.h"
#include "sw/device/lib/dif/autogen/dif_edn_autogen.h"
#include "sw/device/lib/dif/autogen/dif_gpio_autogen.h"
#include "sw/device/lib/dif/autogen/dif_hmac_autogen.h"
#include "sw/device/lib/dif/autogen/dif_i2c_autogen.h"
#include "sw/device/lib/dif/autogen/dif_keymgr_dpe_autogen.h"
#include "sw/device/lib/dif/autogen/dif_kmac_autogen.h"
#include "sw/device/lib/dif/autogen/dif_lc_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_mbx_autogen.h"
#include "sw/device/lib/dif/autogen/dif_otbn_autogen.h"
#include "sw/device/lib/dif/autogen/dif_otp_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_pinmux_autogen.h"
#include "sw/device/lib/dif/autogen/dif_pwrmgr_autogen.h"
#include "sw/device/lib/dif/autogen/dif_rom_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_rstmgr_autogen.h"
#include "sw/device/lib/dif/autogen/dif_rv_core_ibex_autogen.h"
#include "sw/device/lib/dif/autogen/dif_rv_plic_autogen.h"
#include "sw/device/lib/dif/autogen/dif_rv_timer_autogen.h"
#include "sw/device/lib/dif/autogen/dif_soc_dbg_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_soc_proxy_autogen.h"
#include "sw/device/lib/dif/autogen/dif_spi_device_autogen.h"
#include "sw/device/lib/dif/autogen/dif_spi_host_autogen.h"
#include "sw/device/lib/dif/autogen/dif_sram_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_uart_autogen.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

#include "alert_handler_regs.h"  // Generated.
#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_alert_handler_t alert_handler;
static dif_aes_t aes;
static dif_aon_timer_t aon_timer_aon;
static dif_clkmgr_t clkmgr_aon;
static dif_csrng_t csrng;
static dif_dma_t dma;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_gpio_t gpio;
static dif_hmac_t hmac;
static dif_i2c_t i2c0;
static dif_keymgr_dpe_t keymgr_dpe;
static dif_kmac_t kmac;
static dif_lc_ctrl_t lc_ctrl;
static dif_mbx_t mbx0;
static dif_mbx_t mbx1;
static dif_mbx_t mbx2;
static dif_mbx_t mbx3;
static dif_mbx_t mbx4;
static dif_mbx_t mbx5;
static dif_mbx_t mbx6;
static dif_mbx_t mbx_jtag;
static dif_mbx_t mbx_pcie0;
static dif_mbx_t mbx_pcie1;
static dif_otbn_t otbn;
static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux_aon;
static dif_pwrmgr_t pwrmgr_aon;
static dif_rom_ctrl_t rom_ctrl0;
static dif_rom_ctrl_t rom_ctrl1;
static dif_rstmgr_t rstmgr_aon;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_rv_plic_t rv_plic;
static dif_rv_timer_t rv_timer;
static dif_soc_dbg_ctrl_t soc_dbg_ctrl;
static dif_soc_proxy_t soc_proxy;
static dif_spi_device_t spi_device;
static dif_spi_host_t spi_host0;
static dif_sram_ctrl_t sram_ctrl_main;
static dif_sram_ctrl_t sram_ctrl_mbox;
static dif_sram_ctrl_t sram_ctrl_ret_aon;
static dif_uart_t uart0;

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  mmio_region_t base_addr;
  base_addr = mmio_region_from_addr(TOP_DARJEELING_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, &alert_handler));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_AES_BASE_ADDR);
  CHECK_DIF_OK(dif_aes_init(base_addr, &aes));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_AON_TIMER_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_aon_timer_init(base_addr, &aon_timer_aon));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_CLKMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_clkmgr_init(base_addr, &clkmgr_aon));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_CSRNG_BASE_ADDR);
  CHECK_DIF_OK(dif_csrng_init(base_addr, &csrng));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_DMA_BASE_ADDR);
  CHECK_DIF_OK(dif_dma_init(base_addr, &dma));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_EDN0_BASE_ADDR);
  CHECK_DIF_OK(dif_edn_init(base_addr, &edn0));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_EDN1_BASE_ADDR);
  CHECK_DIF_OK(dif_edn_init(base_addr, &edn1));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_GPIO_BASE_ADDR);
  CHECK_DIF_OK(dif_gpio_init(base_addr, &gpio));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_HMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_hmac_init(base_addr, &hmac));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_I2C0_BASE_ADDR);
  CHECK_DIF_OK(dif_i2c_init(base_addr, &i2c0));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_KEYMGR_DPE_BASE_ADDR);
  CHECK_DIF_OK(dif_keymgr_dpe_init(base_addr, &keymgr_dpe));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_KMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_kmac_init(base_addr, &kmac));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_LC_CTRL_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_lc_ctrl_init(base_addr, &lc_ctrl));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX0_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx0));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX1_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx1));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX2_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx2));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX3_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx3));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX4_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx4));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX5_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx5));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX6_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx6));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX_JTAG_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx_jtag));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX_PCIE0_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx_pcie0));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX_PCIE1_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx_pcie1));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_OTBN_BASE_ADDR);
  CHECK_DIF_OK(dif_otbn_init(base_addr, &otbn));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_otp_ctrl_init(base_addr, &otp_ctrl));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_PINMUX_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pinmux_init(base_addr, &pinmux_aon));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_PWRMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwrmgr_init(base_addr, &pwrmgr_aon));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_ROM_CTRL0_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_rom_ctrl_init(base_addr, &rom_ctrl0));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_ROM_CTRL1_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_rom_ctrl_init(base_addr, &rom_ctrl1));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_RSTMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_rstmgr_init(base_addr, &rstmgr_aon));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_core_ibex_init(base_addr, &rv_core_ibex));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &rv_plic));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_RV_TIMER_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_timer_init(base_addr, &rv_timer));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_SOC_DBG_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_soc_dbg_ctrl_init(base_addr, &soc_dbg_ctrl));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_SOC_PROXY_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_soc_proxy_init(base_addr, &soc_proxy));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_SPI_DEVICE_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_device_init(base_addr, &spi_device));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_SPI_HOST0_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_host_init(base_addr, &spi_host0));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_sram_ctrl_init(base_addr, &sram_ctrl_main));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_SRAM_CTRL_MBOX_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_sram_ctrl_init(base_addr, &sram_ctrl_mbox));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_SRAM_CTRL_RET_AON_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_sram_ctrl_init(base_addr, &sram_ctrl_ret_aon));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_UART0_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart0));

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
    exp_alert = kTopDarjeelingAlertIdAesRecovCtrlUpdateErr + i;
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
    exp_alert = kTopDarjeelingAlertIdAonTimerAonFatalFault + i;
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
    exp_alert = kTopDarjeelingAlertIdClkmgrAonRecovFault + i;
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
    exp_alert = kTopDarjeelingAlertIdCsrngRecovAlert + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write dma's alert_test reg and check alert_cause.
  for (dif_dma_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_dma_alert_force(&dma, kDifDmaAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdDmaFatalFault + i;
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
    exp_alert = kTopDarjeelingAlertIdEdn0RecovAlert + i;
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
    exp_alert = kTopDarjeelingAlertIdEdn1RecovAlert + i;
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
    exp_alert = kTopDarjeelingAlertIdGpioFatalFault + i;
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
    exp_alert = kTopDarjeelingAlertIdHmacFatalFault + i;
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
    exp_alert = kTopDarjeelingAlertIdI2c0FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write keymgr_dpe's alert_test reg and check alert_cause.
  for (dif_keymgr_dpe_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_keymgr_dpe_alert_force(&keymgr_dpe, kDifKeymgrDpeAlertRecovOperationErr + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdKeymgrDpeRecovOperationErr + i;
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
    exp_alert = kTopDarjeelingAlertIdKmacRecovOperationErr + i;
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
    exp_alert = kTopDarjeelingAlertIdLcCtrlFatalProgError + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write mbx's alert_test reg and check alert_cause.
  for (dif_mbx_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_mbx_alert_force(&mbx0, kDifMbxAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdMbx0FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write mbx's alert_test reg and check alert_cause.
  for (dif_mbx_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_mbx_alert_force(&mbx1, kDifMbxAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdMbx1FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write mbx's alert_test reg and check alert_cause.
  for (dif_mbx_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_mbx_alert_force(&mbx2, kDifMbxAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdMbx2FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write mbx's alert_test reg and check alert_cause.
  for (dif_mbx_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_mbx_alert_force(&mbx3, kDifMbxAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdMbx3FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write mbx's alert_test reg and check alert_cause.
  for (dif_mbx_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_mbx_alert_force(&mbx4, kDifMbxAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdMbx4FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write mbx's alert_test reg and check alert_cause.
  for (dif_mbx_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_mbx_alert_force(&mbx5, kDifMbxAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdMbx5FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write mbx's alert_test reg and check alert_cause.
  for (dif_mbx_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_mbx_alert_force(&mbx6, kDifMbxAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdMbx6FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write mbx's alert_test reg and check alert_cause.
  for (dif_mbx_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_mbx_alert_force(&mbx_jtag, kDifMbxAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdMbxJtagFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write mbx's alert_test reg and check alert_cause.
  for (dif_mbx_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_mbx_alert_force(&mbx_pcie0, kDifMbxAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdMbxPcie0FatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write mbx's alert_test reg and check alert_cause.
  for (dif_mbx_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_mbx_alert_force(&mbx_pcie1, kDifMbxAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdMbxPcie1FatalFault + i;
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
    exp_alert = kTopDarjeelingAlertIdOtbnFatal + i;
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
      exp_alert = kTopDarjeelingAlertIdOtpCtrlFatalMacroError + i;
      CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
          &alert_handler, exp_alert, &is_cause));
      CHECK(is_cause, "Expect alert %d!", exp_alert);

      // Clear alert cause register
      CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
          &alert_handler, exp_alert));
    }
  }

  // Write pinmux's alert_test reg and check alert_cause.
  for (dif_pinmux_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_pinmux_alert_force(&pinmux_aon, kDifPinmuxAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdPinmuxAonFatalFault + i;
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
    exp_alert = kTopDarjeelingAlertIdPwrmgrAonFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write rom_ctrl's alert_test reg and check alert_cause.
  for (dif_rom_ctrl_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_rom_ctrl_alert_force(&rom_ctrl0, kDifRomCtrlAlertFatal + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdRomCtrl0Fatal + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write rom_ctrl's alert_test reg and check alert_cause.
  for (dif_rom_ctrl_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_rom_ctrl_alert_force(&rom_ctrl1, kDifRomCtrlAlertFatal + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdRomCtrl1Fatal + i;
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
    exp_alert = kTopDarjeelingAlertIdRstmgrAonFatalFault + i;
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
    exp_alert = kTopDarjeelingAlertIdRvCoreIbexFatalSwErr + i;
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
    exp_alert = kTopDarjeelingAlertIdRvPlicFatalFault + i;
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
    exp_alert = kTopDarjeelingAlertIdRvTimerFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write soc_dbg_ctrl's alert_test reg and check alert_cause.
  for (dif_soc_dbg_ctrl_alert_t i = 0; i < 2; ++i) {
    CHECK_DIF_OK(dif_soc_dbg_ctrl_alert_force(&soc_dbg_ctrl, kDifSocDbgCtrlAlertFatalFault + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdSocDbgCtrlFatalFault + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write soc_proxy's alert_test reg and check alert_cause.
  for (dif_soc_proxy_alert_t i = 0; i < 29; ++i) {
    CHECK_DIF_OK(dif_soc_proxy_alert_force(&soc_proxy, kDifSocProxyAlertFatalAlertIntg + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdSocProxyFatalAlertIntg + i;
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
    exp_alert = kTopDarjeelingAlertIdSpiDeviceFatalFault + i;
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
    exp_alert = kTopDarjeelingAlertIdSpiHost0FatalFault + i;
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
    exp_alert = kTopDarjeelingAlertIdSramCtrlMainFatalError + i;
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
        &alert_handler, exp_alert, &is_cause));
    CHECK(is_cause, "Expect alert %d!", exp_alert);

    // Clear alert cause register
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
        &alert_handler, exp_alert));
  }

  // Write sram_ctrl's alert_test reg and check alert_cause.
  for (dif_sram_ctrl_alert_t i = 0; i < 1; ++i) {
    CHECK_DIF_OK(dif_sram_ctrl_alert_force(&sram_ctrl_mbox, kDifSramCtrlAlertFatalError + i));

    // Verify that alert handler received it.
    exp_alert = kTopDarjeelingAlertIdSramCtrlMboxFatalError + i;
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
    exp_alert = kTopDarjeelingAlertIdSramCtrlRetAonFatalError + i;
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
    exp_alert = kTopDarjeelingAlertIdUart0FatalFault + i;
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
