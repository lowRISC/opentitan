// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/alert_fi.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pattgen.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwm.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rom_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/alert_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

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

enum { kNumberTestRegisters = 63 };

static status_t init_peripherals(void) {
  mmio_region_t base_addr;
  base_addr = mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  TRY(dif_alert_handler_init(base_addr, &alert_handler));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR);
  TRY(dif_adc_ctrl_init(base_addr, &adc_ctrl_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR);
  TRY(dif_aes_init(base_addr, &aes));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR);
  TRY(dif_aon_timer_init(base_addr, &aon_timer_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR);
  TRY(dif_clkmgr_init(base_addr, &clkmgr_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR);
  TRY(dif_csrng_init(base_addr, &csrng));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR);
  TRY(dif_edn_init(base_addr, &edn0));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR);
  TRY(dif_edn_init(base_addr, &edn1));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR);
  TRY(dif_entropy_src_init(base_addr, &entropy_src));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR);
  TRY(dif_flash_ctrl_init(base_addr, &flash_ctrl));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR);
  TRY(dif_gpio_init(base_addr, &gpio));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR);
  TRY(dif_hmac_init(base_addr, &hmac));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR);
  TRY(dif_i2c_init(base_addr, &i2c0));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C1_BASE_ADDR);
  TRY(dif_i2c_init(base_addr, &i2c1));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C2_BASE_ADDR);
  TRY(dif_i2c_init(base_addr, &i2c2));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR);
  TRY(dif_keymgr_init(base_addr, &keymgr));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR);
  TRY(dif_kmac_init(base_addr, &kmac));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR);
  TRY(dif_lc_ctrl_init(base_addr, &lc_ctrl));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR);
  TRY(dif_otbn_init(base_addr, &otbn));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR);
  TRY(dif_otp_ctrl_init(base_addr, &otp_ctrl));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PATTGEN_BASE_ADDR);
  TRY(dif_pattgen_init(base_addr, &pattgen));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  TRY(dif_pinmux_init(base_addr, &pinmux_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PWM_AON_BASE_ADDR);
  TRY(dif_pwm_init(base_addr, &pwm_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR);
  TRY(dif_pwrmgr_init(base_addr, &pwrmgr_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR);
  TRY(dif_rom_ctrl_init(base_addr, &rom_ctrl));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR);
  TRY(dif_rstmgr_init(base_addr, &rstmgr_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);
  TRY(dif_rv_core_ibex_init(base_addr, &rv_core_ibex));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  TRY(dif_rv_plic_init(base_addr, &rv_plic));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR);
  TRY(dif_rv_timer_init(base_addr, &rv_timer));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR);
  TRY(dif_sensor_ctrl_init(base_addr, &sensor_ctrl_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR);
  TRY(dif_spi_device_init(base_addr, &spi_device));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR);
  TRY(dif_spi_host_init(base_addr, &spi_host0));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_HOST1_BASE_ADDR);
  TRY(dif_spi_host_init(base_addr, &spi_host1));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR);
  TRY(dif_sram_ctrl_init(base_addr, &sram_ctrl_main));

  base_addr =
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR);
  TRY(dif_sram_ctrl_init(base_addr, &sram_ctrl_ret_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR);
  TRY(dif_sysrst_ctrl_init(base_addr, &sysrst_ctrl_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR);
  TRY(dif_uart_init(base_addr, &uart0));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_UART1_BASE_ADDR);
  TRY(dif_uart_init(base_addr, &uart1));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_UART2_BASE_ADDR);
  TRY(dif_uart_init(base_addr, &uart2));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_UART3_BASE_ADDR);
  TRY(dif_uart_init(base_addr, &uart3));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_USBDEV_BASE_ADDR);
  TRY(dif_usbdev_init(base_addr, &usbdev));

  return OK_STATUS();
}

status_t handle_alert_fi_trigger(ujson_t *uj) {
  alert_fi_trigger_t uj_trigger;
  TRY(ujson_deserialize_alert_fi_trigger_t(uj, &uj_trigger));

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  if (uj_trigger.alert >= kNumberTestRegisters) {
    alert_fi_empty_out_t uj_output;
    uj_output.success = false;
    LOG_ERROR("Wrong alert given");
    RESP_OK(ujson_serialize_alert_fi_empty_out_t, uj, &uj_output);
  }

  // Trigger the alert given by the user. Namely, trigger the test register from
  // the corresponding block.
  switch (uj_trigger.alert) {
    case 0:
      TRY(dif_aes_alert_force(&aes, kDifAesAlertRecovCtrlUpdateErr));
      break;
    case 1:
      TRY(dif_aes_alert_force(&aes, kDifAesAlertFatalFault));
      break;
    case 2:
      TRY(dif_aon_timer_alert_force(&aon_timer_aon,
                                    kDifAonTimerAlertFatalFault));
      break;
    case 3:
      TRY(dif_clkmgr_alert_force(&clkmgr_aon, kDifClkmgrAlertRecovFault));
      break;
    case 4:
      TRY(dif_clkmgr_alert_force(&clkmgr_aon, kDifClkmgrAlertFatalFault));
      break;
    case 5:
      TRY(dif_csrng_alert_force(&csrng, kDifCsrngAlertRecovAlert));
      break;
    case 6:
      TRY(dif_csrng_alert_force(&csrng, kDifCsrngAlertFatalAlert));
      break;
    case 7:
      TRY(dif_edn_alert_force(&edn0, kDifEdnAlertRecovAlert));
      break;
    case 8:
      TRY(dif_edn_alert_force(&edn0, kDifEdnAlertFatalAlert));
      break;
    case 9:
      TRY(dif_edn_alert_force(&edn1, kDifEdnAlertRecovAlert));
      break;
    case 10:
      TRY(dif_edn_alert_force(&edn1, kDifEdnAlertFatalAlert));
      break;
    case 11:
      TRY(dif_entropy_src_alert_force(&entropy_src,
                                      kDifEntropySrcAlertRecovAlert));
      break;
    case 12:
      TRY(dif_entropy_src_alert_force(&entropy_src,
                                      kDifEntropySrcAlertFatalAlert));
      break;
    case 13:
      TRY(dif_flash_ctrl_alert_force(&flash_ctrl, kDifFlashCtrlAlertRecovErr));
      break;
    case 14:
      TRY(dif_flash_ctrl_alert_force(&flash_ctrl,
                                     kDifFlashCtrlAlertFatalStdErr));
      break;
    case 15:
      TRY(dif_flash_ctrl_alert_force(&flash_ctrl, kDifFlashCtrlAlertFatalErr));
      break;
    case 16:
      TRY(dif_flash_ctrl_alert_force(&flash_ctrl,
                                     kDifFlashCtrlAlertFatalPrimFlashAlert));
      break;
    case 17:
      TRY(dif_flash_ctrl_alert_force(&flash_ctrl,
                                     kDifFlashCtrlAlertRecovPrimFlashAlert));
      break;
    case 18:
      TRY(dif_gpio_alert_force(&gpio, kDifGpioAlertFatalFault));
      break;
    case 19:
      TRY(dif_hmac_alert_force(&hmac, kDifHmacAlertFatalFault));
      break;
    case 20:
      TRY(dif_i2c_alert_force(&i2c0, kDifI2cAlertFatalFault));
      break;
    case 21:
      TRY(dif_i2c_alert_force(&i2c1, kDifI2cAlertFatalFault));
      break;
    case 22:
      TRY(dif_i2c_alert_force(&i2c2, kDifI2cAlertFatalFault));
      break;
    case 23:
      TRY(dif_keymgr_alert_force(&keymgr, kDifKeymgrAlertRecovOperationErr));
      break;
    case 24:
      TRY(dif_keymgr_alert_force(&keymgr, kDifKeymgrAlertFatalFaultErr));
      break;
    case 25:
      TRY(dif_kmac_alert_force(&kmac, kDifKmacAlertRecovOperationErr));
      break;
    case 26:
      TRY(dif_kmac_alert_force(&kmac, kDifKmacAlertFatalFaultErr));
      break;
    case 27:
      TRY(dif_lc_ctrl_alert_force(&lc_ctrl, kDifLcCtrlAlertFatalProgError));
      break;
    case 28:
      TRY(dif_lc_ctrl_alert_force(&lc_ctrl, kDifLcCtrlAlertFatalStateError));
      break;
    case 29:
      TRY(dif_lc_ctrl_alert_force(&lc_ctrl, kDifLcCtrlAlertFatalBusIntegError));
      break;
    case 30:
      TRY(dif_otbn_alert_force(&otbn, kDifOtbnAlertFatal));
      break;
    case 31:
      TRY(dif_otbn_alert_force(&otbn, kDifOtbnAlertRecov));
      break;
    case 32:
      TRY(dif_otp_ctrl_alert_force(&otp_ctrl, kDifOtpCtrlAlertFatalMacroError));
      break;
    case 33:
      TRY(dif_otp_ctrl_alert_force(&otp_ctrl, kDifOtpCtrlAlertFatalCheckError));
      break;
    case 34:
      TRY(dif_otp_ctrl_alert_force(&otp_ctrl,
                                   kDifOtpCtrlAlertFatalBusIntegError));
      break;
    case 35:
      TRY(dif_otp_ctrl_alert_force(&otp_ctrl,
                                   kDifOtpCtrlAlertFatalPrimOtpAlert));
      break;
    case 36:
      TRY(dif_otp_ctrl_alert_force(&otp_ctrl,
                                   kDifOtpCtrlAlertRecovPrimOtpAlert));
      break;
    case 37:
      TRY(dif_pattgen_alert_force(&pattgen, kDifPattgenAlertFatalFault));
      break;
    case 38:
      TRY(dif_pinmux_alert_force(&pinmux_aon, kDifPinmuxAlertFatalFault));
      break;
    case 39:
      TRY(dif_pwm_alert_force(&pwm_aon, kDifPwmAlertFatalFault));
      break;
    case 40:
      TRY(dif_pwrmgr_alert_force(&pwrmgr_aon, kDifPwrmgrAlertFatalFault));
      break;
    case 41:
      TRY(dif_rom_ctrl_alert_force(&rom_ctrl, kDifRomCtrlAlertFatal));
      break;
    case 42:
      TRY(dif_rstmgr_alert_force(&rstmgr_aon, kDifRstmgrAlertFatalFault));
      break;
    case 43:
      TRY(dif_rstmgr_alert_force(&rstmgr_aon, kDifRstmgrAlertFatalCnstyFault));
      break;
    case 44:
      TRY(dif_rv_core_ibex_alert_force(&rv_core_ibex,
                                       kDifRvCoreIbexAlertFatalSwErr));
      break;
    case 45:
      TRY(dif_rv_core_ibex_alert_force(&rv_core_ibex,
                                       kDifRvCoreIbexAlertRecovSwErr));
      break;
    case 46:
      TRY(dif_rv_core_ibex_alert_force(&rv_core_ibex,
                                       kDifRvCoreIbexAlertFatalHwErr));
      break;
    case 47:
      TRY(dif_rv_core_ibex_alert_force(&rv_core_ibex,
                                       kDifRvCoreIbexAlertRecovHwErr));
      break;
    case 48:
      TRY(dif_rv_plic_alert_force(&rv_plic, kDifRvPlicAlertFatalFault));
      break;
    case 49:
      TRY(dif_rv_timer_alert_force(&rv_timer, kDifRvTimerAlertFatalFault));
      break;
    case 50:
      TRY(dif_sensor_ctrl_alert_force(&sensor_ctrl_aon,
                                      kDifSensorCtrlAlertRecovAlert));
      break;
    case 51:
      TRY(dif_sensor_ctrl_alert_force(&sensor_ctrl_aon,
                                      kDifSensorCtrlAlertFatalAlert));
      break;
    case 52:
      TRY(dif_spi_device_alert_force(&spi_device,
                                     kDifSpiDeviceAlertFatalFault));
      break;
    case 53:
      TRY(dif_spi_host_alert_force(&spi_host0, kDifSpiHostAlertFatalFault));
      break;
    case 54:
      TRY(dif_spi_host_alert_force(&spi_host1, kDifSpiHostAlertFatalFault));
      break;
    case 55:
      TRY(dif_sram_ctrl_alert_force(&sram_ctrl_main,
                                    kDifSramCtrlAlertFatalError));
      break;
    case 56:
      TRY(dif_sram_ctrl_alert_force(&sram_ctrl_ret_aon,
                                    kDifSramCtrlAlertFatalError));
      break;
    case 57:
      TRY(dif_sysrst_ctrl_alert_force(&sysrst_ctrl_aon,
                                      kDifSysrstCtrlAlertFatalFault));
      break;
    case 58:
      TRY(dif_uart_alert_force(&uart0, kDifUartAlertFatalFault));
      break;
    case 59:
      TRY(dif_uart_alert_force(&uart1, kDifUartAlertFatalFault));
      break;
    case 60:
      TRY(dif_uart_alert_force(&uart2, kDifUartAlertFatalFault));
      break;
    case 61:
      TRY(dif_uart_alert_force(&uart3, kDifUartAlertFatalFault));
      break;
    case 62:
      TRY(dif_usbdev_alert_force(&usbdev, kDifUsbdevAlertFatalFault));
      break;
    default:
      LOG_ERROR("Wrong alert given");
      return INVALID_ARGUMENT();
  }

  // Cycle a duration to ensure escalation propagated following the duration
  // settings of the user.
  uint32_t duration_cycles = 0;
  ptrdiff_t phase0_cycles_reg_offset =
      ALERT_HANDLER_CLASSA_PHASE0_CYC_SHADOWED_REG_OFFSET;
  duration_cycles +=
      mmio_region_read32(alert_handler.base_addr, phase0_cycles_reg_offset);
  ptrdiff_t phase1_cycles_reg_offset =
      ALERT_HANDLER_CLASSA_PHASE1_CYC_SHADOWED_REG_OFFSET;
  duration_cycles +=
      mmio_region_read32(alert_handler.base_addr, phase1_cycles_reg_offset);
  ptrdiff_t phase2_cycles_reg_offset =
      ALERT_HANDLER_CLASSA_PHASE2_CYC_SHADOWED_REG_OFFSET;
  duration_cycles +=
      mmio_region_read32(alert_handler.base_addr, phase2_cycles_reg_offset);
  ptrdiff_t phase3_cycles_reg_offset =
      ALERT_HANDLER_CLASSA_PHASE3_CYC_SHADOWED_REG_OFFSET;
  duration_cycles +=
      mmio_region_read32(alert_handler.base_addr, phase3_cycles_reg_offset);

  for (uint32_t wait = 0; wait < duration_cycles; wait++)
    asm volatile("nop");

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  alert_fi_alert_out_t uj_output;
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_alert_fi_alert_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_alert_fi_sensor_ctrl_trigger(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Write to sensor control's ALERT_TRIG
  TRY(dif_sensor_ctrl_set_ast_event_trigger(&sensor_ctrl_aon, 0,
                                            kDifToggleEnabled));

  // Cycle a duration to ensure escalation propagated following the duration
  // settings of the user.
  uint32_t duration_cycles = 0;
  ptrdiff_t phase0_cycles_reg_offset =
      ALERT_HANDLER_CLASSA_PHASE0_CYC_SHADOWED_REG_OFFSET;
  duration_cycles +=
      mmio_region_read32(alert_handler.base_addr, phase0_cycles_reg_offset);
  ptrdiff_t phase1_cycles_reg_offset =
      ALERT_HANDLER_CLASSA_PHASE1_CYC_SHADOWED_REG_OFFSET;
  duration_cycles +=
      mmio_region_read32(alert_handler.base_addr, phase1_cycles_reg_offset);
  ptrdiff_t phase2_cycles_reg_offset =
      ALERT_HANDLER_CLASSA_PHASE2_CYC_SHADOWED_REG_OFFSET;
  duration_cycles +=
      mmio_region_read32(alert_handler.base_addr, phase2_cycles_reg_offset);
  ptrdiff_t phase3_cycles_reg_offset =
      ALERT_HANDLER_CLASSA_PHASE3_CYC_SHADOWED_REG_OFFSET;
  duration_cycles +=
      mmio_region_read32(alert_handler.base_addr, phase3_cycles_reg_offset);

  for (uint32_t wait = 0; wait < duration_cycles; wait++)
    asm volatile("nop");

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  alert_fi_alert_out_t uj_output;
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_alert_fi_alert_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_alert_fi_ibex_sw_fatal(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Write to the CSR.
  TRY(dif_rv_core_ibex_trigger_sw_fatal_err_alert(&rv_core_ibex));

  // Cycle a duration to ensure escalation propagated following the duration
  // settings of the user.
  uint32_t duration_cycles = 0;
  ptrdiff_t phase0_cycles_reg_offset =
      ALERT_HANDLER_CLASSA_PHASE0_CYC_SHADOWED_REG_OFFSET;
  duration_cycles +=
      mmio_region_read32(alert_handler.base_addr, phase0_cycles_reg_offset);
  ptrdiff_t phase1_cycles_reg_offset =
      ALERT_HANDLER_CLASSA_PHASE1_CYC_SHADOWED_REG_OFFSET;
  duration_cycles +=
      mmio_region_read32(alert_handler.base_addr, phase1_cycles_reg_offset);
  ptrdiff_t phase2_cycles_reg_offset =
      ALERT_HANDLER_CLASSA_PHASE2_CYC_SHADOWED_REG_OFFSET;
  duration_cycles +=
      mmio_region_read32(alert_handler.base_addr, phase2_cycles_reg_offset);
  ptrdiff_t phase3_cycles_reg_offset =
      ALERT_HANDLER_CLASSA_PHASE3_CYC_SHADOWED_REG_OFFSET;
  duration_cycles +=
      mmio_region_read32(alert_handler.base_addr, phase3_cycles_reg_offset);

  for (uint32_t wait = 0; wait < duration_cycles; wait++)
    asm volatile("nop");

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  alert_fi_alert_out_t uj_output;
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_alert_fi_alert_out_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_alert_fi_init(ujson_t *uj) {
  // Configure the device.
  pentest_setup_device(uj, true, false);

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEdn |
                   kPentestPeripheralCsrng | kPentestPeripheralEntropy |
                   kPentestPeripheralAes | kPentestPeripheralHmac |
                   kPentestPeripheralKmac | kPentestPeripheralOtbn);

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Initialize all HW blocks
  TRY(init_peripherals());

  // Read different SKU config fields and return to host.
  TRY(pentest_send_sku_config(uj));

  return OK_STATUS();
}

status_t handle_alert_fi(ujson_t *uj) {
  alert_fi_subcommand_t cmd;
  TRY(ujson_deserialize_alert_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kAlertFiSubcommandInit:
      return handle_alert_fi_init(uj);
    case kAlertFiSubcommandTrigger:
      return handle_alert_fi_trigger(uj);
    case kAlertFiSubcommandSensorCtrlTrigger:
      return handle_alert_fi_sensor_ctrl_trigger(uj);
    case kAlertFiSubcommandIbexSwFatal:
      return handle_alert_fi_ibex_sw_fatal(uj);
    default:
      LOG_ERROR("Unrecognized Alert FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
