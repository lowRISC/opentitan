// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
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
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/ret_sram_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "adc_ctrl_regs.h"
#include "aes_regs.h"
#include "alert_handler_regs.h"
#include "aon_timer_regs.h"
#include "clkmgr_regs.h"
#include "csrng_regs.h"
#include "edn_regs.h"
#include "entropy_src_regs.h"
#include "flash_ctrl_regs.h"
#include "gpio_regs.h"
#include "hmac_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"
#include "keymgr_regs.h"
#include "kmac_regs.h"
#include "lc_ctrl_regs.h"
#include "otp_ctrl_regs.h"
#include "pattgen_regs.h"
#include "pinmux_regs.h"
#include "pwm_regs.h"
#include "pwrmgr_regs.h"
#include "rom_ctrl_regs.h"
#include "rstmgr_regs.h"
#include "rv_core_ibex_regs.h"
#include "rv_plic_regs.h"
#include "rv_timer_regs.h"
#include "sensor_ctrl_regs.h"
#include "spi_device_regs.h"
#include "spi_host_regs.h"
#include "sram_ctrl_regs.h"
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
#include "sw/device/lib/dif/autogen/dif_rv_dm_autogen.h"
#include "sw/device/lib/dif/autogen/dif_rv_timer_autogen.h"
#include "sw/device/lib/dif/autogen/dif_sensor_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_spi_device_autogen.h"
#include "sw/device/lib/dif/autogen/dif_spi_host_autogen.h"
#include "sw/device/lib/dif/autogen/dif_sram_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_sysrst_ctrl_autogen.h"
#include "sw/device/lib/dif/autogen/dif_uart_autogen.h"
#include "sw/device/lib/dif/autogen/dif_usbdev_autogen.h"
#include "sysrst_ctrl_regs.h"
#include "uart_regs.h"
#include "usbdev_regs.h"

OTTF_DEFINE_TEST_CONFIG(.ignore_alerts = true);

#define MAX_ISR_EXECUTIONS 10

// Retention SRAM slot used to store the current test phase marker.
#define RET_SRAM_SLOT_TEST_PHASE 0
// Retention SRAM slot to store the index of the alert being tested in
// All Active IRQ Phase (AAIP)
#define RET_SRAM_SLOT_ALL_ACTIVE_IRQ_IDX 1
// Retention SRAM slot to store the index of the alert being tested in
// All Active Reset Phase (AARP)
#define RET_SRAM_SLOT_ALL_ACTIVE_RESET_IDX 2

// State identifier indicating the test is in Phase 1 (All Active IRQ Phase)
#define TEST_PHASE_ALL_ACTIVE_IRQ 0xA117E57C
// State identifier indicating the test is in Phase 2 (All Active Reset Phase)
#define TEST_PHASE_ALL_ACTIVE_RESET 0xD33E5222

// Global DIF handles
dif_alert_handler_t alert_handler;
dif_pwrmgr_t pwrmgr;
dif_rv_plic_t rv_plic;
dif_rstmgr_t rstmgr;
dif_clkmgr_t clkmgr;
dif_aon_timer_t aon_timer;
dif_gpio_t gpio;
dif_uart_t uart0, uart1, uart2, uart3;
dif_spi_device_t spi_device;
dif_i2c_t i2c0, i2c1, i2c2;
dif_pattgen_t pattgen;
dif_rv_timer_t rv_timer;
dif_otp_ctrl_t otp_ctrl;
dif_lc_ctrl_t lc_ctrl;
dif_spi_host_t spi_host0, spi_host1;
dif_usbdev_t usbdev;
dif_pwrmgr_t pwrmgr_aon;
dif_rstmgr_t rstmgr_aon;
dif_clkmgr_t clkmgr_aon;
dif_sysrst_ctrl_t sysrst_ctrl_aon;
dif_adc_ctrl_t adc_ctrl_aon;
dif_pwm_t pwm_aon;
dif_pinmux_t pinmux_aon;
dif_aon_timer_t aon_timer_aon;
dif_sensor_ctrl_t sensor_ctrl_aon;
dif_sram_ctrl_t sram_ctrl_ret_aon;
dif_flash_ctrl_t flash_ctrl;
dif_rv_dm_t rv_dm;
dif_rv_plic_t rv_plic_for_alert;
dif_aes_t aes;
dif_hmac_t hmac;
dif_kmac_t kmac;
dif_otbn_t otbn_alert;
dif_keymgr_t keymgr_alert;
dif_csrng_t csrng_alert;
dif_entropy_src_t entropy_src_alert;
dif_edn_t edn0, edn1;
dif_sram_ctrl_t sram_ctrl_main;
dif_rom_ctrl_t rom_ctrl;
dif_rv_core_ibex_t rv_core_ibex;

static volatile bool plic_irq_fired = false;
static volatile top_earlgrey_alert_id_t serviced_alert =
    (top_earlgrey_alert_id_t)-1;
static volatile int isr_counter = 0;

typedef enum {
  kAlertSourceUnknown,
  kAlertSourceUart0,
  kAlertSourceUart1,
  kAlertSourceUart2,
  kAlertSourceUart3,
  kAlertSourceGpio,
  kAlertSourceSpiDevice,
  kAlertSourceI2c0,
  kAlertSourceI2c1,
  kAlertSourceI2c2,
  kAlertSourcePattgen,
  kAlertSourceRvTimer,
  kAlertSourceOtpCtrl,
  kAlertSourceLcCtrl,
  kAlertSourceSpiHost0,
  kAlertSourceSpiHost1,
  kAlertSourceUsbdev,
  kAlertSourcePwrmgrAon,
  kAlertSourceRstmgrAon,
  kAlertSourceClkmgrAon,
  kAlertSourceSysrstCtrlAon,
  kAlertSourceAdcCtrlAon,
  kAlertSourcePwmAon,
  kAlertSourcePinmuxAon,
  kAlertSourceAonTimerAon,
  kAlertSourceSensorCtrlAon,
  kAlertSourceSramCtrlRetAon,
  kAlertSourceFlashCtrl,
  kAlertSourceRvDm,
  kAlertSourceRvPlic,
  kAlertSourceAes,
  kAlertSourceHmac,
  kAlertSourceKmac,
  kAlertSourceOtbn,
  kAlertSourceKeymgr,
  kAlertSourceCsrng,
  kAlertSourceEntropySrc,
  kAlertSourceEdn0,
  kAlertSourceEdn1,
  kAlertSourceSramCtrlMain,
  kAlertSourceRomCtrl,
  kAlertSourceRvCoreIbex,
} alert_source_type_t;

// Forward declaration.
struct alert_config;
static void *get_peripheral_dif_handle(const struct alert_config *config);
static void cleanup_after_alert(const struct alert_config *config,
                                uint32_t current_test_phase);
static void prepare_for_all_active_irq(void);
static void prepare_for_all_active_reset(void);
static void check_alert_all_active_defaults(void);
// static void capture_and_log_debug_info(const char *label,
// top_earlgrey_alert_id_t current_alert_id);
static void enable_alert_handler_class_irq(
    dif_alert_handler_class_t class_to_enable);
static void deassert_alert_source(const struct alert_config *config);
static void check_alert_all_active_irq(uint32_t start_alert_id);
// static void log_alert_cause_bits(const dif_rstmgr_alert_info_dump_segment_t
// *dump, size_t segments_read);
static void check_reset_and_alert_info(
    dif_rstmgr_reset_info_bitfield_t reset_info, uint32_t expected_alert_id);
static void check_alert_all_active_reset(uint32_t alert_id);

// Function pointer types force/deassert functions
typedef dif_result_t (*alert_force_fn)(void *dif_handle,
                                       const struct alert_config *config);
typedef void (*alert_deassert_fn)(const struct alert_config *config);

typedef struct alert_config {
  top_earlgrey_alert_id_t id;
  const char *name;
  dif_alert_handler_class_t recommended_class;
  alert_source_type_t source_type;
  uintptr_t base_addr;
  alert_force_fn force_func;
  alert_deassert_fn deassert_func;
  bool skip_test;

  union {
    dif_uart_alert_t uart_alert;
    dif_gpio_alert_t gpio_alert;
    dif_spi_device_alert_t spi_device_alert;
    dif_i2c_alert_t i2c_alert;
    dif_pattgen_alert_t pattgen_alert;
    dif_rv_timer_alert_t rv_timer_alert;
    dif_otp_ctrl_alert_t otp_ctrl_alert;
    dif_lc_ctrl_alert_t lc_ctrl_alert;
    dif_spi_host_alert_t spi_host_alert;
    dif_usbdev_alert_t usbdev_alert;
    dif_pwrmgr_alert_t pwrmgr_aon_alert;
    dif_rstmgr_alert_t rstmgr_aon_alert;
    dif_clkmgr_alert_t clkmgr_aon_alert;
    dif_sysrst_ctrl_alert_t sysrst_ctrl_aon_alert;
    dif_adc_ctrl_alert_t adc_ctrl_aon_alert;
    dif_pwm_alert_t pwm_aon_alert;
    dif_pinmux_alert_t pinmux_aon_alert;
    dif_aon_timer_alert_t aon_timer_aon_alert;
    dif_sensor_ctrl_alert_t sensor_ctrl_aon_alert;
    dif_sram_ctrl_alert_t sram_ctrl_alert;
    dif_flash_ctrl_alert_t flash_ctrl_alert;
    dif_rv_dm_alert_t rv_dm_alert;
    dif_rv_plic_alert_t rv_plic_alert;
    dif_aes_alert_t aes_alert;
    dif_hmac_alert_t hmac_alert;
    dif_kmac_alert_t kmac_alert;
    dif_otbn_alert_t otbn_alert;
    dif_keymgr_alert_t keymgr_alert;
    dif_csrng_alert_t csrng_alert;
    dif_entropy_src_alert_t entropy_src_alert;
    dif_edn_alert_t edn_alert;
    dif_rom_ctrl_alert_t rom_ctrl_alert;
    dif_rv_core_ibex_alert_t rv_core_ibex_alert;
  } module_alert_type;
} alert_config_t;

// Module-specific force/deassert functions
static dif_result_t force_gpio_alert(void *dif_handle,
                                     const alert_config_t *config) {
  return dif_gpio_alert_force((dif_gpio_t *)dif_handle,
                              config->module_alert_type.gpio_alert);
}
static void deassert_gpio_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      GPIO_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_uart_alert(void *dif_handle,
                                     const alert_config_t *config) {
  dif_uart_t *uart = (dif_uart_t *)dif_handle;
  dif_uart_alert_t alert = config->module_alert_type.uart_alert;

  // Check if the handle is valid
  if (uart == NULL) {
    LOG_ERROR(">> FORCE_UART: UART handle is NULL");
    return kDifBadArg;
  }

  // This is the core function where the reset occurs
  dif_result_t result = dif_uart_alert_force(uart, alert);

  return result;
}

static void deassert_uart_alert(const alert_config_t *config) {
  LOG_INFO("De-asserting UART alert %d by clearing ALERT_TEST register.",
           config->id);
  // Writing 0 to the ALERT_TEST register should de-assert any forced alerts.
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      UART_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_spi_device_alert(void *dif_handle,
                                           const alert_config_t *config) {
  return dif_spi_device_alert_force((const dif_spi_device_t *)dif_handle,
                                    config->module_alert_type.spi_device_alert);
}
static void deassert_spi_device_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      SPI_DEVICE_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_i2c_alert(void *dif_handle,
                                    const alert_config_t *config) {
  dif_i2c_t *i2c = (dif_i2c_t *)dif_handle;
  dif_i2c_alert_t alert = config->module_alert_type.i2c_alert;

  if (i2c == NULL) {
    LOG_ERROR(">> FORCE_I2C: I2C handle is NULL");
    return kDifBadArg;
  }

  dif_result_t result = dif_i2c_alert_force(i2c, alert);

  return result;
}

static void deassert_i2c_alert(const alert_config_t *config) {
  // Writing 0 to the ALERT_TEST register de-asserts the fatal_fault alert.
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      I2C_ALERT_TEST_REG_OFFSET, 0);
  LOG_INFO("I2C ALERT_TEST register cleared for alert %d.", config->id);
}

static dif_result_t force_pattgen_alert(void *dif_handle,
                                        const alert_config_t *config) {
  dif_pattgen_t *pattgen = (dif_pattgen_t *)dif_handle;
  dif_pattgen_alert_t alert = config->module_alert_type.pattgen_alert;

  if (pattgen == NULL) {
    LOG_ERROR(">> FORCE_PATTGEN: PATTGEN handle is NULL");
    return kDifBadArg;
  }

  LOG_INFO(
      ">> FORCE_PATTGEN: PRE-CALL dif_pattgen_alert_force for alert type %d",
      alert);
  dif_result_t result = dif_pattgen_alert_force(pattgen, alert);

  return result;
}

static void deassert_pattgen_alert(const alert_config_t *config) {
  LOG_INFO("De-asserting PATTGEN alert %d by clearing ALERT_TEST register.",
           config->id);
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      PATTGEN_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_rv_timer_alert(void *dif_handle,
                                         const alert_config_t *config) {
  dif_rv_timer_t *timer = (dif_rv_timer_t *)dif_handle;
  dif_rv_timer_alert_t alert = config->module_alert_type.rv_timer_alert;
  return dif_rv_timer_alert_force(timer, alert);
}

static void deassert_rv_timer_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      RV_TIMER_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_otp_ctrl_alert(void *dif_handle,
                                         const alert_config_t *config) {
  dif_otp_ctrl_t *otp = (dif_otp_ctrl_t *)dif_handle;
  dif_otp_ctrl_alert_t alert = config->module_alert_type.otp_ctrl_alert;
  return dif_otp_ctrl_alert_force(otp, alert);
}

static void deassert_otp_ctrl_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      OTP_CTRL_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_lc_ctrl_alert(void *dif_handle,
                                        const alert_config_t *config) {
  dif_lc_ctrl_t *lc = (dif_lc_ctrl_t *)dif_handle;
  dif_lc_ctrl_alert_t alert = config->module_alert_type.lc_ctrl_alert;
  return dif_lc_ctrl_alert_force(lc, alert);
}
static void deassert_lc_ctrl_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      LC_CTRL_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_spi_host_alert(void *dif_handle,
                                         const alert_config_t *config) {
  dif_spi_host_t *spi_host = (dif_spi_host_t *)dif_handle;
  dif_spi_host_alert_t alert = config->module_alert_type.spi_host_alert;
  return dif_spi_host_alert_force(spi_host, alert);
}
static void deassert_spi_host_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      SPI_HOST_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_usbdev_alert(void *dif_handle,
                                       const alert_config_t *config) {
  dif_usbdev_t *usbdev_h = (dif_usbdev_t *)dif_handle;
  dif_usbdev_alert_t alert = config->module_alert_type.usbdev_alert;
  return dif_usbdev_alert_force(usbdev_h, alert);
}
static void deassert_usbdev_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      USBDEV_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_pwrmgr_aon_alert(void *dif_handle,
                                           const alert_config_t *config) {
  dif_pwrmgr_t *pwrmgr_h = (dif_pwrmgr_t *)dif_handle;
  dif_pwrmgr_alert_t alert = config->module_alert_type.pwrmgr_aon_alert;
  return dif_pwrmgr_alert_force(pwrmgr_h, alert);
}
static void deassert_pwrmgr_aon_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      PWRMGR_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_rstmgr_aon_alert(void *dif_handle,
                                           const alert_config_t *config) {
  dif_rstmgr_t *rstmgr_h = (dif_rstmgr_t *)dif_handle;
  dif_rstmgr_alert_t alert = config->module_alert_type.rstmgr_aon_alert;
  return dif_rstmgr_alert_force(rstmgr_h, alert);
}
static void deassert_rstmgr_aon_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      RSTMGR_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_clkmgr_aon_alert(void *dif_handle,
                                           const alert_config_t *config) {
  dif_clkmgr_t *clkmgr_h = (dif_clkmgr_t *)dif_handle;
  dif_clkmgr_alert_t alert = config->module_alert_type.clkmgr_aon_alert;
  return dif_clkmgr_alert_force(clkmgr_h, alert);
}
static void deassert_clkmgr_aon_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      CLKMGR_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_sysrst_ctrl_aon_alert(void *dif_handle,
                                                const alert_config_t *config) {
  dif_sysrst_ctrl_t *sysrst_ctrl_h = (dif_sysrst_ctrl_t *)dif_handle;
  dif_sysrst_ctrl_alert_t alert =
      config->module_alert_type.sysrst_ctrl_aon_alert;
  return dif_sysrst_ctrl_alert_force(sysrst_ctrl_h, alert);
}
static void deassert_sysrst_ctrl_aon_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      SYSRST_CTRL_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_adc_ctrl_aon_alert(void *dif_handle,
                                             const alert_config_t *config) {
  dif_adc_ctrl_t *adc_ctrl_h = (dif_adc_ctrl_t *)dif_handle;
  dif_adc_ctrl_alert_t alert = config->module_alert_type.adc_ctrl_aon_alert;
  return dif_adc_ctrl_alert_force(adc_ctrl_h, alert);
}
static void deassert_adc_ctrl_aon_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      ADC_CTRL_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_pwm_aon_alert(void *dif_handle,
                                        const alert_config_t *config) {
  dif_pwm_t *pwm_h = (dif_pwm_t *)dif_handle;
  dif_pwm_alert_t alert = config->module_alert_type.pwm_aon_alert;
  return dif_pwm_alert_force(pwm_h, alert);
}
static void deassert_pwm_aon_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      PWM_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_pinmux_aon_alert(void *dif_handle,
                                           const alert_config_t *config) {
  dif_pinmux_t *pinmux_h = (dif_pinmux_t *)dif_handle;
  dif_pinmux_alert_t alert = config->module_alert_type.pinmux_aon_alert;
  return dif_pinmux_alert_force(pinmux_h, alert);
}
static void deassert_pinmux_aon_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      PINMUX_ALERT_TEST_REG_OFFSET, 0);
  LOG_INFO("PINMUX_AON ALERT_TEST register cleared for alert %d.", config->id);
}

static dif_result_t force_aon_timer_aon_alert(void *dif_handle,
                                              const alert_config_t *config) {
  dif_aon_timer_t *aon_timer_h = (dif_aon_timer_t *)dif_handle;
  dif_aon_timer_alert_t alert = config->module_alert_type.aon_timer_aon_alert;
  return dif_aon_timer_alert_force(aon_timer_h, alert);
}
static void deassert_aon_timer_aon_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      AON_TIMER_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_sensor_ctrl_aon_alert(void *dif_handle,
                                                const alert_config_t *config) {
  dif_sensor_ctrl_t *sensor_ctrl = (dif_sensor_ctrl_t *)dif_handle;
  dif_sensor_ctrl_alert_t alert =
      config->module_alert_type.sensor_ctrl_aon_alert;
  return dif_sensor_ctrl_alert_force(sensor_ctrl, alert);
}

static void deassert_sensor_ctrl_aon_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      SENSOR_CTRL_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_sram_ctrl_alert(void *dif_handle,
                                          const alert_config_t *config) {
  dif_sram_ctrl_t *sram_ctrl = (dif_sram_ctrl_t *)dif_handle;
  dif_sram_ctrl_alert_t alert = config->module_alert_type.sram_ctrl_alert;
  return dif_sram_ctrl_alert_force(sram_ctrl, alert);
}

static void deassert_sram_ctrl_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      SRAM_CTRL_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_flash_ctrl_alert(void *dif_handle,
                                           const alert_config_t *config) {
  dif_flash_ctrl_t *flash_ctrl_h = (dif_flash_ctrl_t *)dif_handle;
  dif_flash_ctrl_alert_t alert = config->module_alert_type.flash_ctrl_alert;
  return dif_flash_ctrl_alert_force(flash_ctrl_h, alert);
}

static void deassert_flash_ctrl_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      FLASH_CTRL_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_rv_dm_alert(void *dif_handle,
                                      const alert_config_t *config) {
  dif_rv_dm_t *rv_dm_h = (dif_rv_dm_t *)dif_handle;
  dif_rv_dm_alert_t alert = config->module_alert_type.rv_dm_alert;
  return dif_rv_dm_alert_force(rv_dm_h, alert);
}

static void deassert_rv_dm_alert(const alert_config_t *config) {
  // No de-assert mechanism via register write for rv_dm alerts.
}

static dif_result_t force_rv_plic_alert(void *dif_handle,
                                        const alert_config_t *config) {
  dif_rv_plic_t *plic = (dif_rv_plic_t *)dif_handle;
  dif_rv_plic_alert_t alert = config->module_alert_type.rv_plic_alert;
  return dif_rv_plic_alert_force(plic, alert);
}

static void deassert_rv_plic_alert(const alert_config_t *config) {
  // Re-forcing the alert is assumed to de-assert it for some DIFs.
  // This is a fallback as there is no specific de-assert register.
  // temp force_rv_plic_alert(get_peripheral_dif_handle(config), config);
}

static dif_result_t force_aes_alert(void *dif_handle,
                                    const alert_config_t *config) {
  dif_aes_t *aes_h = (dif_aes_t *)dif_handle;
  dif_aes_alert_t alert = config->module_alert_type.aes_alert;
  return dif_aes_alert_force(aes_h, alert);
}

static void deassert_aes_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      AES_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_hmac_alert(void *dif_handle,
                                     const alert_config_t *config) {
  dif_hmac_t *hmac_h = (dif_hmac_t *)dif_handle;
  dif_hmac_alert_t alert = config->module_alert_type.hmac_alert;
  return dif_hmac_alert_force(hmac_h, alert);
}

static void deassert_hmac_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      HMAC_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_kmac_alert(void *dif_handle,
                                     const alert_config_t *config) {
  dif_kmac_t *kmac_h = (dif_kmac_t *)dif_handle;
  dif_kmac_alert_t alert = config->module_alert_type.kmac_alert;
  return dif_kmac_alert_force(kmac_h, alert);
}

static void deassert_kmac_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      KMAC_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_otbn_alert(void *dif_handle,
                                     const alert_config_t *config) {
  dif_otbn_t *otbn_h = (dif_otbn_t *)dif_handle;
  dif_otbn_alert_t alert = config->module_alert_type.otbn_alert;
  return dif_otbn_alert_force(otbn_h, alert);
}

static void deassert_otbn_alert(const alert_config_t *config) {}

static dif_result_t force_keymgr_alert(void *dif_handle,
                                       const alert_config_t *config) {
  dif_keymgr_t *keymgr_h = (dif_keymgr_t *)dif_handle;
  dif_keymgr_alert_t alert = config->module_alert_type.keymgr_alert;
  return dif_keymgr_alert_force(keymgr_h, alert);
}

static void deassert_keymgr_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      KEYMGR_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_csrng_alert(void *dif_handle,
                                      const alert_config_t *config) {
  dif_csrng_t *csrng_h = (dif_csrng_t *)dif_handle;
  dif_csrng_alert_t alert = config->module_alert_type.csrng_alert;
  return dif_csrng_alert_force(csrng_h, alert);
}

static void deassert_csrng_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      CSRNG_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_entropy_src_alert(void *dif_handle,
                                            const alert_config_t *config) {
  dif_entropy_src_t *entropy_src_h = (dif_entropy_src_t *)dif_handle;
  dif_entropy_src_alert_t alert = config->module_alert_type.entropy_src_alert;
  return dif_entropy_src_alert_force(entropy_src_h, alert);
}

static void deassert_entropy_src_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      ENTROPY_SRC_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_edn_alert(void *dif_handle,
                                    const alert_config_t *config) {
  dif_edn_t *edn_h = (dif_edn_t *)dif_handle;
  dif_edn_alert_t alert = config->module_alert_type.edn_alert;
  return dif_edn_alert_force(edn_h, alert);
}

static void deassert_edn_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      EDN_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_sram_ctrl_main_alert(void *dif_handle,
                                               const alert_config_t *config) {
  dif_sram_ctrl_t *sram_ctrl_h = (dif_sram_ctrl_t *)dif_handle;
  dif_sram_ctrl_alert_t alert = config->module_alert_type.sram_ctrl_alert;
  return dif_sram_ctrl_alert_force(sram_ctrl_h, alert);
}

static void deassert_sram_ctrl_main_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      SRAM_CTRL_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_rom_ctrl_alert(void *dif_handle,
                                         const alert_config_t *config) {
  dif_rom_ctrl_t *rom_ctrl_h = (dif_rom_ctrl_t *)dif_handle;
  dif_rom_ctrl_alert_t alert = config->module_alert_type.rom_ctrl_alert;
  return dif_rom_ctrl_alert_force(rom_ctrl_h, alert);
}

static void deassert_rom_ctrl_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      ROM_CTRL_ALERT_TEST_REG_OFFSET, 0);
}

static dif_result_t force_rv_core_ibex_alert(void *dif_handle,
                                             const alert_config_t *config) {
  dif_rv_core_ibex_t *rv_core_ibex_h = (dif_rv_core_ibex_t *)dif_handle;
  dif_rv_core_ibex_alert_t alert = config->module_alert_type.rv_core_ibex_alert;
  return dif_rv_core_ibex_alert_force(rv_core_ibex_h, alert);
}

static void deassert_rv_core_ibex_alert(const alert_config_t *config) {
  mmio_region_write32(mmio_region_from_addr(config->base_addr),
                      RV_CORE_IBEX_ALERT_TEST_REG_OFFSET, 0);
}

// This function implements the logic for looking up the correct DIF handle
// for a given alert configuration
// Returns the appropriate peripheral DIF handle based on the alert source type.
//
// @param config The alert configuration.
// @return A pointer to the peripheral's DIF handle, or NULL if unknown.

static void *get_peripheral_dif_handle(const alert_config_t *config) {
  void *handle = NULL;  // Initialize handle
  switch (config->source_type) {
    case kAlertSourceUart0:
      handle = (void *)&uart0;
      break;
    case kAlertSourceUart1:
      handle = (void *)&uart1;
      break;
    case kAlertSourceUart2:
      handle = (void *)&uart2;
      break;
    case kAlertSourceUart3:
      handle = (void *)&uart3;
      break;
    case kAlertSourceGpio:
      handle = (void *)&gpio;
      break;
    case kAlertSourceSpiDevice:
      handle = (void *)&spi_device;
      break;
    case kAlertSourceI2c0:
      handle = (void *)&i2c0;
      break;
    case kAlertSourceI2c1:
      handle = (void *)&i2c1;
      break;
    case kAlertSourceI2c2:
      handle = (void *)&i2c2;
      break;
    case kAlertSourcePattgen:
      handle = (void *)&pattgen;
      break;
    case kAlertSourceRvTimer:
      handle = (void *)&rv_timer;
      break;
    case kAlertSourceOtpCtrl:
      handle = (void *)&otp_ctrl;
      break;
    case kAlertSourceLcCtrl:
      handle = (void *)&lc_ctrl;
      break;
    case kAlertSourceSpiHost0:
      handle = (void *)&spi_host0;
      break;
    case kAlertSourceSpiHost1:
      handle = (void *)&spi_host1;
      break;
    case kAlertSourceUsbdev:
      handle = (void *)&usbdev;
      break;
    case kAlertSourcePwrmgrAon:
      handle = (void *)&pwrmgr_aon;
      break;
    case kAlertSourceRstmgrAon:
      handle = (void *)&rstmgr_aon;
      break;
    case kAlertSourceClkmgrAon:
      handle = (void *)&clkmgr_aon;
      break;
    case kAlertSourceSysrstCtrlAon:
      handle = (void *)&sysrst_ctrl_aon;
      break;
    case kAlertSourceAdcCtrlAon:
      handle = (void *)&adc_ctrl_aon;
      break;
    case kAlertSourcePwmAon:
      handle = (void *)&pwm_aon;
      break;
    case kAlertSourcePinmuxAon:
      handle = (void *)&pinmux_aon;
      break;
    case kAlertSourceAonTimerAon:
      handle = (void *)&aon_timer_aon;
      break;
    case kAlertSourceSensorCtrlAon:
      handle = (void *)&sensor_ctrl_aon;
      break;
    case kAlertSourceSramCtrlRetAon:
      handle = (void *)&sram_ctrl_ret_aon;
      break;
    case kAlertSourceFlashCtrl:
      handle = (void *)&flash_ctrl;
      break;
    case kAlertSourceRvDm:
      handle = (void *)&rv_dm;
      break;
    case kAlertSourceRvPlic:
      handle = (void *)&rv_plic_for_alert;
      break;
    case kAlertSourceAes:
      handle = (void *)&aes;
      break;
    case kAlertSourceHmac:
      handle = (void *)&hmac;
      break;
    case kAlertSourceKmac:
      handle = (void *)&kmac;
      break;
    case kAlertSourceOtbn:
      handle = (void *)&otbn_alert;
      break;
    case kAlertSourceKeymgr:
      handle = (void *)&keymgr_alert;
      break;
    case kAlertSourceCsrng:
      handle = (void *)&csrng_alert;
      break;
    case kAlertSourceEntropySrc:
      handle = (void *)&entropy_src_alert;
      break;
    case kAlertSourceEdn0:
      handle = (void *)&edn0;
      break;
    case kAlertSourceEdn1:
      handle = (void *)&edn1;
      break;
    case kAlertSourceSramCtrlMain:
      handle = (void *)&sram_ctrl_main;
      break;
    case kAlertSourceRomCtrl:
      handle = (void *)&rom_ctrl;
      break;
    case kAlertSourceRvCoreIbex:
      handle = (void *)&rv_core_ibex;
      break;
    default:
      LOG_ERROR("Unknown alert source type %d for alert %d (%s).",
                config->source_type, config->id, config->name);
      return NULL;
  }
  return handle;
}

static const alert_config_t kAlertConfigs[ALERT_HANDLER_PARAM_N_ALERTS] = {
    [kTopEarlgreyAlertIdUart0FatalFault] =
        {.id = kTopEarlgreyAlertIdUart0FatalFault,
         .name = "uart0_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceUart0,
         .base_addr = TOP_EARLGREY_UART0_BASE_ADDR,
         .force_func = force_uart_alert,
         .deassert_func = deassert_uart_alert,
         .module_alert_type.uart_alert = kDifUartAlertFatalFault},
    [kTopEarlgreyAlertIdUart1FatalFault] =
        {.id = kTopEarlgreyAlertIdUart1FatalFault,
         .name = "uart1_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceUart1,
         .base_addr = TOP_EARLGREY_UART1_BASE_ADDR,
         .force_func = force_uart_alert,
         .deassert_func = deassert_uart_alert,
         .module_alert_type.uart_alert = kDifUartAlertFatalFault},
    [kTopEarlgreyAlertIdUart2FatalFault] =
        {.id = kTopEarlgreyAlertIdUart2FatalFault,
         .name = "uart2_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceUart2,
         .base_addr = TOP_EARLGREY_UART2_BASE_ADDR,
         .force_func = force_uart_alert,
         .deassert_func = deassert_uart_alert,
         .module_alert_type.uart_alert = kDifUartAlertFatalFault},
    [kTopEarlgreyAlertIdUart3FatalFault] =
        {.id = kTopEarlgreyAlertIdUart3FatalFault,
         .name = "uart3_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceUart3,
         .base_addr = TOP_EARLGREY_UART3_BASE_ADDR,
         .force_func = force_uart_alert,
         .deassert_func = deassert_uart_alert,
         .module_alert_type.uart_alert = kDifUartAlertFatalFault},
    [kTopEarlgreyAlertIdGpioFatalFault] =
        {.id = kTopEarlgreyAlertIdGpioFatalFault,
         .name = "gpio_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceGpio,
         .base_addr = TOP_EARLGREY_GPIO_BASE_ADDR,
         .force_func = force_gpio_alert,
         .deassert_func = deassert_gpio_alert,
         .module_alert_type.gpio_alert = kDifGpioAlertFatalFault},
    [kTopEarlgreyAlertIdSpiDeviceFatalFault] =
        {.id = kTopEarlgreyAlertIdSpiDeviceFatalFault,
         .name = "spi_device_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceSpiDevice,
         .base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
         .force_func = force_spi_device_alert,
         .deassert_func = deassert_spi_device_alert,
         .module_alert_type.spi_device_alert = kDifSpiDeviceAlertFatalFault},
    [kTopEarlgreyAlertIdI2c0FatalFault] =
        {.id = kTopEarlgreyAlertIdI2c0FatalFault,
         .name = "i2c0_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceI2c0,
         .base_addr = TOP_EARLGREY_I2C0_BASE_ADDR,
         .force_func = force_i2c_alert,
         .deassert_func = deassert_i2c_alert,
         .module_alert_type.i2c_alert = kDifI2cAlertFatalFault},
    [kTopEarlgreyAlertIdI2c1FatalFault] =
        {.id = kTopEarlgreyAlertIdI2c1FatalFault,
         .name = "i2c1_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceI2c1,
         .base_addr = TOP_EARLGREY_I2C1_BASE_ADDR,
         .force_func = force_i2c_alert,
         .deassert_func = deassert_i2c_alert,
         .module_alert_type.i2c_alert = kDifI2cAlertFatalFault},
    [kTopEarlgreyAlertIdI2c2FatalFault] =
        {.id = kTopEarlgreyAlertIdI2c2FatalFault,
         .name = "i2c2_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceI2c2,
         .base_addr = TOP_EARLGREY_I2C2_BASE_ADDR,
         .force_func = force_i2c_alert,
         .deassert_func = deassert_i2c_alert,
         .module_alert_type.i2c_alert = kDifI2cAlertFatalFault},
    [kTopEarlgreyAlertIdPattgenFatalFault] =
        {.id = kTopEarlgreyAlertIdPattgenFatalFault,
         .name = "pattgen_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourcePattgen,
         .base_addr = TOP_EARLGREY_PATTGEN_BASE_ADDR,
         .force_func = force_pattgen_alert,
         .deassert_func = deassert_pattgen_alert,
         .module_alert_type.pattgen_alert = kDifPattgenAlertFatalFault},
    [kTopEarlgreyAlertIdRvTimerFatalFault] =
        {.id = kTopEarlgreyAlertIdRvTimerFatalFault,
         .name = "rv_timer_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceRvTimer,
         .base_addr = TOP_EARLGREY_RV_TIMER_BASE_ADDR,
         .force_func = force_rv_timer_alert,
         .deassert_func = deassert_rv_timer_alert,
         .module_alert_type.rv_timer_alert = kDifRvTimerAlertFatalFault},
    [kTopEarlgreyAlertIdOtpCtrlFatalMacroError] =
        {.id = kTopEarlgreyAlertIdOtpCtrlFatalMacroError,
         .name = "otp_ctrl_fatal_macro_error",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceOtpCtrl,
         .base_addr = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR,
         .force_func = force_otp_ctrl_alert,
         .deassert_func = deassert_otp_ctrl_alert,
         .module_alert_type.otp_ctrl_alert = kDifOtpCtrlAlertFatalMacroError},
    [kTopEarlgreyAlertIdOtpCtrlFatalCheckError] =
        {.id = kTopEarlgreyAlertIdOtpCtrlFatalCheckError,
         .name = "otp_ctrl_fatal_check_error",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceOtpCtrl,
         .base_addr = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR,
         .force_func = force_otp_ctrl_alert,
         .deassert_func = deassert_otp_ctrl_alert,
         .module_alert_type.otp_ctrl_alert = kDifOtpCtrlAlertFatalCheckError},
    [kTopEarlgreyAlertIdOtpCtrlFatalBusIntegError] =
        {.id = kTopEarlgreyAlertIdOtpCtrlFatalBusIntegError,
         .name = "otp_ctrl_fatal_bus_integ_error",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceOtpCtrl,
         .base_addr = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR,
         .force_func = force_otp_ctrl_alert,
         .deassert_func = deassert_otp_ctrl_alert,
         .module_alert_type.otp_ctrl_alert =
             kDifOtpCtrlAlertFatalBusIntegError},
    [kTopEarlgreyAlertIdOtpCtrlFatalPrimOtpAlert] =
        {.id = kTopEarlgreyAlertIdOtpCtrlFatalPrimOtpAlert,
         .name = "otp_ctrl_fatal_prim_otp_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .skip_test = false,
         .source_type = kAlertSourceOtpCtrl,
         .base_addr = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR,
         .force_func = force_otp_ctrl_alert,
         .deassert_func = deassert_otp_ctrl_alert,
         .module_alert_type.otp_ctrl_alert = kDifOtpCtrlAlertFatalPrimOtpAlert},
    [kTopEarlgreyAlertIdOtpCtrlRecovPrimOtpAlert] =
        {.id = kTopEarlgreyAlertIdOtpCtrlRecovPrimOtpAlert,
         .name = "otp_ctrl_recov_prim_otp_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceOtpCtrl,
         .base_addr = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR,
         .force_func = force_otp_ctrl_alert,
         .deassert_func = deassert_otp_ctrl_alert,
         .skip_test = false,
         .module_alert_type.otp_ctrl_alert = kDifOtpCtrlAlertRecovPrimOtpAlert},
    [kTopEarlgreyAlertIdLcCtrlFatalProgError] =
        {.id = kTopEarlgreyAlertIdLcCtrlFatalProgError,
         .name = "lc_ctrl_fatal_prog_error",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceLcCtrl,
         .base_addr = TOP_EARLGREY_LC_CTRL_BASE_ADDR,
         .force_func = force_lc_ctrl_alert,
         .deassert_func = deassert_lc_ctrl_alert,
         .skip_test = false,
         .module_alert_type.lc_ctrl_alert = kDifLcCtrlAlertFatalProgError},
    [kTopEarlgreyAlertIdLcCtrlFatalStateError] =
        {.id = kTopEarlgreyAlertIdLcCtrlFatalStateError,
         .name = "lc_ctrl_fatal_state_error",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceLcCtrl,
         .base_addr = TOP_EARLGREY_LC_CTRL_BASE_ADDR,
         .force_func = force_lc_ctrl_alert,
         .deassert_func = deassert_lc_ctrl_alert,
         .skip_test = false,
         .module_alert_type.lc_ctrl_alert = kDifLcCtrlAlertFatalStateError},
    [kTopEarlgreyAlertIdLcCtrlFatalBusIntegError] =
        {.id = kTopEarlgreyAlertIdLcCtrlFatalBusIntegError,
         .name = "lc_ctrl_fatal_bus_integ_error",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceLcCtrl,
         .base_addr = TOP_EARLGREY_LC_CTRL_BASE_ADDR,
         .force_func = force_lc_ctrl_alert,
         .deassert_func = deassert_lc_ctrl_alert,
         .skip_test = false,
         .module_alert_type.lc_ctrl_alert = kDifLcCtrlAlertFatalBusIntegError},
    [kTopEarlgreyAlertIdSpiHost0FatalFault] =
        {.id = kTopEarlgreyAlertIdSpiHost0FatalFault,
         .name = "spi_host0_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceSpiHost0,
         .base_addr = TOP_EARLGREY_SPI_HOST0_BASE_ADDR,
         .force_func = force_spi_host_alert,
         .deassert_func = deassert_spi_host_alert,
         .skip_test = false,
         .module_alert_type.spi_host_alert = kDifSpiHostAlertFatalFault},
    [kTopEarlgreyAlertIdSpiHost1FatalFault] =
        {.id = kTopEarlgreyAlertIdSpiHost1FatalFault,
         .name = "spi_host1_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceSpiHost1,
         .base_addr = TOP_EARLGREY_SPI_HOST1_BASE_ADDR,
         .force_func = force_spi_host_alert,
         .deassert_func = deassert_spi_host_alert,
         .skip_test = false,
         .module_alert_type.spi_host_alert = kDifSpiHostAlertFatalFault},
    [kTopEarlgreyAlertIdUsbdevFatalFault] =
        {.id = kTopEarlgreyAlertIdUsbdevFatalFault,
         .name = "usbdev_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceUsbdev,
         .base_addr = TOP_EARLGREY_USBDEV_BASE_ADDR,
         .force_func = force_usbdev_alert,
         .deassert_func = deassert_usbdev_alert,
         .skip_test = false,
         .module_alert_type.usbdev_alert = kDifUsbdevAlertFatalFault},
    [kTopEarlgreyAlertIdPwrmgrAonFatalFault] =
        {.id = kTopEarlgreyAlertIdPwrmgrAonFatalFault,
         .name = "pwrmgr_aon_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourcePwrmgrAon,
         .base_addr = TOP_EARLGREY_PWRMGR_AON_BASE_ADDR,
         .force_func = force_pwrmgr_aon_alert,
         .deassert_func = deassert_pwrmgr_aon_alert,
         .skip_test = false,
         .module_alert_type.pwrmgr_aon_alert = kDifPwrmgrAlertFatalFault},
    [kTopEarlgreyAlertIdRstmgrAonFatalFault] =
        {.id = kTopEarlgreyAlertIdRstmgrAonFatalFault,
         .name = "rstmgr_aon_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceRstmgrAon,
         .base_addr = TOP_EARLGREY_RSTMGR_AON_BASE_ADDR,
         .force_func = force_rstmgr_aon_alert,
         .deassert_func = deassert_rstmgr_aon_alert,
         .skip_test = false,
         .module_alert_type.rstmgr_aon_alert = kDifRstmgrAlertFatalFault},
    [kTopEarlgreyAlertIdRstmgrAonFatalCnstyFault] =
        {.id = kTopEarlgreyAlertIdRstmgrAonFatalCnstyFault,
         .name = "rstmgr_aon_fatal_cnsty_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceRstmgrAon,
         .base_addr = TOP_EARLGREY_RSTMGR_AON_BASE_ADDR,
         .force_func = force_rstmgr_aon_alert,
         .deassert_func = deassert_rstmgr_aon_alert,
         .skip_test = false,
         .module_alert_type.rstmgr_aon_alert = kDifRstmgrAlertFatalCnstyFault},
    [kTopEarlgreyAlertIdClkmgrAonRecovFault] =
        {.id = kTopEarlgreyAlertIdClkmgrAonRecovFault,
         .name = "clkmgr_aon_recov_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceClkmgrAon,
         .base_addr = TOP_EARLGREY_CLKMGR_AON_BASE_ADDR,
         .force_func = force_clkmgr_aon_alert,
         .deassert_func = deassert_clkmgr_aon_alert,
         .skip_test = false,
         .module_alert_type.clkmgr_aon_alert = kDifClkmgrAlertRecovFault},
    [kTopEarlgreyAlertIdClkmgrAonFatalFault] =
        {.id = kTopEarlgreyAlertIdClkmgrAonFatalFault,
         .name = "clkmgr_aon_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceClkmgrAon,
         .base_addr = TOP_EARLGREY_CLKMGR_AON_BASE_ADDR,
         .force_func = force_clkmgr_aon_alert,
         .deassert_func = deassert_clkmgr_aon_alert,
         .skip_test = false,
         .module_alert_type.clkmgr_aon_alert = kDifClkmgrAlertFatalFault},
    [kTopEarlgreyAlertIdSysrstCtrlAonFatalFault] =
        {.id = kTopEarlgreyAlertIdSysrstCtrlAonFatalFault,
         .name = "sysrst_ctrl_aon_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceSysrstCtrlAon,
         .base_addr = TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR,
         .force_func = force_sysrst_ctrl_aon_alert,
         .deassert_func = deassert_sysrst_ctrl_aon_alert,
         .skip_test = false,
         .module_alert_type.sysrst_ctrl_aon_alert =
             kDifSysrstCtrlAlertFatalFault},
    [kTopEarlgreyAlertIdAdcCtrlAonFatalFault] =
        {.id = kTopEarlgreyAlertIdAdcCtrlAonFatalFault,
         .name = "adc_ctrl_aon_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceAdcCtrlAon,
         .base_addr = TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR,
         .force_func = force_adc_ctrl_aon_alert,
         .deassert_func = deassert_adc_ctrl_aon_alert,
         .skip_test = false,
         .module_alert_type.adc_ctrl_aon_alert = kDifAdcCtrlAlertFatalFault},
    [kTopEarlgreyAlertIdPwmAonFatalFault] =
        {.id = kTopEarlgreyAlertIdPwmAonFatalFault,
         .name = "pwm_aon_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourcePwmAon,
         .base_addr = TOP_EARLGREY_PWM_AON_BASE_ADDR,
         .force_func = force_pwm_aon_alert,
         .deassert_func = deassert_pwm_aon_alert,
         .skip_test = false,
         .module_alert_type.pwm_aon_alert = kDifPwmAlertFatalFault},
    [kTopEarlgreyAlertIdPinmuxAonFatalFault] =
        {.id = kTopEarlgreyAlertIdPinmuxAonFatalFault,
         .name = "pinmux_aon_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourcePinmuxAon,
         .base_addr = TOP_EARLGREY_PINMUX_AON_BASE_ADDR,
         .force_func = force_pinmux_aon_alert,
         .deassert_func = deassert_pinmux_aon_alert,
         .skip_test = false,
         .module_alert_type.pinmux_aon_alert = kDifPinmuxAlertFatalFault},
    [kTopEarlgreyAlertIdAonTimerAonFatalFault] =
        {.id = kTopEarlgreyAlertIdAonTimerAonFatalFault,
         .name = "aon_timer_aon_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceAonTimerAon,
         .base_addr = TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR,
         .force_func = force_aon_timer_aon_alert,
         .deassert_func = deassert_aon_timer_aon_alert,
         .skip_test = false,
         .module_alert_type.aon_timer_aon_alert = kDifAonTimerAlertFatalFault},
    [kTopEarlgreyAlertIdSensorCtrlAonRecovAlert] =
        {.id = kTopEarlgreyAlertIdSensorCtrlAonRecovAlert,
         .name = "sensor_ctrl_aon_recov_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceSensorCtrlAon,
         .base_addr = TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR,
         .force_func = force_sensor_ctrl_aon_alert,
         .deassert_func = deassert_sensor_ctrl_aon_alert,
         .skip_test = false,
         .module_alert_type.sensor_ctrl_aon_alert =
             kDifSensorCtrlAlertRecovAlert},
    [kTopEarlgreyAlertIdSensorCtrlAonFatalAlert] =
        {.id = kTopEarlgreyAlertIdSensorCtrlAonFatalAlert,
         .name = "sensor_ctrl_aon_fatal_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceSensorCtrlAon,
         .base_addr = TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR,
         .force_func = force_sensor_ctrl_aon_alert,
         .deassert_func = deassert_sensor_ctrl_aon_alert,
         .skip_test = false,
         .module_alert_type.sensor_ctrl_aon_alert =
             kDifSensorCtrlAlertFatalAlert},
    [kTopEarlgreyAlertIdSramCtrlRetAonFatalError] =
        {.id = kTopEarlgreyAlertIdSramCtrlRetAonFatalError,
         .name = "sram_ctrl_ret_aon_fatal_error",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceSramCtrlRetAon,
         .base_addr = TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR,
         .force_func = force_sram_ctrl_alert,
         .deassert_func = deassert_sram_ctrl_alert,
         .skip_test = false,
         .module_alert_type.sram_ctrl_alert = kDifSramCtrlAlertFatalError},
    [kTopEarlgreyAlertIdFlashCtrlRecovErr] =
        {.id = kTopEarlgreyAlertIdFlashCtrlRecovErr,
         .name = "flash_ctrl_recov_err",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceFlashCtrl,
         .base_addr = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR,
         .force_func = force_flash_ctrl_alert,
         .deassert_func = deassert_flash_ctrl_alert,
         .skip_test = false,
         .module_alert_type.flash_ctrl_alert = kDifFlashCtrlAlertRecovErr},
    [kTopEarlgreyAlertIdFlashCtrlFatalStdErr] =
        {.id = kTopEarlgreyAlertIdFlashCtrlFatalStdErr,
         .name = "flash_ctrl_fatal_std_err",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceFlashCtrl,
         .base_addr = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR,
         .force_func = force_flash_ctrl_alert,
         .deassert_func = deassert_flash_ctrl_alert,
         .skip_test = false,
         .module_alert_type.flash_ctrl_alert = kDifFlashCtrlAlertFatalStdErr},
    [kTopEarlgreyAlertIdFlashCtrlFatalErr] =
        {.id = kTopEarlgreyAlertIdFlashCtrlFatalErr,
         .name = "flash_ctrl_fatal_err",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceFlashCtrl,
         .base_addr = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR,
         .force_func = force_flash_ctrl_alert,
         .deassert_func = deassert_flash_ctrl_alert,
         .skip_test =
#if FPGA_TARGET
             true,
#else
             false,
#endif
         .module_alert_type.flash_ctrl_alert = kDifFlashCtrlAlertFatalErr},
    [kTopEarlgreyAlertIdFlashCtrlFatalPrimFlashAlert] =
        {.id = kTopEarlgreyAlertIdFlashCtrlFatalPrimFlashAlert,
         .name = "flash_ctrl_fatal_prim_flash_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceFlashCtrl,
         .base_addr = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR,
         .force_func = force_flash_ctrl_alert,
         .deassert_func = deassert_flash_ctrl_alert,
         .skip_test = false,
         .module_alert_type.flash_ctrl_alert =
             kDifFlashCtrlAlertFatalPrimFlashAlert},
    [kTopEarlgreyAlertIdFlashCtrlRecovPrimFlashAlert] =
        {.id = kTopEarlgreyAlertIdFlashCtrlRecovPrimFlashAlert,
         .name = "flash_ctrl_recov_prim_flash_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceFlashCtrl,
         .base_addr = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR,
         .force_func = force_flash_ctrl_alert,
         .deassert_func = deassert_flash_ctrl_alert,
         .skip_test = false,
         .module_alert_type.flash_ctrl_alert =
             kDifFlashCtrlAlertRecovPrimFlashAlert},
    [kTopEarlgreyAlertIdRvDmFatalFault] =
        {.id = kTopEarlgreyAlertIdRvDmFatalFault,
         .name = "rv_dm_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceRvDm,
         .base_addr = TOP_EARLGREY_RV_DM_REGS_BASE_ADDR,
         .force_func = force_rv_dm_alert,
         .deassert_func = deassert_rv_dm_alert,
         .skip_test = false,
         .module_alert_type.rv_dm_alert = kDifRvDmAlertFatalFault},
    [kTopEarlgreyAlertIdRvPlicFatalFault] =
        {.id = kTopEarlgreyAlertIdRvPlicFatalFault,
         .name = "rv_plic_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceRvPlic,
         .base_addr = TOP_EARLGREY_RV_PLIC_BASE_ADDR,
         .force_func = force_rv_plic_alert,
         .deassert_func = deassert_rv_plic_alert,
         .skip_test = false,
         .module_alert_type.rv_plic_alert = kDifRvPlicAlertFatalFault},
    [kTopEarlgreyAlertIdAesRecovCtrlUpdateErr] =
        {.id = kTopEarlgreyAlertIdAesRecovCtrlUpdateErr,
         .name = "aes_recov_ctrl_update_err",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceAes,
         .base_addr = TOP_EARLGREY_AES_BASE_ADDR,
         .force_func = force_aes_alert,
         .deassert_func = deassert_aes_alert,
         .skip_test = false,
         .module_alert_type.aes_alert = kDifAesAlertRecovCtrlUpdateErr},
    [kTopEarlgreyAlertIdAesFatalFault] =
        {.id = kTopEarlgreyAlertIdAesFatalFault,
         .name = "aes_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceAes,
         .base_addr = TOP_EARLGREY_AES_BASE_ADDR,
         .force_func = force_aes_alert,
         .deassert_func = deassert_aes_alert,
         .skip_test = false,
         .module_alert_type.aes_alert = kDifAesAlertFatalFault},
    [kTopEarlgreyAlertIdHmacFatalFault] =
        {.id = kTopEarlgreyAlertIdHmacFatalFault,
         .name = "hmac_fatal_fault",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceHmac,
         .base_addr = TOP_EARLGREY_HMAC_BASE_ADDR,
         .force_func = force_hmac_alert,
         .deassert_func = deassert_hmac_alert,
         .skip_test = false,
         .module_alert_type.hmac_alert = kDifHmacAlertFatalFault},
    [kTopEarlgreyAlertIdKmacRecovOperationErr] =
        {.id = kTopEarlgreyAlertIdKmacRecovOperationErr,
         .name = "kmac_recov_operation_err",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceKmac,
         .base_addr = TOP_EARLGREY_KMAC_BASE_ADDR,
         .force_func = force_kmac_alert,
         .deassert_func = deassert_kmac_alert,
         .skip_test = false,
         .module_alert_type.kmac_alert = kDifKmacAlertRecovOperationErr},
    [kTopEarlgreyAlertIdKmacFatalFaultErr] =
        {.id = kTopEarlgreyAlertIdKmacFatalFaultErr,
         .name = "kmac_fatal_fault_err",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceKmac,
         .base_addr = TOP_EARLGREY_KMAC_BASE_ADDR,
         .force_func = force_kmac_alert,
         .deassert_func = deassert_kmac_alert,
         .skip_test = false,
         .module_alert_type.kmac_alert = kDifKmacAlertFatalFaultErr},
    [kTopEarlgreyAlertIdOtbnFatal] = {.id = kTopEarlgreyAlertIdOtbnFatal,
                                      .name = "otbn_fatal",
                                      .recommended_class =
                                          kDifAlertHandlerClassA,
                                      .source_type = kAlertSourceOtbn,
                                      .base_addr = TOP_EARLGREY_OTBN_BASE_ADDR,
                                      .force_func = force_otbn_alert,
                                      .deassert_func = deassert_otbn_alert,
                                      .skip_test = false,
                                      .module_alert_type.otbn_alert =
                                          kDifOtbnAlertFatal},
    [kTopEarlgreyAlertIdOtbnRecov] = {.id = kTopEarlgreyAlertIdOtbnRecov,
                                      .name = "otbn_recov",
                                      .recommended_class =
                                          kDifAlertHandlerClassA,
                                      .source_type = kAlertSourceOtbn,
                                      .base_addr = TOP_EARLGREY_OTBN_BASE_ADDR,
                                      .force_func = force_otbn_alert,
                                      .deassert_func = deassert_otbn_alert,
                                      .skip_test = false,
                                      .module_alert_type.otbn_alert =
                                          kDifOtbnAlertRecov},
    [kTopEarlgreyAlertIdKeymgrRecovOperationErr] =
        {.id = kTopEarlgreyAlertIdKeymgrRecovOperationErr,
         .name = "keymgr_recov_operation_err",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceKeymgr,
         .base_addr = TOP_EARLGREY_KEYMGR_BASE_ADDR,
         .force_func = force_keymgr_alert,
         .deassert_func = deassert_keymgr_alert,
         .skip_test = false,
         .module_alert_type.keymgr_alert = kDifKeymgrAlertRecovOperationErr},
    [kTopEarlgreyAlertIdKeymgrFatalFaultErr] =
        {.id = kTopEarlgreyAlertIdKeymgrFatalFaultErr,
         .name = "keymgr_fatal_fault_err",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceKeymgr,
         .base_addr = TOP_EARLGREY_KEYMGR_BASE_ADDR,
         .force_func = force_keymgr_alert,
         .deassert_func = deassert_keymgr_alert,
         .skip_test = false,
         .module_alert_type.keymgr_alert = kDifKeymgrAlertFatalFaultErr},
    [kTopEarlgreyAlertIdCsrngRecovAlert] =
        {.id = kTopEarlgreyAlertIdCsrngRecovAlert,
         .name = "csrng_recov_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceCsrng,
         .base_addr = TOP_EARLGREY_CSRNG_BASE_ADDR,
         .force_func = force_csrng_alert,
         .deassert_func = deassert_csrng_alert,
         .skip_test = false,
         .module_alert_type.csrng_alert = kDifCsrngAlertRecovAlert},
    [kTopEarlgreyAlertIdCsrngFatalAlert] =
        {.id = kTopEarlgreyAlertIdCsrngFatalAlert,
         .name = "csrng_fatal_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceCsrng,
         .base_addr = TOP_EARLGREY_CSRNG_BASE_ADDR,
         .force_func = force_csrng_alert,
         .deassert_func = deassert_csrng_alert,
         .skip_test = false,
         .module_alert_type.csrng_alert = kDifCsrngAlertFatalAlert},
    [kTopEarlgreyAlertIdEntropySrcRecovAlert] =
        {.id = kTopEarlgreyAlertIdEntropySrcRecovAlert,
         .name = "entropy_src_recov_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceEntropySrc,
         .base_addr = TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR,
         .force_func = force_entropy_src_alert,
         .deassert_func = deassert_entropy_src_alert,
         .skip_test = false,
         .module_alert_type.entropy_src_alert = kDifEntropySrcAlertRecovAlert},
    [kTopEarlgreyAlertIdEntropySrcFatalAlert] =
        {.id = kTopEarlgreyAlertIdEntropySrcFatalAlert,
         .name = "entropy_src_fatal_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceEntropySrc,
         .base_addr = TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR,
         .force_func = force_entropy_src_alert,
         .deassert_func = deassert_entropy_src_alert,
         .skip_test = false,
         .module_alert_type.entropy_src_alert = kDifEntropySrcAlertFatalAlert},
    [kTopEarlgreyAlertIdEdn0RecovAlert] =
        {.id = kTopEarlgreyAlertIdEdn0RecovAlert,
         .name = "edn0_recov_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceEdn0,
         .base_addr = TOP_EARLGREY_EDN0_BASE_ADDR,
         .force_func = force_edn_alert,
         .deassert_func = deassert_edn_alert,
         .skip_test = false,
         .module_alert_type.edn_alert = kDifEdnAlertRecovAlert},
    [kTopEarlgreyAlertIdEdn0FatalAlert] =
        {.id = kTopEarlgreyAlertIdEdn0FatalAlert,
         .name = "edn0_fatal_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceEdn0,
         .base_addr = TOP_EARLGREY_EDN0_BASE_ADDR,
         .force_func = force_edn_alert,
         .deassert_func = deassert_edn_alert,
         .skip_test = false,
         .module_alert_type.edn_alert = kDifEdnAlertFatalAlert},
    [kTopEarlgreyAlertIdEdn1RecovAlert] =
        {.id = kTopEarlgreyAlertIdEdn1RecovAlert,
         .name = "edn1_recov_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceEdn1,
         .base_addr = TOP_EARLGREY_EDN1_BASE_ADDR,
         .force_func = force_edn_alert,
         .deassert_func = deassert_edn_alert,
         .skip_test = false,
         .module_alert_type.edn_alert = kDifEdnAlertRecovAlert},
    [kTopEarlgreyAlertIdEdn1FatalAlert] =
        {.id = kTopEarlgreyAlertIdEdn1FatalAlert,
         .name = "edn1_fatal_alert",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceEdn1,
         .base_addr = TOP_EARLGREY_EDN1_BASE_ADDR,
         .force_func = force_edn_alert,
         .deassert_func = deassert_edn_alert,
         .skip_test = false,
         .module_alert_type.edn_alert = kDifEdnAlertFatalAlert},
    [kTopEarlgreyAlertIdSramCtrlMainFatalError] =
        {.id = kTopEarlgreyAlertIdSramCtrlMainFatalError,
         .name = "sram_ctrl_main_fatal_error",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceSramCtrlMain,
         .base_addr = TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR,
         .force_func = force_sram_ctrl_main_alert,
         .deassert_func = deassert_sram_ctrl_main_alert,
         .skip_test = false,
         .module_alert_type.sram_ctrl_alert = kDifSramCtrlAlertFatalError},
    [kTopEarlgreyAlertIdRomCtrlFatal] =
        {.id = kTopEarlgreyAlertIdRomCtrlFatal,
         .name = "rom_ctrl_fatal",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceRomCtrl,
         .base_addr = TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR,
         .force_func = force_rom_ctrl_alert,
         .deassert_func = deassert_rom_ctrl_alert,
         .skip_test = false,
         .module_alert_type.rom_ctrl_alert = kDifRomCtrlAlertFatal},
    [kTopEarlgreyAlertIdRvCoreIbexFatalSwErr] =
        {.id = kTopEarlgreyAlertIdRvCoreIbexFatalSwErr,
         .name = "rv_core_ibex_fatal_sw_err",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceRvCoreIbex,
         .base_addr = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR,
         .force_func = force_rv_core_ibex_alert,
         .deassert_func = deassert_rv_core_ibex_alert,
         .skip_test = false,
         .module_alert_type.rv_core_ibex_alert = kDifRvCoreIbexAlertFatalSwErr},
    [kTopEarlgreyAlertIdRvCoreIbexRecovSwErr] =
        {.id = kTopEarlgreyAlertIdRvCoreIbexRecovSwErr,
         .name = "rv_core_ibex_recov_sw_err",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceRvCoreIbex,
         .base_addr = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR,
         .force_func = force_rv_core_ibex_alert,
         .deassert_func = deassert_rv_core_ibex_alert,
         .skip_test = false,
         .module_alert_type.rv_core_ibex_alert = kDifRvCoreIbexAlertRecovSwErr},
    [kTopEarlgreyAlertIdRvCoreIbexFatalHwErr] =
        {.id = kTopEarlgreyAlertIdRvCoreIbexFatalHwErr,
         .name = "rv_core_ibex_fatal_hw_err",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceRvCoreIbex,
         .base_addr = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR,
         .force_func = force_rv_core_ibex_alert,
         .deassert_func = deassert_rv_core_ibex_alert,
         .skip_test = false,
         .module_alert_type.rv_core_ibex_alert = kDifRvCoreIbexAlertFatalHwErr},
    [kTopEarlgreyAlertIdRvCoreIbexRecovHwErr] =
        {.id = kTopEarlgreyAlertIdRvCoreIbexRecovHwErr,
         .name = "rv_core_ibex_recov_hw_err",
         .recommended_class = kDifAlertHandlerClassA,
         .source_type = kAlertSourceRvCoreIbex,
         .base_addr = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR,
         .force_func = force_rv_core_ibex_alert,
         .deassert_func = deassert_rv_core_ibex_alert,
         .skip_test = false,
         .module_alert_type.rv_core_ibex_alert = kDifRvCoreIbexAlertRecovHwErr},
};

// Overridden external interrupt handler. Claims PLIC interrupts,
// checks if they originate from the Alert Handler, and if so,
// identifies which alert(s) caused the interrupt, acknowledges them,
// and sets plic_irq_fired if it matches the expected serviced_alert
// global variable.
void ottf_external_isr(uint32_t *exc_info) {
  (void)exc_info;
  if (isr_counter >= MAX_ISR_EXECUTIONS)
    return;
  isr_counter++;
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                     &plic_irq_id));
  dif_alert_handler_class_t ack_class;
  if (plic_irq_id >= kTopEarlgreyPlicIrqIdAlertHandlerClassa &&
      plic_irq_id <= kTopEarlgreyPlicIrqIdAlertHandlerClassd) {
    ack_class =
        (dif_alert_handler_class_t)(plic_irq_id -
                                    kTopEarlgreyPlicIrqIdAlertHandlerClassa);
    LOG_INFO("ISR: Alert Handler IRQ detected for PLIC ID %d (Class %d)",
             plic_irq_id, ack_class);
    CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
        &alert_handler, (dif_alert_handler_irq_t)ack_class,
        kDifToggleDisabled));
    bool alert_found = false;
    for (top_earlgrey_alert_id_t id = 0; id <= kTopEarlgreyAlertIdLast; ++id) {
      bool is_cause = false;
      if (dif_alert_handler_alert_is_cause(&alert_handler, id, &is_cause) ==
              kDifOk &&
          is_cause) {
        CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(&alert_handler, id));
        if (id == serviced_alert) {
          plic_irq_fired = true;
        }
        alert_found = true;
      }
    }
    if (!alert_found) {
      LOG_WARNING(
          "ISR: Claimed Class %d IRQ, but no alert cause bits were set.",
          ack_class);
    }
  } else {
    LOG_ERROR("ISR: Unexpected PLIC IRQ ID: %d", plic_irq_id);
  }
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                        plic_irq_id));
}

// Initializes all required peripheral DIF handles
static void initialize_peripherals(void) {
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &rv_plic));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart0));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART1_BASE_ADDR), &uart1));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART2_BASE_ADDR), &uart2));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART3_BASE_ADDR), &uart3));
  CHECK_DIF_OK(dif_spi_device_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spi_device));
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR), &i2c0));
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C1_BASE_ADDR), &i2c1));
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C2_BASE_ADDR), &i2c2));
  CHECK_DIF_OK(dif_pattgen_init(
      mmio_region_from_addr(TOP_EARLGREY_PATTGEN_BASE_ADDR), &pattgen));
  CHECK_DIF_OK(dif_rv_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR), &rv_timer));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR), &lc_ctrl));
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR), &spi_host0));
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST1_BASE_ADDR), &spi_host1));
  CHECK_DIF_OK(dif_usbdev_init(
      mmio_region_from_addr(TOP_EARLGREY_USBDEV_BASE_ADDR), &usbdev));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr_aon));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr_aon));
  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr_aon));
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl_aon));
  CHECK_DIF_OK(dif_adc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR),
      &adc_ctrl_aon));
  CHECK_DIF_OK(dif_pwm_init(
      mmio_region_from_addr(TOP_EARLGREY_PWM_AON_BASE_ADDR), &pwm_aon));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux_aon));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR),
      &aon_timer_aon));
  CHECK_DIF_OK(dif_sensor_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR),
      &sensor_ctrl_aon));
  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR),
      &sram_ctrl_ret_aon));
  CHECK_DIF_OK(dif_flash_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR),
      &flash_ctrl));
  CHECK_DIF_OK(dif_rv_dm_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_DM_REGS_BASE_ADDR), &rv_dm));
  CHECK_DIF_OK(
      dif_rv_plic_init(mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR),
                       &rv_plic_for_alert));
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(
      dif_hmac_init(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac));
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  CHECK_DIF_OK(dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR),
                             &otbn_alert));
  CHECK_DIF_OK(dif_keymgr_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), &keymgr_alert));
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng_alert));
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR),
      &entropy_src_alert));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn0));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn1));
  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR),
      &sram_ctrl_main));
  CHECK_DIF_OK(dif_rom_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR), &rom_ctrl));
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));
}

// Verifies that no alerts are
// unexpectedly asserted after a Power-On Reset.
static void check_alert_all_active_defaults(void) {
  for (top_earlgrey_alert_id_t alert_id = 0;
       alert_id < ALERT_HANDLER_PARAM_N_ALERTS; ++alert_id) {
    const alert_config_t *config = &kAlertConfigs[alert_id];
    if (config->name == NULL)
      continue;
#if FPGA_TARGET
    if (config->id == kTopEarlgreyAlertIdFlashCtrlFatalErr) {
      LOG_INFO("Skipping flash_ctrl_fatal_err on FPGA target.");
      continue;
    }
#endif
    bool is_cause = false;
    CHECK_DIF_OK(
        dif_alert_handler_alert_is_cause(&alert_handler, alert_id, &is_cause));
    if (is_cause) {
      LOG_WARNING("Alert %d (%s) unexpectedly asserted in All-Active state.",
                  alert_id, config->name);
      CHECK_DIF_OK(
          dif_alert_handler_alert_acknowledge(&alert_handler, alert_id));
    } else {
      // LOG_INFO("Alert %d (%s) correctly inactive", alert_id, config->name);
    }
  }
  LOG_INFO("All-Active Alert Verification complete.");
}

typedef struct system_debug_info {
  dif_pwrmgr_wakeup_reason_t pwrmgr_wakeup_reason;
  uint32_t pwrmgr_wake_info_val;
  uint32_t pwrmgr_control_reg_val;
  dif_rstmgr_reset_info_bitfield_t rstmgr_reset_info;
  uint32_t rstmgr_alert_info;
  uint32_t alert_handler_esc_cnt;
  bool alert_handler_current_alert_is_cause;
  uint32_t alert_handler_intr_state;
  uint32_t clkmgr_recov_err_code;
  uint32_t plic_intr_pending_val;
  uint32_t plic_intr_enable_val;
} system_debug_info_t;

//  Logs various system and peripheral status registers
//  for debugging purposes, including RSTMGR, PWRMGR,
//  Alert Handler, PLIC, and CLKMGR. Takes the boot time
//  reset_info as an argument.
static void capture_and_log_debug_info(
    const char *label, top_earlgrey_alert_id_t current_alert_id) {
  const alert_config_t *config = &kAlertConfigs[current_alert_id];
  LOG_INFO("--- Capturing Debug Info for alert %d (%s): %s ---",
           current_alert_id, config->name, label);
  system_debug_info_t debug_info;
  CHECK_DIF_OK(
      dif_rstmgr_reset_info_get(&rstmgr, &debug_info.rstmgr_reset_info));
  LOG_INFO("  RSTMGR Reset Info: 0x%x", debug_info.rstmgr_reset_info);
  debug_info.rstmgr_alert_info = mmio_region_read32(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR),
      RSTMGR_ALERT_INFO_REG_OFFSET);
  LOG_INFO("  RSTMGR Alert Info: 0x%x", debug_info.rstmgr_alert_info);
  CHECK_DIF_OK(
      dif_pwrmgr_wakeup_reason_get(&pwrmgr, &debug_info.pwrmgr_wakeup_reason));
  LOG_INFO("  PWRMGR Wakeup Reasons: types=0x%x, sources=0x%x",
           debug_info.pwrmgr_wakeup_reason.types,
           debug_info.pwrmgr_wakeup_reason.request_sources);
  debug_info.pwrmgr_wake_info_val = mmio_region_read32(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR),
      PWRMGR_WAKE_INFO_REG_OFFSET);
  LOG_INFO("  PWRMGR WAKE_INFO: 0x%x (FallThrough=%d, Abort=%d)",
           debug_info.pwrmgr_wake_info_val,
           bitfield_bit32_read(debug_info.pwrmgr_wake_info_val,
                               PWRMGR_WAKE_INFO_FALL_THROUGH_BIT),
           bitfield_bit32_read(debug_info.pwrmgr_wake_info_val,
                               PWRMGR_WAKE_INFO_ABORT_BIT));
  debug_info.pwrmgr_control_reg_val = mmio_region_read32(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR),
      PWRMGR_CONTROL_REG_OFFSET);
  LOG_INFO("  PWRMGR CONTROL: 0x%x (LowPowerHint=%d, IOClockEn=%d)",
           debug_info.pwrmgr_control_reg_val,
           bitfield_bit32_read(debug_info.pwrmgr_control_reg_val,
                               PWRMGR_CONTROL_LOW_POWER_HINT_BIT),
           bitfield_bit32_read(debug_info.pwrmgr_control_reg_val,
                               PWRMGR_CONTROL_IO_CLK_EN_BIT));
  ptrdiff_t esc_cnt_reg;
  switch (config->recommended_class) {
    case kDifAlertHandlerClassA:
      esc_cnt_reg = ALERT_HANDLER_CLASSA_ESC_CNT_REG_OFFSET;
      break;
    case kDifAlertHandlerClassB:
      esc_cnt_reg = ALERT_HANDLER_CLASSB_ESC_CNT_REG_OFFSET;
      break;
    case kDifAlertHandlerClassC:
      esc_cnt_reg = ALERT_HANDLER_CLASSC_ESC_CNT_REG_OFFSET;
      break;
    case kDifAlertHandlerClassD:
      esc_cnt_reg = ALERT_HANDLER_CLASSD_ESC_CNT_REG_OFFSET;
      break;
    default:
      esc_cnt_reg = 0;
  }
  if (esc_cnt_reg != 0) {
    debug_info.alert_handler_esc_cnt =
        mmio_region_read32(alert_handler.base_addr, esc_cnt_reg);
    LOG_INFO("  Alert Handler Class %d Escalation Counter: %u",
             config->recommended_class, debug_info.alert_handler_esc_cnt);
  }
  CHECK_DIF_OK(dif_alert_handler_alert_is_cause(
      &alert_handler, current_alert_id,
      &debug_info.alert_handler_current_alert_is_cause));
  LOG_INFO("  Alert Handler Alert %d (%s) is cause: %s", current_alert_id,
           config->name,
           debug_info.alert_handler_current_alert_is_cause ? "yes" : "no");
  debug_info.alert_handler_intr_state = mmio_region_read32(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      ALERT_HANDLER_INTR_STATE_REG_OFFSET);
  LOG_INFO("  Alert Handler INTR_STATE: 0x%x",
           debug_info.alert_handler_intr_state);
  dif_rv_plic_irq_id_t irq_id;
  if (config->recommended_class == kDifAlertHandlerClassA) {
    irq_id = kTopEarlgreyPlicIrqIdAlertHandlerClassa;
  } else if (config->recommended_class == kDifAlertHandlerClassB) {
    irq_id = kTopEarlgreyPlicIrqIdAlertHandlerClassb;
  } else if (config->recommended_class == kDifAlertHandlerClassC) {
    irq_id = kTopEarlgreyPlicIrqIdAlertHandlerClassc;
  } else {
    irq_id = kTopEarlgreyPlicIrqIdAlertHandlerClassd;
  }
  uint32_t reg_idx = (uint32_t)irq_id / 32;
  uint32_t bit_idx = (uint32_t)irq_id % 32;
  ptrdiff_t ie_reg_offset = RV_PLIC_IE0_0_REG_OFFSET + (ptrdiff_t)reg_idx * 4;
  ptrdiff_t ip_reg_offset = RV_PLIC_IP_0_REG_OFFSET + (ptrdiff_t)reg_idx * 4;
  debug_info.plic_intr_enable_val = mmio_region_read32(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), ie_reg_offset);
  LOG_INFO("  PLIC IE for IRQ %d (Reg %d): 0x%x (Bit %d is %d)", irq_id,
           reg_idx, debug_info.plic_intr_enable_val, bit_idx,
           bitfield_bit32_read(debug_info.plic_intr_enable_val, bit_idx));
  debug_info.plic_intr_pending_val = mmio_region_read32(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), ip_reg_offset);
  LOG_INFO("  PLIC IP for IRQ %d (Reg %d): 0x%x (Bit %d is %d)", irq_id,
           reg_idx, debug_info.plic_intr_pending_val, bit_idx,
           bitfield_bit32_read(debug_info.plic_intr_pending_val, bit_idx));
  debug_info.clkmgr_recov_err_code = mmio_region_read32(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR),
      CLKMGR_RECOV_ERR_CODE_REG_OFFSET);
  LOG_INFO("  CLKMGR Recoverable Error Code: 0x%x",
           debug_info.clkmgr_recov_err_code);
  LOG_INFO("--- Debug Info Capture Complete ---");
}

// Enables the PLIC interrupt for a specific alert handler class.
void enable_alert_handler_class_irq(dif_alert_handler_class_t class_to_enable) {
  dif_rv_plic_irq_id_t irq_id;
  if (class_to_enable == kDifAlertHandlerClassA) {
    irq_id = kTopEarlgreyPlicIrqIdAlertHandlerClassa;
  } else if (class_to_enable == kDifAlertHandlerClassB) {
    irq_id = kTopEarlgreyPlicIrqIdAlertHandlerClassb;
  } else if (class_to_enable == kDifAlertHandlerClassC) {
    irq_id = kTopEarlgreyPlicIrqIdAlertHandlerClassc;
  } else if (class_to_enable == kDifAlertHandlerClassD) {
    irq_id = kTopEarlgreyPlicIrqIdAlertHandlerClassd;
  } else {
    LOG_ERROR("Invalid alert class: %d", class_to_enable);
    return;
  }
  const dif_rv_plic_target_t target = kTopEarlgreyPlicTargetIbex0;
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&rv_plic, target, 0));
  rv_plic_testutils_irq_range_enable(&rv_plic, target, irq_id, irq_id);
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&rv_plic, irq_id, 1));
  LOG_INFO("Enabled PLIC interrupt for Alert Handler Class %d (IRQ ID: %d)",
           class_to_enable, irq_id);
}

// Calls the appropriate peripheral-specific de-assertion function
// based on the alert_config_t.
static void deassert_alert_source(const alert_config_t *config) {
  if (config->deassert_func) {
    config->deassert_func(config);
  } else {
    LOG_WARNING("De-assert function not set for %s", config->name);
  }
}

// De-asserts the alert at the source, pulses the alert class
// clear register, waits for the class state to return to IDLE,
// and disables the alert in the alert handler.
// Includes watchdog trigger after cleanup fails.
static void cleanup_after_alert(const alert_config_t *config,
                                uint32_t current_test_phase) {
  top_earlgrey_alert_id_t alert_id = config->id;
  dif_alert_handler_class_t alert_class = config->recommended_class;
  LOG_INFO("Starting cleanup for alert ID %d (%s) in phase 0x%x...", alert_id,
           config->name, current_test_phase);

  // Step 1: De-assert the alert at the source peripheral.
  deassert_alert_source(config);
  busy_spin_micros(10);

  // Step 1a: VERIFY that the alert was de-asserted.
  bool still_cause = true;
  for (int i = 0; i < 100; ++i) {
    CHECK_DIF_OK(dif_alert_handler_alert_is_cause(&alert_handler, alert_id,
                                                  &still_cause));
    if (!still_cause)
      break;
    busy_spin_micros(1);
  }
  CHECK(!still_cause, "Alert ID %d (%s) source de-assertion failed!", alert_id,
        config->name);
  LOG_INFO("DE-ASSERT OK: Alert ID %d (%s) source de-asserted.", alert_id,
           config->name);

  // Determine register offsets based on the class
  ptrdiff_t class_clr_reg;
  ptrdiff_t class_state_reg;
  uint32_t idle_state_val;
  uint32_t class_state_mask;

  switch (alert_class) {
    case kDifAlertHandlerClassA:
      class_clr_reg = ALERT_HANDLER_CLASSA_CLR_SHADOWED_REG_OFFSET;
      class_state_reg = ALERT_HANDLER_CLASSA_STATE_REG_OFFSET;
      idle_state_val = ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_IDLE;
      class_state_mask = ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_MASK;
      break;
    case kDifAlertHandlerClassB:
      class_clr_reg = ALERT_HANDLER_CLASSB_CLR_SHADOWED_REG_OFFSET;
      class_state_reg = ALERT_HANDLER_CLASSB_STATE_REG_OFFSET;
      idle_state_val = ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_VALUE_IDLE;
      class_state_mask = ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_MASK;
      break;
    case kDifAlertHandlerClassC:
      class_clr_reg = ALERT_HANDLER_CLASSC_CLR_SHADOWED_REG_OFFSET;
      class_state_reg = ALERT_HANDLER_CLASSC_STATE_REG_OFFSET;
      idle_state_val = ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_VALUE_IDLE;
      class_state_mask = ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_MASK;
      break;
    case kDifAlertHandlerClassD:
      class_clr_reg = ALERT_HANDLER_CLASSD_CLR_SHADOWED_REG_OFFSET;
      class_state_reg = ALERT_HANDLER_CLASSD_STATE_REG_OFFSET;
      idle_state_val = ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_VALUE_IDLE;
      class_state_mask = ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_MASK;
      break;
    default:
      LOG_FATAL("Invalid alert class: %d", alert_class);
      return;
  }

  uint32_t state_val =
      mmio_region_read32(alert_handler.base_addr, class_state_reg) &
      class_state_mask;
  if (current_test_phase == TEST_PHASE_ALL_ACTIVE_IRQ) {
    // 1. Attempt to clear with the INCORRECT method (single write)
    LOG_INFO(
        "Attempting to clear class %d with single write (expected to fail)...",
        alert_class);
    mmio_region_write32(alert_handler.base_addr, class_clr_reg, 1u);
    busy_spin_micros(10);  // Give it time to potentially (not) take effect

    state_val = mmio_region_read32(alert_handler.base_addr, class_state_reg) &
                class_state_mask;
    CHECK(state_val != idle_state_val,
          "Class %d cleared with a single write! Shadowing failed!",
          alert_class);
    LOG_INFO("OK: Class %d state did not change with a single write.",
             alert_class);

    // 2. Clear with the CORRECT method (shadowed write)
    LOG_INFO("Clearing class %d with shadowed write...", alert_class);
    mmio_region_write32_shadowed(alert_handler.base_addr, class_clr_reg, 1u);
    busy_spin_micros(10);

    // 3. Verify the state is now IDLE
    bool cleared_to_idle = false;
    for (int i = 0; i < 1000; ++i) {
      state_val = mmio_region_read32(alert_handler.base_addr, class_state_reg);
      if ((state_val & class_state_mask) == idle_state_val) {
        cleared_to_idle = true;
        break;
      }
      busy_spin_micros(1);
    }
    CHECK(cleared_to_idle,
          "Alert class %d (Alert ID %d) did NOT clear to IDLE after shadowed "
          "write!",
          alert_class, alert_id);
    LOG_INFO("OK: Alert class %d (Alert ID %d) cleared to IDLE as expected.",
             alert_class, alert_id);

    // In the IRQ phase, trigger a watchdog reset to move to the next alert.
    uint32_t next_alert_id_to_save = alert_id;
    do {
      // Find the next valid alert ID.
      next_alert_id_to_save++;
    } while (next_alert_id_to_save < ALERT_HANDLER_PARAM_N_ALERTS &&
             kAlertConfigs[next_alert_id_to_save].name == NULL);

    LOG_INFO(
        "Saving next alert ID %d to retention SRAM. Triggering watchdog...",
        next_alert_id_to_save);
    CHECK_STATUS_OK(ret_sram_testutils_counter_set(
        RET_SRAM_SLOT_ALL_ACTIVE_IRQ_IDX, next_alert_id_to_save));
    CHECK_DIF_OK(dif_aon_timer_watchdog_start(&aon_timer, 2, 4, false, false));
    while (true) {
    };
  } else if (current_test_phase == TEST_PHASE_ALL_ACTIVE_RESET) {
    // In RESET Phase, the class state SHOULD ALREADY BE IDLE due to the HW
    // reset.
    CHECK(state_val == idle_state_val,
          "RESET Phase (Alert ID %d, Class %d): Alert Handler Class state is "
          "NOT IDLE after hardware reset! State: %u",
          alert_id, alert_class, state_val);
    LOG_INFO(
        "RESET Phase (Alert ID %d, Class %d): Alert Handler Class is IDLE as "
        "expected.",
        alert_id, alert_class);
  } else {
    LOG_FATAL("cleanup_after_alert called with unknown test phase: 0x%x",
              current_test_phase);
  }

  CHECK_DIF_OK(dif_alert_handler_configure_alert(
      &alert_handler, alert_id, alert_class, kDifToggleDisabled,
      kDifToggleDisabled));
  LOG_INFO("Cleanup complete for alert %d (%s)", alert_id, config->name);
}

// While being in All Active state, loops through alerts, enables one,
// forces it, enters WFI, and verifies wakeup via ISR
static void check_alert_all_active_irq(uint32_t start_alert_id) {
  LOG_INFO("Phase 1:ALL ACTIVE IRQ (AAIP): Testing alerts with WFI - Start");
  irq_global_ctrl(true);

  for (uint32_t i = start_alert_id; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    const alert_config_t *config = &kAlertConfigs[i];
    if (config->name == NULL)
      continue;
    if (config->skip_test) {
      LOG_INFO("Skipping alert %d (%s) as it is marked to be skipped.",
               config->id, config->name);
      continue;
    }

    top_earlgrey_alert_id_t alert_id = config->id;
    dif_alert_handler_class_t recommended_alert_class =
        config->recommended_class;

    serviced_alert = alert_id;
    plic_irq_fired = false;
    isr_counter = 0;

    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        &alert_handler, alert_id, recommended_alert_class, kDifToggleEnabled,
        kDifToggleEnabled));
    CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(&alert_handler, alert_id));
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_clear(&pwrmgr));

    enable_alert_handler_class_irq(recommended_alert_class);
    CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
        &alert_handler, (dif_alert_handler_irq_t)recommended_alert_class,
        kDifToggleEnabled));

    irq_global_ctrl(false);
    irq_external_ctrl(true);

    LOG_INFO("Forcing alert %d (%s)...", alert_id, config->name);
    void *dif_handle = get_peripheral_dif_handle(config);
    // Ensure dif_handle is not NULL (handle unknown source types gracefully)
    if (dif_handle == NULL) {
      LOG_FATAL("Failed to get DIF handle for alert %d (%s). Skipping test.",
                alert_id, config->name);
      continue;
    }

    CHECK_DIF_OK(config->force_func(dif_handle, config));

    wait_for_interrupt();
    irq_global_ctrl(true);
    busy_spin_micros(10);

    if (plic_irq_fired) {
      LOG_INFO("Alert %d (%s) IRQ fired as expected", alert_id, config->name);
    } else {
      LOG_ERROR("Alert %d (%s) IRQ did NOT fire", alert_id, config->name);
    }

    cleanup_after_alert(config, TEST_PHASE_ALL_ACTIVE_IRQ);
  }
  LOG_INFO("Phase 1: ALL ACTIVE IRQ (AAIP) - Complete");
}

//
static void prepare_for_all_active_irq(void) {
  const dif_alert_handler_escalation_phase_t kSimpleEscPhases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = 10000},
  };

  const dif_alert_handler_class_config_t kSimpleClassConfig = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = 0,
      .escalation_phases = kSimpleEscPhases,
      .escalation_phases_len = ARRAYSIZE(kSimpleEscPhases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase0,
  };

  // Configure all classes (A, B, C, D) with the simple, non-escalating config
  for (dif_alert_handler_class_t alert_class = kDifAlertHandlerClassA;
       alert_class <= kDifAlertHandlerClassD; ++alert_class) {
    CHECK_DIF_OK(dif_alert_handler_configure_class(
        &alert_handler, alert_class, kSimpleClassConfig, kDifToggleEnabled,
        kDifToggleDisabled));
  }
  LOG_INFO(
      "Peripherals and all Alert Handler Classes (A, B, C, D) initialized "
      "successfully");
}

//
static void prepare_for_all_active_reset(void) {
  const dif_alert_handler_escalation_phase_t kEscResetPhase[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = 1000},
      {.phase = kDifAlertHandlerClassStatePhase1,
       .signal = 1,
       .duration_cycles = 1000},
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 3,
       .duration_cycles = 100},
  };
  const dif_alert_handler_class_config_t kResetConfig = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = 0,
      .escalation_phases = kEscResetPhase,
      .escalation_phases_len = ARRAYSIZE(kEscResetPhase),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  // Configure all classes (A, B, C, D) with the reset escalation config
  for (dif_alert_handler_class_t alert_class = kDifAlertHandlerClassA;
       alert_class <= kDifAlertHandlerClassD; ++alert_class) {
    CHECK_DIF_OK(dif_alert_handler_configure_class(
        &alert_handler, alert_class, kResetConfig, kDifToggleEnabled,
        kDifToggleDisabled));
  }
}

// Parses and logs the individual bits set within the
// alert_cause fields of the raw RSTMGR alert dump segments.
static void log_alert_cause_bits(
    const dif_rstmgr_alert_info_dump_segment_t *dump, size_t segments_read) {
  if (segments_read < 7) {
    LOG_INFO(" DEBUG: Not enough segments to fully decode alert_cause.");
    return;
  }

  // alert_cause starts at bit 211
  // Segment 6: bits 19-31 for alert_cause[0-12]
  // Segment 7: bits 0-31 for alert_cause[13-44]
  // Segment 8: bits 0-31 for alert_cause[45-76] (only need up to 64)

  uint32_t seg6 = dump[6];
  LOG_INFO("   DEBUG: Seg[6] 0x%08x:", seg6);
  for (int i = 0; i <= 12; ++i) {
    if ((seg6 >> (19 + i)) & 1) {
      LOG_INFO("     DEBUG: alert_cause[%d] (bit %d) = 1", i, 19 + i);
    }
  }

  if (segments_read > 7) {
    uint32_t seg7 = dump[7];
    LOG_INFO("  Seg[7] 0x%08x:", seg7);
    for (int i = 0; i <= 31; ++i) {
      if ((seg7 >> i) & 1) {
        LOG_INFO("     DEBUG: alert_cause[%d] (bit %d) = 1", 13 + i, i);
      }
    }
  }

  if (segments_read > 8) {
    uint32_t seg8 = dump[8];
    LOG_INFO("  Seg[8] 0x%08x:", seg8);
    for (int i = 0; i <= 19; ++i) {
      if ((seg8 >> i) & 1) {
        LOG_INFO("     DEBUG: alert_cause[%d] (bit %d) = 1", 45 + i, i);
      }
    }
  }
}

// Checks the rstmgr registers to confirm a reset was caused by the alert
// handler.
static void check_reset_and_alert_info(
    dif_rstmgr_reset_info_bitfield_t reset_info, uint32_t expected_alert_id) {
  // After a reset from All Active Reset Phase (AARP), we expect the cause to
  // be a hardware request.
  CHECK((reset_info & kDifRstmgrResetInfoHwReq) != 0,
        "Reset reason was not a hardware request. Got 0x%x", reset_info);
  LOG_INFO(
      ">> ALL ACTIVE RESET PHASE (AARP) CHECK: Reset reason includes Hardware "
      "Request (0x%x), as "
      "expected.",
      reset_info);

  // Read the alert info dump from RSTMGR
  dif_rstmgr_alert_info_dump_segment_t dump[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];
  size_t segments_read;
  dif_result_t read_res = dif_rstmgr_alert_info_dump_read(
      &rstmgr, dump, DIF_RSTMGR_ALERT_INFO_MAX_SIZE, &segments_read);
  CHECK_DIF_OK(read_res);

  // Log the bit-level details for alert_cause
  log_alert_cause_bits(dump, segments_read);

  if (segments_read > 0) {
    // Parse the dump information
    alert_handler_testutils_info_t actual_info;
    status_t parse_status = alert_handler_testutils_info_parse(
        dump, (int)segments_read, &actual_info);
    CHECK_STATUS_OK(parse_status);

    LOG_INFO(
        ">> ALL ACTIVE RESET PHASE (AARP) CHECK: Parsed Alert Dump Info "
        "Values:");
    alert_handler_testutils_info_dump(&actual_info);

    // Check if the expected alert ID is in the alert_cause array
    if (expected_alert_id < ALERT_HANDLER_PARAM_N_ALERTS) {
      CHECK(actual_info.alert_cause[expected_alert_id],
            "Expected alert ID %d NOT found in dump's alert_cause array.",
            expected_alert_id);
      LOG_INFO(
          ">> ALL ACTIVE RESET PHASE (AARP) CHECK: SUCCESS: Expected alert ID "
          "%d found in dump.",
          expected_alert_id);
    } else {
      LOG_FATAL(
          ">> ALL ACTIVE RESET PHASE (AARP) CHECK: Expected alert ID %d is "
          "out of bounds for "
          "alert_cause array.",
          expected_alert_id);
    }

    // Check for any other alerts
    int other_alerts = 0;
    for (int i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
      if (i != expected_alert_id && actual_info.alert_cause[i]) {
        LOG_WARNING(
            ">> ALL ACTIVE RESET PHASE (AARP) CHECK: Unexpected alert ID %d "
            "also found in dump.",
            i);
        other_alerts++;
      }
    }
    if (other_alerts == 0 && actual_info.alert_cause[expected_alert_id]) {
      LOG_INFO(
          ">> ALL ACTIVE RESET PHASE (AARP) CHECK: No other unexpected alerts "
          "found in dump.");
    }
  } else {
    LOG_WARNING(
        ">> ALL ACTIVE RESET PHASE (AARP) CHECK: No alert info dump segments "
        "were read from "
        "rstmgr.");
    CHECK(false, "Alert info dump was expected but not found.");
  }
}

// Configures the alert for reset escalation, prepares RSTMGR, configures
// for All Active Reset Phase (AARP) test, forces the alert, and then spins,
// expecting a system reset.
static void check_alert_all_active_reset(uint32_t alert_id) {
  const alert_config_t *config = &kAlertConfigs[alert_id];

  if (config->skip_test) {
    LOG_INFO(
        "Skipping alert %d (%s) in RESET phase as it is marked to be skipped.",
        config->id, config->name);
    // Find the next valid alert ID to test, skipping the current one.
    uint32_t next_alert_id_to_save = alert_id;
    do {
      next_alert_id_to_save++;
    } while (next_alert_id_to_save < ALERT_HANDLER_PARAM_N_ALERTS &&
             kAlertConfigs[next_alert_id_to_save].name == NULL);
    CHECK_STATUS_OK(ret_sram_testutils_counter_set(
        RET_SRAM_SLOT_ALL_ACTIVE_RESET_IDX, next_alert_id_to_save));
    return;
  }

  CHECK_DIF_OK(dif_alert_handler_configure_alert(
      &alert_handler, alert_id, config->recommended_class, kDifToggleEnabled,
      kDifToggleEnabled));

  CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));
  LOG_INFO(">> ALL ACTIVE RESET PHASE (AARP); Prepared rstmgr for reset");

  LOG_INFO(">> ALL ACTIVE RESET PHASE (AARP): Getting dif_handle for alert %d",
           alert_id);
  void *dif_handle = get_peripheral_dif_handle(config);
  // Ensure dif_handle is not NULL (handle unknown source types gracefully)
  if (dif_handle == NULL) {
    LOG_FATAL(
        ">> ALL ACTIVE RESET PHASE (AARP):Failed to get DIF handle for alert "
        "%d (%s). Skipping test.",
        alert_id, config->name);
    CHECK(false, "Failed to get peripheral DIF handle for reset phase test.");
    return;
  }

  LOG_INFO(
      ">> ALL ACTIVE RESET PHASE (AARP): PRE-CALL config->force_func for alert "
      "%d (%s)",
      alert_id, config->name);
  dif_result_t force_result = config->force_func(dif_handle, config);
  // Below logic will never execute and is expected
  LOG_INFO(
      ">> ALL ACTIVE RESET PHASE (AARP): POST-CALL config->force_func for "
      "alert %d, result=%d",
      alert_id, force_result);
  CHECK_DIF_OK(force_result);
  LOG_INFO(">> ALL ACTIVE RESET PHASE (AARP): Alert %d forced OK", alert_id);

  LOG_INFO(
      ">> ALL ACTIVE RESET PHASE (AARP): Spinning for 10ms, expecting reset "
      "from alert ID %d...",
      alert_id);
  busy_spin_micros(10000);

  LOG_ERROR("FAIL: Should have reset via alert handler escalation.");
  while (true) {
    // Spin
  }
}

//
bool test_main(void) {
  busy_spin_micros(1000);
  initialize_peripherals();

  dif_rstmgr_reset_info_bitfield_t reset_info = rstmgr_testutils_reason_get();
  LOG_INFO(">> TEST_MAIN: Start. Raw reset_info=0x%x", reset_info);

  uint32_t state_id = 0;
  CHECK_STATUS_OK(
      ret_sram_testutils_counter_get(RET_SRAM_SLOT_TEST_PHASE, &state_id));

  if (state_id != TEST_PHASE_ALL_ACTIVE_RESET) {
    // --- Phase 1: All-Active IRQ States --- //
    uint32_t next_alert_id = 0;

    if (state_id != TEST_PHASE_ALL_ACTIVE_IRQ ||
        (reset_info & kDifRstmgrResetInfoPor)) {
      LOG_INFO(">> TEST_MAIN: POR");
      rstmgr_testutils_reason_clear();
      CHECK_STATUS_OK(ret_sram_testutils_counter_set(
          RET_SRAM_SLOT_TEST_PHASE, TEST_PHASE_ALL_ACTIVE_IRQ));
      CHECK_STATUS_OK(
          ret_sram_testutils_counter_set(RET_SRAM_SLOT_ALL_ACTIVE_IRQ_IDX, 0));
      CHECK_STATUS_OK(ret_sram_testutils_counter_set(
          RET_SRAM_SLOT_ALL_ACTIVE_RESET_IDX, 0));

      if (reset_info & kDifRstmgrResetInfoPor) {
        LOG_INFO("Reset Reason: POR, Check alert for All Active state");
      } else {
        CHECK(false, "Reset Reason: Unknown, but state_id was invalid.");
      }
      check_alert_all_active_defaults();
    } else {
      // Watchdog reset
      CHECK_STATUS_OK(ret_sram_testutils_counter_get(
          RET_SRAM_SLOT_ALL_ACTIVE_IRQ_IDX, &next_alert_id));
      LOG_INFO(
          ">> TEST_MAIN: Resuming All Active IRQ Phase test from alert %d "
          "(Reset Info: "
          "0x%x)",
          next_alert_id, reset_info);
      if (reset_info & kDifRstmgrResetInfoWatchdog) {
        LOG_INFO(
            ">> TEST_MAIN: Watchdog reset detected, verifying all alert "
            "classes are IDLE.");
        for (dif_alert_handler_class_t alert_class = kDifAlertHandlerClassA;
             alert_class <= kDifAlertHandlerClassD; ++alert_class) {
          dif_alert_handler_class_state_t class_state;
          CHECK_DIF_OK(dif_alert_handler_get_class_state(
              &alert_handler, alert_class, &class_state));

          uint32_t idle_state_val;
          switch (alert_class) {
            case kDifAlertHandlerClassA:
              idle_state_val =
                  ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_IDLE;
              break;
            case kDifAlertHandlerClassB:
              idle_state_val =
                  ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_VALUE_IDLE;
              break;
            case kDifAlertHandlerClassC:
              idle_state_val =
                  ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_VALUE_IDLE;
              break;
            case kDifAlertHandlerClassD:
              idle_state_val =
                  ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_VALUE_IDLE;
              break;
            default:
              LOG_FATAL("Invalid alert class: %d", alert_class);
              return false;
          }
          CHECK(class_state == idle_state_val,
                "Class %d state not IDLE after watchdog reset! State: %d",
                alert_class, class_state);
        }
        LOG_INFO("  POST-WATCHDOG: All class states are IDLE as expected.");
      }
      rstmgr_testutils_reason_clear();
    }

    irq_global_ctrl(true);

    if (next_alert_id < ALERT_HANDLER_PARAM_N_ALERTS) {
      LOG_INFO(
          ">> TEST_MAIN: Starting/Resuming All Active IRQ Phase (AAIP) from "
          "alert %d.",
          next_alert_id);
      prepare_for_all_active_irq();
      check_alert_all_active_irq(next_alert_id);
    }

    // This point is reached only when the for loop in
    // check_alert_all_active_irq completes.
    LOG_INFO(
        ">> TEST_MAIN: ALL Active IRQ Phase (AAIP) complete. Setting state_id "
        "for All Active"
        "Reset Phase(AARP) test and resetting.");
    CHECK_STATUS_OK(ret_sram_testutils_counter_set(
        RET_SRAM_SLOT_TEST_PHASE, TEST_PHASE_ALL_ACTIVE_RESET));
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    // Loop forever until reset
    while (true) {
    }
  } else {
    // --- Phase 2: All Active Reset Phase (AARP) State --- //
    prepare_for_all_active_reset();

    uint32_t current_alert_id_from_sram = 0;
    // be tested
    CHECK_STATUS_OK(ret_sram_testutils_counter_get(
        RET_SRAM_SLOT_ALL_ACTIVE_RESET_IDX, &current_alert_id_from_sram));

    // Handle initial SW Reset or subsequent HW Request/Unexpected Reset
    if (reset_info & kDifRstmgrResetInfoSw) {
      LOG_INFO(
          ">> TEST_MAIN: Software reset detected. Starting All Active Reset "
          "Phase(AARP) from alert %d.",
          current_alert_id_from_sram);
      rstmgr_testutils_reason_clear();
      // current_alert_id_from_sram is already pointing to the first alert to be
      // *attempted* for testing.
    } else if (reset_info & kDifRstmgrResetInfoHwReq) {
      // This block is entered *after* a hardware reset has occurred,
      // meaning the *previous* alert caused the reset and needs verification.
      const alert_config_t *prev_alert_config =
          &kAlertConfigs[current_alert_id_from_sram];
      LOG_INFO(
          ">> TEST_MAIN: All Active Reset Phase(AARP) Reset HW reset detected. "
          "Verifying alert %d.",
          prev_alert_config->id);
      check_reset_and_alert_info(reset_info, prev_alert_config->id);
      rstmgr_testutils_reason_clear();

      cleanup_after_alert(prev_alert_config, TEST_PHASE_ALL_ACTIVE_RESET);

      // After verification and cleanup, advance the alert ID for the *next*
      // test.
      do {
        current_alert_id_from_sram++;
      } while (current_alert_id_from_sram < ALERT_HANDLER_PARAM_N_ALERTS &&
               kAlertConfigs[current_alert_id_from_sram].name == NULL);
      CHECK_STATUS_OK(ret_sram_testutils_counter_set(
          RET_SRAM_SLOT_ALL_ACTIVE_RESET_IDX, current_alert_id_from_sram));

    } else {
      LOG_FATAL(
          ">> TEST_MAIN: !! Unexpected reset during All Active Reset "
          "Phase(AARP): 0x%x, expected HW or SW",
          reset_info);
      rstmgr_testutils_reason_clear();
      return false;
    }

    // Now, having handled the reset reason and potentially updated
    // current_alert_id_from_sram: This loop processes alerts until all are
    // done, or a new reset is triggered.
    while (true) {
      // This loop manages the actual test execution and skipping
      // for the current boot
      // Find the next defined alert to test (skipping any undefined IDs)
      while (current_alert_id_from_sram < ALERT_HANDLER_PARAM_N_ALERTS &&
             kAlertConfigs[current_alert_id_from_sram].name == NULL) {
        current_alert_id_from_sram++;
      }

      // Check for test completion
      if (current_alert_id_from_sram >= ALERT_HANDLER_PARAM_N_ALERTS) {
        LOG_INFO(
            ">> TEST_MAIN: All Active Reset Phase(AARP) alert tests passed.");
        CHECK_STATUS_OK(
            ret_sram_testutils_counter_set(RET_SRAM_SLOT_TEST_PHASE, 0));
        return true;
      }

      const alert_config_t *config_to_test =
          &kAlertConfigs[current_alert_id_from_sram];

      // Handle skipping *before* attempting to trigger a reset
      if (config_to_test->skip_test) {
        LOG_INFO(
            "Skipping alert %d (%s) in RESET phase as it is marked to be "
            "skipped.",
            config_to_test->id, config_to_test->name);
        // Advance current_alert_id_from_sram (robustly) and save to SRAM for
        // the *next* iteration.
        do {
          current_alert_id_from_sram++;
        } while (current_alert_id_from_sram < ALERT_HANDLER_PARAM_N_ALERTS &&
                 kAlertConfigs[current_alert_id_from_sram].name == NULL);
        CHECK_STATUS_OK(ret_sram_testutils_counter_set(
            RET_SRAM_SLOT_ALL_ACTIVE_RESET_IDX, current_alert_id_from_sram));
        // After skipping and updating SRAM, immediately re-check for test
        // completion. If there are no more alerts, this loop will naturally
        // exit in the next iteration.
        continue;
      }

      // If not skipped, proceed to trigger the reset for this alert.
      check_alert_all_active_reset(config_to_test->id);

      // This point should NOT be reached if check_alert_all_active_reset
      // correctly triggers a HW reset. If it is reached, it implies the
      // hardware reset failed.
      LOG_FATAL(
          "FAIL: check_alert_all_active_reset for alert %d (%s) failed to "
          "trigger a hardware reset!",
          config_to_test->id, config_to_test->name);
      return false;
    }
  }
  return false;
}
