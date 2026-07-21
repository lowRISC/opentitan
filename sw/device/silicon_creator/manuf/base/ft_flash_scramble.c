// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdalign.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/macros.h"

#define PINMUX_MIO_OUTSEL_0_REG_OFFSET 0x288
#define GPIO_DIRECT_OE_REG_OFFSET 0x20
#define GPIO_DIRECT_OUT_REG_OFFSET 0x14
#define GPIO_MASKED_OUT_LOWER_REG_OFFSET 0x18

#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"
#include "sw/device/silicon_creator/manuf/lib/personalize_secret1.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

// ATE Indicator GPIOs.
static const uint32_t kGpioPinTestStart = 0;
static const uint32_t kGpioPinTestDone = 1;
static const uint32_t kGpioPinTestError = 2;

static void set_ate_indicator(uint32_t pin, bool value) {
  uint32_t data = value ? (1u << pin) : 0;
  abs_mmio_write32(
      TOP_EARLGREY_GPIO_BASE_ADDR + GPIO_MASKED_OUT_LOWER_REG_OFFSET,
      (1u << (pin + 16)) | data);
}

OTTF_DEFINE_TEST_CONFIG(.console.type = kOttfConsoleUart);

static const uint32_t kCreatorSwCfgFlashDataDefaultCfgValue = 0x00090606;

static status_t individualize_flash_data_default_cfg_check(void) {
  uint32_t val =
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG_OFFSET);
  return (val != 0) ? OK_STATUS() : INTERNAL();
}

static status_t individualize_flash_data_default_cfg_write(void) {
  TRY(otp_dai_write32(
      kOtpPartitionCreatorSwCfg,
      OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG_OFFSET -
          OTP_CTRL_PARAM_CREATOR_SW_CFG_OFFSET,
      kCreatorSwCfgFlashDataDefaultCfgValue));
  return OK_STATUS();
}

static status_t configure_ate_gpio_indicators(void) {
  abs_mmio_write32(TOP_EARLGREY_PINMUX_AON_BASE_ADDR +
                       PINMUX_MIO_OUTSEL_0_REG_OFFSET +
                       kTopEarlgreyPinmuxMioOutIoa0 * sizeof(uint32_t),
                   kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinTestError);
  abs_mmio_write32(TOP_EARLGREY_PINMUX_AON_BASE_ADDR +
                       PINMUX_MIO_OUTSEL_0_REG_OFFSET +
                       kTopEarlgreyPinmuxMioOutIoa1 * sizeof(uint32_t),
                   kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinTestDone);
  abs_mmio_write32(TOP_EARLGREY_PINMUX_AON_BASE_ADDR +
                       PINMUX_MIO_OUTSEL_0_REG_OFFSET +
                       kTopEarlgreyPinmuxMioOutIoa4 * sizeof(uint32_t),
                   kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinTestStart);
  abs_mmio_write32(TOP_EARLGREY_GPIO_BASE_ADDR + GPIO_DIRECT_OE_REG_OFFSET,
                   0x7);
  abs_mmio_write32(TOP_EARLGREY_GPIO_BASE_ADDR + GPIO_DIRECT_OUT_REG_OFFSET, 0);
  return OK_STATUS();
}

static status_t personalize_otp_and_flash_secrets(void) {
  if (!status_ok(manuf_personalize_device_secret1_check())) {
    TRY(manuf_personalize_device_secret1());
  }

  // Check if CreatorSwCfg partition is already locked by reading its digest.
  uint32_t digest0 =
      abs_mmio_read32(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
                      OTP_CTRL_CREATOR_SW_CFG_DIGEST_0_REG_OFFSET);
  uint32_t digest1 =
      abs_mmio_read32(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
                      OTP_CTRL_CREATOR_SW_CFG_DIGEST_1_REG_OFFSET);
  if (digest0 != 0 || digest1 != 0) {
    // Partition is already locked! Scrambling is finalized. Skip write.
    set_ate_indicator(kGpioPinTestDone, true);
    wait_for_interrupt();
    return OK_STATUS();
  }

  if (!status_ok(individualize_flash_data_default_cfg_check())) {
    TRY(individualize_flash_data_default_cfg_write());
    TRY(individualize_flash_data_default_cfg_check());

    // Scrambling was successfully written and verified! Drive TestDone (GPIO 1
    // / IOA1) HIGH!
    set_ate_indicator(kGpioPinTestDone, true);

    wait_for_interrupt();
  } else {
    // Scrambling is ALREADY set up! This is an unauthorized attempt to re-run
    // Stage 1! Error out immediately!
    set_ate_indicator(kGpioPinTestError, true);
    return INTERNAL();
  }
  return OK_STATUS();
}

void _ottf_main(void) {
  watchdog_disable();

  if (!status_ok(configure_ate_gpio_indicators())) {
    while (true) {
    }
  }
  set_ate_indicator(kGpioPinTestStart, true);

  uint32_t reason = rstmgr_reason_get();
  if (reason != 0) {
    rstmgr_reason_clear(reason);
  }

  status_t result = personalize_otp_and_flash_secrets();
  if (!status_ok(result)) {
    set_ate_indicator(kGpioPinTestError, true);
  } else {
    set_ate_indicator(kGpioPinTestDone, true);
  }

  while (true) {
    wait_for_interrupt();
  }
}

// Linker stubs to discard the heavy unhardened printing/formatting library.
#include <stdarg.h>
void base_log_internal_core(const void *log, ...) {
  // Empty stub
}

int base_vfprintf(void *stream, const char *format, va_list ap) {
  return 0;  // Empty stub
}
