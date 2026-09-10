// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/bootstrap.h"

#include "hw/top/dt/gpio.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

#include "hw/top/gpio_regs.h"
#include "hw/top/otp_ctrl_regs.h"

static const dt_gpio_t kGpioDt = kDtGpio;

rom_error_t bootstrap_chip_erase(void) { return nvm_ctrl_chip_erase(); }

rom_error_t bootstrap_erase_verify(void) {
  return nvm_ctrl_chip_erase_verify();
}

hardened_bool_t bootstrap_requested(void) {
  uint32_t bootstrap_dis =
      otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET);
  if (launder32(bootstrap_dis) == kHardenedBoolTrue) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_NE(bootstrap_dis, kHardenedBoolTrue);

  // A single read is sufficient since we expect strong pull-ups on the strap
  // pins.  We assume pinmux has already been configured (by pinmux_init) to
  // enable the internal pull-downs on the strap pins.  As such, an external
  // weak pull-up will not be detected as a logic-high.
  uint32_t res = launder32(kHardenedBoolTrue) ^ SW_STRAP_BOOTSTRAP;
  res ^= abs_mmio_read32(dt_gpio_primary_reg_block(kGpioDt) +
                         GPIO_DATA_IN_REG_OFFSET) &
         SW_STRAP_MASK;
  if (launder32(res) != kHardenedBoolTrue) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_EQ(res, kHardenedBoolTrue);
  return res;
}

rom_error_t bootstrap(void) {
  hardened_bool_t requested = bootstrap_requested();
  if (launder32(requested) != kHardenedBoolTrue) {
    return kErrorBootstrapNotRequested;
  }
  HARDENED_CHECK_EQ(requested, kHardenedBoolTrue);

  return enter_bootstrap();
}
