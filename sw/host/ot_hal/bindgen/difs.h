// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#ifndef OPENTITAN_SW_HOST_OT_HAL_BINDGEN_DIFS_H_
#define OPENTITAN_SW_HOST_OT_HAL_BINDGEN_DIFS_H_

#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"

#ifdef OT_IS_ENGLISH_BREAKFAST_REDUCED_SUPPORT_FOR_INTERNAL_USE_ONLY_

#include "hw/top/aon_timer_regs.h"  // Generated.
#include "hw/top/clkmgr_regs.h"     // Generated.
#include "hw/top/lc_ctrl_regs.h"    // Generated.
#include "hw/top/otp_ctrl_regs.h"   // Generated.
#include "hw/top/rstmgr_regs.h"     // Generated.
#include "hw/top/sram_ctrl_regs.h"  // Generated.
#include "hw/top/uart_regs.h"       // Generated.

#else

#include "hw/top/adc_ctrl_regs.h"       // Generated.
#include "hw/top/aes_regs.h"            // Generated.
#include "hw/top/alert_handler_regs.h"  // Generated.
#include "hw/top/aon_timer_regs.h"      // Generated.
#include "hw/top/clkmgr_regs.h"         // Generated.
#include "hw/top/csrng_regs.h"          // Generated.
#include "hw/top/edn_regs.h"            // Generated.
#include "hw/top/entropy_src_regs.h"    // Generated.
#include "hw/top/flash_ctrl_regs.h"     // Generated.
#include "hw/top/gpio_regs.h"           // Generated.
#include "hw/top/hmac_regs.h"           // Generated.
#include "hw/top/i2c_regs.h"            // Generated.
#include "hw/top/keymgr_regs.h"         // Generated.
#include "hw/top/kmac_regs.h"           // Generated.
#include "hw/top/lc_ctrl_regs.h"        // Generated.
#include "hw/top/otbn_regs.h"           // Generated.
#include "hw/top/otp_ctrl_regs.h"       // Generated.
#include "hw/top/pattgen_regs.h"        // Generated.
#include "hw/top/pinmux_regs.h"         // Generated.
#include "hw/top/pwm_regs.h"            // Generated.
#include "hw/top/pwrmgr_regs.h"         // Generated.
#include "hw/top/rstmgr_regs.h"         // Generated.
#include "hw/top/rv_timer_regs.h"       // Generated.
#include "hw/top/sensor_ctrl_regs.h"    // Generated.
#include "hw/top/spi_device_regs.h"     // Generated.
#include "hw/top/spi_host_regs.h"       // Generated.
#include "hw/top/sram_ctrl_regs.h"      // Generated.
#include "hw/top/sysrst_ctrl_regs.h"    // Generated.
#include "hw/top/uart_regs.h"           // Generated.
#include "hw/top/usbdev_regs.h"         // Generated.

#endif

#endif  // OPENTITAN_SW_HOST_OT_HAL_BINDGEN_DIFS_H_
