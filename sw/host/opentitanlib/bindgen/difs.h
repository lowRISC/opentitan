// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#ifndef OPENTITAN_SW_HOST_OPENTITANLIB_BINDGEN_DIFS_H_
#define OPENTITAN_SW_HOST_OPENTITANLIB_BINDGEN_DIFS_H_

#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"

#ifdef OT_IS_ENGLISH_BREAKFAST_REDUCED_SUPPORT_FOR_INTERNAL_USE_ONLY_

#include "aon_timer_regs.h"  // Generated.
#include "clkmgr_regs.h"     // Generated.
#include "lc_ctrl_regs.h"    // Generated.
#include "otp_ctrl_regs.h"   // Generated.
#include "rstmgr_regs.h"     // Generated.
#include "uart_regs.h"       // Generated.

#else

#include "adc_ctrl_regs.h"       // Generated.
#include "aes_regs.h"            // Generated.
#include "alert_handler_regs.h"  // Generated.
#include "aon_timer_regs.h"      // Generated.
#include "clkmgr_regs.h"         // Generated.
#include "csrng_regs.h"          // Generated.
#include "edn_regs.h"            // Generated.
#include "entropy_src_regs.h"    // Generated.
#include "flash_ctrl_regs.h"     // Generated.
#include "gpio_regs.h"           // Generated.
#include "hmac_regs.h"           // Generated.
#include "i2c_regs.h"            // Generated.
#include "keymgr_regs.h"         // Generated.
#include "kmac_regs.h"           // Generated.
#include "lc_ctrl_regs.h"        // Generated.
#include "otbn_regs.h"           // Generated.
#include "otp_ctrl_regs.h"       // Generated.
#include "pattgen_regs.h"        // Generated.
#include "pinmux_regs.h"         // Generated.
#include "pwm_regs.h"            // Generated.
#include "pwrmgr_regs.h"         // Generated.
#include "rstmgr_regs.h"         // Generated.
#include "rv_timer_regs.h"       // Generated.
#include "sensor_ctrl_regs.h"    // Generated.
#include "spi_device_regs.h"     // Generated.
#include "spi_host_regs.h"       // Generated.
#include "sram_ctrl_regs.h"      // Generated.
#include "sysrst_ctrl_regs.h"    // Generated.
#include "uart_regs.h"           // Generated.
#include "usbdev_regs.h"         // Generated.

#endif

#endif  // OPENTITAN_SW_HOST_OPENTITANLIB_BINDGEN_DIFS_H_
