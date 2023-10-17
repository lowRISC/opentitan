// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_SIM_DV_PWRMGR_SLEEP_ALL_WAKE_UPS_IMPL_H_
#define OPENTITAN_SW_DEVICE_TESTS_SIM_DV_PWRMGR_SLEEP_ALL_WAKE_UPS_IMPL_H_

// Contains header for code that is common to deep, normal, and random sleep for
// pwrmgr all_wake_ups test.

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

/**
 * The retention sram counter used in this test.
 */
enum { kCounterCases };

typedef struct test_wakeup_sources {
  /**
   * Name of the device.
   */
  const char *name;
  /**
   * Handle to the DIF object for this device.
   */
  void *dif_handle;
  /**
   * Wakeup Sources.
   */
  dif_pwrmgr_request_sources_t wakeup_src;
  /**
   * Configuration and initialization actions for the device.
   * This will be passed the value of `dif` above.
   */
  void (*config)(void *dif);
} test_wakeup_sources_t;

extern dif_adc_ctrl_t adc_ctrl;
extern dif_aon_timer_t aon_timer;
extern dif_flash_ctrl_state_t flash_ctrl;
extern dif_pinmux_t pinmux;
extern dif_pwrmgr_t pwrmgr;
extern dif_rv_plic_t rv_plic;
extern dif_sensor_ctrl_t sensor_ctrl;
extern dif_sysrst_ctrl_t sysrst_ctrl;
extern dif_usbdev_t usbdev;

/**
 * Initialize the units used in this test.
 */
void init_units(void);

/**
 * Check pwrmgr reports this unit as the reason for the wakeup.
 */
void check_wakeup_reason(uint32_t wakeup_unit);

/**
 * Execute the test for a given unit and sleep mode.
 *
 * Configure wakeup_unit to cause a wakeup up and the pwrmgr sleep mode,
 * and let the CPU wait for interrupt.
 */
void execute_test(uint32_t wakeup_unit, bool deep_sleep);

/**
 * Clear the wakeup for the given unit.
 */
void clear_wakeup(uint32_t wakeup_unit);

#endif  // OPENTITAN_SW_DEVICE_TESTS_SIM_DV_PWRMGR_SLEEP_ALL_WAKE_UPS_IMPL_H_
