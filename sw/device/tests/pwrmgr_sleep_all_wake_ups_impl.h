// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PWRMGR_SLEEP_ALL_WAKE_UPS_IMPL_H_
#define OPENTITAN_SW_DEVICE_TESTS_PWRMGR_SLEEP_ALL_WAKE_UPS_IMPL_H_

// Contains header for code that is common to deep, normal, and random sleep for
// pwrmgr all_wake_ups test.

#include "sw/device/lib/dif/dif_pwrmgr.h"
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
  /*
   * Type of the module.
   */
  dt_device_type_t dev_type;
  /*
   * Index of the wakeup signal.
   */
  size_t wakeup;
  /**
   * Check whether this wake up should be skipped in this configuration.
   * If set to NULL, assume that it should not be skipped.
   */
  bool (*skip)(dt_pwrmgr_wakeup_src_t src);
  /**
   * Configuration and initialization actions for the device.
   */
  void (*config)(dt_pwrmgr_wakeup_src_t src);
  /**
   * Check the wakeup reason.
   */
  void (*check)(dt_pwrmgr_wakeup_src_t src);
  /**
   * Clear the wakeup reason.
   */
  void (*clear)(dt_pwrmgr_wakeup_src_t src);
} test_wakeup_sources_t;

extern dif_pwrmgr_t pwrmgr;

/**
 * Initialize the units used in this test.
 */
void init_units(void);

/**
 * Return the number of units to test.
 */
size_t get_wakeup_count(void);

/**
 * Obtain information about a wakeup source.
 */
const test_wakeup_sources_t *get_wakeup_source(size_t wakeup_unit,
                                               dt_pwrmgr_wakeup_src_t *src);

/**
 * Check pwrmgr reports this unit as the reason for the wakeup.
 */
void check_wakeup_reason(size_t wakeup_unit);

/**
 * Execute the test for a given unit and sleep mode.
 *
 * Configure wakeup_unit to cause a wakeup up and the pwrmgr sleep mode,
 * and let the CPU wait for interrupt. Returns false if this wakeup unit
 * must be skipped.
 */
OT_WARN_UNUSED_RESULT
bool execute_test(size_t wakeup_unit, bool deep_sleep);

/**
 * Clear the wakeup for the given unit.
 */
void clear_wakeup(size_t wakeup_unit);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PWRMGR_SLEEP_ALL_WAKE_UPS_IMPL_H_
