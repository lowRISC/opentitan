// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_STATUS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_STATUS_H_

#include <stdnoreturn.h>

/**
 * Indicates the status of the software running on the CPU, from a testing
 * perspective.
 *
 * It is useful to track the current status of the test SW executing on the CPU
 * as a signal the helps aid in debug.
 *
 * The values set to these literals is arbitrary and do not possess any special
 * meaning (other than being hex 'words'). They are chosen to be 16-bit only.
 * The upper 16-bits are reserved for future use.
 *
 * At minimum, it is mandatory to set the status of the software to explicitly
 * indicate whether the software test passed or failed, with
 * `kTestStatusPassed` and `kTestStatusFailed` values. As such these are
 * terimnal states - SW **must not** execute any code after reaching that
 * status.
 */
typedef enum test_status {
  /* Indicates that the CPU has started executing the boot_rom code. */
  kTestStatusBootRom = 0xb090,  // 'bogo', BOotrom GO

  /* Indicates that the CPU has started executing the test code. */
  kTestStatusUnderTest = 0x4354,  // 'test'

  /* Indicates that the CPU is in the WFI state. */
  kTestStatusWfi = 0x1d1e,  // 'idle'

  /* This indicates that the test has passed. */
  kTestStatusPassed = 0x900d,  // 'good'

  /* This indicates that the test has failed. */
  kTestStatusFailed = 0xbaad  // 'baad'
} test_status_t;

/**
 * Sets the test status.
 *
 * In DV testing, this function writes the current status of the software to a
 * specific memory location. In non-DV testing, this converts to a log.
 */
void set_test_status(const test_status_t test_status);

/**
 * Helper functions that assert the end-of-test.
 *
 * These assert that the test has passed/failed and stop execution by calling
 * the `abort()` function. It is mandatory to use the functions below to
 * indicate the terminal status' `kTestStatusPassed` and `kTestStatusFailed`.
 * The `set_test_status()` must not be invoked directly for these.
 */
noreturn void test_passed(void);
noreturn void test_failed(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_STATUS_H_
