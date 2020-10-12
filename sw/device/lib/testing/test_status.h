// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_STATUS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_STATUS_H_

/**
 * Indicates the status of the software running on the CPU, from a testing
 * perspective.
 *
 * It is useful to track the current status of the test SW executing on the CPU
 * as a signal the helps aid in debug.
 *
 * The values set to these literals is arbitrary and do not possess any special
 * meaning (other than being hex 'words'). They are chosen to be 16-bits wide.
 * The upper 16-bits are reserved for future use.
 */
typedef enum test_status {
  /**
   * Indicates that the CPU has started executing the boot_rom code.
   *
   * Writing this value to #kDeviceTestStatusAddress must not stop simulation of
   * the current device.
   */
  kTestStatusInBootRom = 0xb090,  // 'bogo', BOotrom GO

  /**
   * Indicates that the CPU has started executing the test code.
   *
   * Writing this value to #kDeviceTestStatusAddress must not stop simulation of
   * the current device.
   */
  kTestStatusInTest = 0x4354,  // 'test'

  /**
   * Indicates that the CPU is in the WFI state.
   *
   * Writing this value to #kDeviceTestStatusAddress must not stop simulation of
   * the current device.
   */
  kTestStatusInWfi = 0x1d1e,  // 'idle'

  /**
   * This indicates that the test has passed. This is a terminal state. Any code
   * appearing after this value is set is unreachable.
   *
   * Writing this value to #kDeviceTestStatusAddress may stop simulation of the
   * current device.
   */
  kTestStatusPassed = 0x900d,  // 'good'

  /**
   * This indicates that the test has failed. This is a terminal state. Any code
   * appearing after this value is set is unreachable.
   *
   * Writing this value to #kDeviceTestStatusAddress may stop simulation of the
   * current device.
   */
  kTestStatusFailed = 0xbaad  // 'baad'
} test_status_t;

/**
 * This signals the status of the software test with `test_status` value.
 *
 * It is mandatory for tests to indicate whether they passed or failed using
 * this function with #kTestStatusPassed and #kTestStatusFailed.
 *
 * In simulated testing (Verilator, DV), this function writes `test_status` to
 * a specific address, which may cause the simulation to end.
 *
 * In environments with a null #kDeviceTestStatusAddress, this logs a message
 * for terminal states and calls abort. Otherwise, the function returns safely.
 *
 * @param test_status current status of the test.
 */
void test_status_set(test_status_t test_status);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_STATUS_H_
