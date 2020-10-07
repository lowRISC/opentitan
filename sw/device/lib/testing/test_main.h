// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_MAIN_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_MAIN_H_

#include <stdbool.h>

/**
 * @file
 * @brief Entrypoint definitions for on-device tests
 */

/**
 * Configuration variables for an on-device test.
 *
 * This type represents configuration values for an on-device test, which allow
 * tests to configure the behavior of the `test_main.h` harness.
 *
 * New fields can be safely added to this struct without affecting any tests;
 * the "default" value of all fields should be zero (or NULL, or equivalent).
 *
 * See `kTestConfig`.
 */
typedef struct test_config {
  /**
   * Indicates that `test_main()` does something non-trivial to the UART
   * device. Setting this to true will make `test_main()` guard against this
   * by resetting the UART device before printing debug information.
   */
  bool can_clobber_uart;
} test_config_t;

/**
 * Global test configuration.
 *
 * This symbol should be defined externally in a standalone SW test. For most
 * tests, this will just look like the following:
 *
 *   const test_config_t kTestConfig;
 *
 * The zero values of all of the fields will behave like sane defaults.
 *
 * This value needs to be provided as a global so that the code that runs
 * before `test_main()` is called can take note of it.
 */
extern const test_config_t kTestConfig;

/**
 * Entry point for a SW on-device test.
 *
 * This function should be defined externally in a standalone SW test, linked
 * together with this library. This library provides a `main()` function that
 * does test harness setup and calls `test_main()`.
 *
 * @return success or failure of the test as boolean.
 */
extern bool test_main(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_MAIN_H_
