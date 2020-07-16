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
 * Entry point for a SW on-device test.
 *
 * This function should be defined externally in a standalone SW test, linked
 * together with this library. This library provides a `main()` function that
 * does test harness setup and calls `test_main()`.
 *
 * @return success or failure of the test as boolean.
 */
extern bool test_main(void);

/**
 * This flag should be defined in the test runner with the default value,
 * which then can be overriden by individual tests when required. For example,
 * when a test configures UART to non-standard settings for internal use, the
 * flag has to be set to `true` in such test.
 */
extern bool uart_reconfigure_required;

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_MAIN_H_
