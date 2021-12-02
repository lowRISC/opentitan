// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_H_

#include <stdbool.h>

// This private header is included here so that OTTF users can include a single
// header in their test application (the `ottf.h` header).
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"

/**
 * @file
 * @brief Entrypoint definitions for on-device tests
 */

/**
 * Configuration variables for an on-device test.
 *
 * This type represents configuration values for an on-device test, which allow
 * tests to configure the behavior of the OpenTitan Test Framework (OTTF).
 *
 * WARNING: DO NOT REARRANGE THE MEMBERS IN THIS STRUCT. THE FIRST MEMBER IS
 * ACCESSED BY OTTF ISR ASSEMBLY WHICH EXPECTS A SPECIFIC CONFIGURATION.
 *
 * However, new fields can be safely added to this struct without affecting any
 * tests; the "default" value of all fields should be zero (or NULL, or
 * equivalent).
 *
 * See `kTestConfig`.
 */
typedef struct test_config {
  /**
   * If true, `test_main()` is run as a FreeRTOS task, enabling test writers to
   * to spawn additional (concurrent) FreeRTOS tasks within the `test_main()`
   * execution context.
   *
   * If false, `test_main()` is executed on bare-metal, and cannot spawn
   * additional concurrent execution contexts. This is useful for tests that do
   * not require concurrency, and seek to minimize simulation runtime.
   */
  bool enable_concurrency;
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
 * This value needs to be provided as a global so that the initialization code
 * that runs before `test_main()` is executed can take note of it.
 */
extern const test_config_t kTestConfig;

/**
 * Entry point for a SW on-device (or chip-level) test.
 *
 * This function should be defined externally in a standalone SW test, linked
 * together with this library. This library provides a `main()` function that
 * does test harness setup, initializes FreeRTOS, and starts a FreeRTOS task
 * that executes `test_main()`.
 *
 * @return success or failure of the test as boolean.
 */
extern bool test_main(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_H_
