// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_MAIN_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_MAIN_H_

#include <stdbool.h>

// This private header is included here so that OTTF users can include a single
// header in their test application (the `ottf_main.h` header).
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

/**
 * @file
 * @brief Entrypoint definitions for on-device tests
 */

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

/**
 * TODO: add description
 */
extern bool manufacturer_pre_test_hook(void);

/**
 * TODO: add description
 */
extern bool manufacturer_post_test_hook(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_MAIN_H_
