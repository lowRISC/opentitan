// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_TEST_CONFIG_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_TEST_CONFIG_H_

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
 * See `kOttfTestConfig`.
 */
typedef struct ottf_test_config {
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

  /**
   * Name of the file in which `kOttfTestConfig` is defined. Most of the time,
   * this will be the file that defines `test_main()`.
   */
  const char *file;
} ottf_test_config_t;

/**
 * Helper macro for defining the `kOttfTestConfig` symbol in test files.
 *
 * While the `kOttfTestConfig` struct can be defined directly, tests should
 * prefer this macro since it handles the definition of the `file` field.
 *
 * A test with default options should use:
 *
 *   OTTF_DEFINE_TEST_CONFIG();
 *
 * A test that wants to enable concurrency and can also clobber UART should use:
 *
 *   OTTF_DEFINE_TEST_CONFIG(.enable_concurrency = true,
 *                           .can_clobber_uart = true, );
 *
 */
#define OTTF_DEFINE_TEST_CONFIG(...) \
  const ottf_test_config_t kOttfTestConfig = {.file = __FILE__, __VA_ARGS__}

/**
 * Global test configuration.
 *
 * This symbol should be defined externally in a standalone SW test. For most
 * tests, this will just look like the following:
 *
 *   OTTF_DEFINE_TEST_CONFIG();
 *
 * The zero values of all of the fields will behave like sane defaults.
 *
 * This value needs to be provided as a global so that the initialization code
 * that runs before `test_main()` is executed can take note of it.
 */
extern const ottf_test_config_t kOttfTestConfig;

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_TEST_CONFIG_H_
