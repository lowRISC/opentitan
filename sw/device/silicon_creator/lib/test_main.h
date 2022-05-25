// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_TEST_MAIN_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_TEST_MAIN_H_

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/error.h"

/**
 * Execute a test function and log the test result.  Update the result value
 * if there is a failure code.
 */
#define EXECUTE_TEST(result_, test_function_)                               \
  do {                                                                      \
    rom_error_t local_error;                                                \
    LOG_INFO("Starting test " #test_function_ "...");                       \
    local_error = test_function_();                                         \
    if (local_error == kErrorOk) {                                          \
      LOG_INFO("Finished test " #test_function_ ": ok.");                   \
    } else {                                                                \
      result_ = local_error;                                                \
      LOG_ERROR("Finished test " #test_function_ ": 0x%08x.", local_error); \
    }                                                                       \
  } while (0)

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_TEST_MAIN_H_
