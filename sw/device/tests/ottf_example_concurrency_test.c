// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf.h"

const test_config_t kTestConfig = {
    .can_clobber_uart = false,
    .enable_concurrency = true,
};

bool test_main(void) {
  LOG_INFO("Running on-device test as FreeRTOS task using the OTTF.");
  return true;
}
