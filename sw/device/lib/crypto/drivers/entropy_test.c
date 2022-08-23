// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy_kat.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  status_t result = entropy_csrng_kat();
  if (!status_ok(result)) {
    LOG_ERROR("entropy_csrng_kat: %r\n", result);
    return false;
  }
  return true;
}
