// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/usbdev_suspend.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Execute the entire test sequence; all test phases.
  // Note: This is impractical in simulation, and should be used only on FPGA
  // with a physical host.
  return usbdev_suspend_test(kSuspendPhaseSuspend, kSuspendPhaseShutdown, 1u,
                             false);
}
