// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"

/* We need control flow for the ujson messages exchanged
 * with the host in OTTF_WAIT_FOR on real devices. */
OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

enum {
  kTestTimeoutMicros = 1000 * 1000, /* one second */
};

enum phase_t {
  /* Wait for host to move to next phase. */
  kWaitHost1 = 0,
  /* Wait for device to move to next phase. */
  kWaitDevice1 = 1,
  /* Wait for host to move to next phase. */
  kWaitHost2 = 2,
  /* Test finished. */
  kTestDone = 3,
};

/* Use a known size integer for the debugger. Mark this as
 * volatile so it can be changed by the host/DV env. */
volatile uint32_t kPhase = kWaitHost1;

bool test_main(void) {
  LOG_INFO("Waiting for host");
  /* Wait until host changes the phase. On DV, this will simply until
   * the environment change the value of the variable. On a real device,
   * this will wait for ujson messages from the host that read/write
   * memory. The condition is check after each message and the test will
   * be aborted the condition is still false after the timeout. */
  OTTF_WAIT_FOR(kPhase != kWaitHost1, kTestTimeoutMicros);
  /* Make sure that host moved to the expected phase. */
  CHECK(kPhase == kWaitDevice1, "kPhase should be kWaitDevice1 (%d) but is %d",
        kWaitDevice1, kPhase);
  LOG_INFO("Change phase to kWaitHost2");
  /* Change phase, the host will verify that the phase matches. */
  kPhase = kWaitHost2;
  /* Wait until host changes the phase again. */
  OTTF_WAIT_FOR(kPhase != kWaitHost2, kTestTimeoutMicros);
  CHECK(kPhase == kTestDone, "kPhase should be kTestDone (%d) but is %d",
        kTestDone, kPhase);
  return true;
}
