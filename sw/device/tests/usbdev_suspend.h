// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_USBDEV_SUSPEND_H_
#define OPENTITAN_SW_DEVICE_TESTS_USBDEV_SUSPEND_H_
#include <stdbool.h>
#include <stdint.h>

// USB suspend/resume test
//
// The testing of suspend, sleep, wakeup and resume logic can consume a _lot_
// of simulation time because the timings of the USB protocol are very
// conservative, eg. Resume Signaling should occur for at least 20ms and Reset
// Signaling should be at least 10ms. These durations are impractical for
// chip simulation, so the DPI model intentionally shortens these delays.
//
// Additionally, to exercise both Normal and Deep Sleep modes and the three
// different reasons for waking from each sleep, the total number of test
// phases/states is prohibitive for a single simulation. Individual top-level
// tests therefore specify a range of test phases, and it is expected that the
// full sequence shall only ever be exercised on FPGA with a physical host.

// Iteration count that denotes looping indefinitely
#define USBDEV_SUSPEND_ETERNAL 0U

/**
 * Test phases; named according to the event that we are expecting to occur.
 */
typedef enum {
  /**
   * First test phase just tests regular Suspend/Resume signaling; after we've
   * resumed, we expect a Bus Reset from the DPI/Host.
   */
  kSuspendPhaseSuspend = 0u,
  /**
   * This test phase instructs the DPI model to put the DUT into Suspend long
   * enough that this software will attempt to put the device into its Normal
   * Sleep state and exercise the AON/Wakeup module, stopping the clocks but not
   * powering down.
   */
  kSuspendPhaseSleepResume,
  /*
   * The AON/Wakeup module will cause us to awaken in response to a bus reset.
   */
  kSuspendPhaseSleepReset,
  /**
   * As above, but this time we're expecting a VBUS/SENSE loss.
   */
  kSuspendPhaseSleepDisconnect,
  /**
   * Mirrors Resume detection for normal sleep, but this time we enter Deep
   * Sleep and the power is removed too.
   */
  kSuspendPhaseDeepResume,
  /**
   * Mirrors Bus Reset detection for normal sleep, but this time we enter Deep
   * Sleep and the power is removed too.
   */
  kSuspendPhaseDeepReset,
  /**
   * As above, but this time we're expecting a VBUS/SENSE loss.
   */
  kSuspendPhaseDeepDisconnect,
  /**
   * Final phase; shut down.
   */
  kSuspendPhaseShutdown,
} usbdev_suspend_phase_t;

/**
 * USB Suspend/Sleep/Wakeup/Resume test body.
 *
 * @param init_phase   Initial phase of test (inclusive).
 * @param fin_phase    Final phase of test (inclusive).
 * @param num_iters    Number of iterations of the phase sequence. (0 = eternal)
 * @param with_traffic Perform streaming throughout test.
 * @param return       Successful completion of test.
 */
bool usbdev_suspend_test(usbdev_suspend_phase_t init_phase,
                         usbdev_suspend_phase_t fin_phase, uint32_t num_iters,
                         bool with_traffic);

#endif  // OPENTITAN_SW_DEVICE_TESTS_USBDEV_SUSPEND_H_
