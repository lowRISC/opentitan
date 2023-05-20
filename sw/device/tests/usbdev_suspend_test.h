// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_USBDEV_SUSPEND_TEST_H_
#define OPENTITAN_SW_DEVICE_TESTS_USBDEV_SUSPEND_TEST_H_
#include <stdbool.h>

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
 * @param with_traffic Perform streaming throughout test.
 * @param return       Successful completion of test.
 */
bool usbdev_suspend_test(usbdev_suspend_phase_t init_phase,
                         usbdev_suspend_phase_t fin_phase, bool with_traffic);

#endif  // OPENTITAN_SW_DEVICE_TESTS_USBDEV_SUSPEND_TEST_H_
