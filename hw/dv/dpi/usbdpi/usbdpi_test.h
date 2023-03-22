// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_TEST_H_
#define OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_TEST_H_
#include "usb_transfer.h"

// Test number sent via usb_testutils to the DPI model to indicate the test
// stimulus to be presented.
typedef enum usb_testutils_test_number {
  kUsbTestNumberSmoke = 0,
  kUsbTestNumberStreams,
  kUsbTestNumberIso,
  kUsbTestNumberMixed,
  kUsbTestNumberSuspend,
  kUsbTestNumberExc,
} usb_testutils_test_number_t;

// Suspend Test phases (see usbdev_suspend_test.c)
typedef enum {
  kSuspendPhaseSuspend = 0u,
  kSuspendPhaseSleepActivity,
  kSuspendPhaseSleepReset,
  kSuspendPhaseSleepDisconnect,
  kSuspendPhaseDeepActivity,
  kSuspendPhaseDeepReset,
  kSuspendPhaseDeepDisconnect,
} usbdev_suspend_phase_t;

// Test steps
typedef enum {
  STEP_BUS_RESET = 0u,

  STEP_SET_DEVICE_ADDRESS,
  STEP_GET_DEVICE_DESCRIPTOR,
  STEP_GET_CONFIG_DESCRIPTOR,
  STEP_GET_FULL_CONFIG_DESCRIPTOR,
  STEP_SET_DEVICE_CONFIG,

  // Read test configuration
  // This is a bespoke 'vendor' command via which we inquire of the CPU
  // software what behaviour is required
  STEP_GET_TEST_CONFIG,
  // Report test status (pass/failure) to the CPU software
  STEP_SET_TEST_STATUS,

  // usbdev_test
  STEP_FIRST_READ,
  STEP_READ_BAUD,
  STEP_SECOND_READ,
  STEP_SET_BAUD,
  STEP_THIRD_READ,
  STEP_TEST_ISO1,
  STEP_TEST_ISO2,
  STEP_ENDPT_UNIMPL_SETUP,
  STEP_ENDPT_UNIMPL_OUT,
  STEP_ENDPT_UNIMPL_IN,
  STEP_DEVICE_UK_SETUP,
  STEP_UK_SETUP_REQ,

  // Suspend/Resume test
  STEP_SUSPEND,
  STEP_ACTIVE,
  STEP_SUSPEND_LONG,
  STEP_RESUME,

  // usbdev_stream_test
  STEP_STREAM_SERVICE = 0x77u,

  // Idle state, keep sending SOF but do nothing else
  STEP_IDLE = 0x7eu,

  // Disconnect the device and stop
  STEP_BUS_DISCONNECT = 0x7fu
} usbdpi_test_step_t;

// Test-specific initialization
void usbdpi_test_init(usbdpi_ctx_t *ctx);

// Return the next step in the test sequence
usbdpi_test_step_t usbdpi_test_seq_next(usbdpi_ctx_t *ctx,
                                        usbdpi_test_step_t step);

#endif  // OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_TEST_H_
