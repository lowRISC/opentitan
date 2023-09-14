// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB VBUS test
//
// Checks for the presence of VBUS from the host/DPI model, optionally checking
// that VBUS is low initially when the test starts.

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#define USBDEV_BASE_ADDR TOP_EARLGREY_USBDEV_BASE_ADDR

/**
 * Are we expecting VBUS to be low at the start of the test, ie. no connection
 * to the physical host or the DPI model is inactive?
 * Typically useful only for an FPGA target that is being manually supervised.
 */
static const bool kCheckLowFirst = false;

/**
 * USB device handle
 */
static dif_usbdev_t usbdev;

/**
 * Pinmux handle
 */
static dif_pinmux_t pinmux;

// Wait with timeout until the VBUS/SENSE signal is in the expected state.
static status_t vbus_wait(bool expected, uint32_t timeout_micros) {
  ibex_timeout_t timeout = ibex_timeout_init(timeout_micros);
  do {
    // Read the current state of VBUS.
    bool vbus;
    TRY(dif_usbdev_status_get_sense(&usbdev, &vbus));
    if (vbus == expected) {
      return OK_STATUS();
    }
  } while (!ibex_timeout_check(&timeout));

  return DEADLINE_EXCEEDED();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  uint32_t timeout_micros = 1000u;
  bool prompt = false;

  switch (kDeviceType) {
    // In simulation the DPI model connects VBUS shortly after reset.
    case kDeviceSimDV:
    case kDeviceSimVerilator:
      timeout_micros = 1000u;
      break;
    default:
      // FPGA platforms where user intervention may be required.
      timeout_micros = 30 * 1000 * 1000u;
      prompt = true;

      LOG_INFO("Running USBDEV_VBUS test");
      break;
  }

  // Ensure that the VBUS/SENSE signal is routed through to the usbdev
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
      kTopEarlgreyPinmuxInselIoc7));

  CHECK_DIF_OK(
      dif_usbdev_init(mmio_region_from_addr(USBDEV_BASE_ADDR), &usbdev));

  // Initially the VBUS may be expected to be low; if so, ensure that this is
  // the case.
  if (kCheckLowFirst) {
    if (prompt) {
      bool vbus;
      CHECK_DIF_OK(dif_usbdev_status_get_sense(&usbdev, &vbus));
      if (vbus) {
        LOG_INFO("Disconnect or power down the USB");
      }
    }

    CHECK_STATUS_OK(vbus_wait(false, timeout_micros));

    if (prompt) {
      LOG_INFO("Connect or power up the USB");
    }
  }

  // Check for VBUS present/risen.
  CHECK_STATUS_OK(vbus_wait(true, timeout_micros));

  return true;
}
